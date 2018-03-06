#include <config.h>
#include <errno.h>
#include <getopt.h>
#include <unistd.h>

#include "openflow/openflow.h"

#include "openvswitch/hmap.h"
#include "openvswitch/list.h"
#include "openvswitch/ofp-msgs.h"
#include "openvswitch/ofp-util.h"
#include "openvswitch/ofpbuf.h"
#include "openvswitch/poll-loop.h"
#include "openvswitch/rconn.h"
#include "openvswitch/vconn.h"
#include "openvswitch/vlog.h"

#include "lib/command-line.h"
#include "lib/daemon.h"
#include "lib/dirs.h"
#include "lib/fatal-signal.h"
#include "lib/hash.h"
#include "lib/ofp-version-opt.h"
#include "lib/socket-util.h"
#include "lib/stream-ssl.h"
#include "lib/timeval.h"
#include "lib/unixctl.h"
#include "lib/util.h"

VLOG_DEFINE_THIS_MODULE(ofproxy);

/* XID management
 *
 * Maintain an hmap and an ordered list of outstanding XID entries for each
 * switch, and a list for controllers.
 *
 * On message received from controller:
 *  - Allocate a new XID and entry for the message.
 *  - Insert the XID entry to hmap and lists.
 *  - Set new XID and send to switch.
 *
 * On message received from switch:
 *  - Lookup XID entry in hmap.
 *  - If type is BARRIER_REPLY, remove entries prior to the corresponding
 *    BARRIER_REQUEST.
 *  - If the entry has controller information, set original XID and send to
 *    controller.
 *
 * Periodically send BARRIER_REQUEST if there're XID entries.
 */
struct xid_entry {
    struct hmap_node map_node;      /* Links to xid_map of switch. */
    uint32_t xid;

    struct switch_context *sw;
    struct ovs_list sw_node;        /* Links to xid_list of switch. */

    struct ctlr_context *ctlr;      /* Originating controller, if any */
    uint32_t orig_xid;
    struct ovs_list ctlr_node;      /* Links to xid_list of controller. */
};

enum switch_state {
    S_CONNECTING,
    S_ESTABLISHED,
    S_ERROR
};

struct ctlr_context {
    struct ovs_list list_node;      /* List to ctlrs of switch. */
    struct switch_context *sw;
    struct rconn *rconn;
    struct ovs_list xid_list;       /* Outstanding XIDs. */
};

struct switch_context {
    struct ovs_list list_node;
    struct rconn *rconn;
    const char *name;
    enum switch_state state;
    uint32_t protocol_version;

    struct pvconn *pvconn;
    struct ovs_list ctlrs;          /* List of active controllers. */

    uint32_t next_xid;
    struct ovs_list xid_list;       /* Outstanding XID entries, ordered. */
    struct hmap xid_map;            /* XID entries indexed by XID */

    long long barrier_timer;

    struct pvconn *snoop;
};

static struct switch_context *switch_create(struct vconn *vconn);
static void switch_destroy(struct switch_context *sw);
static void switch_run(struct switch_context *sw);
static void switch_wait(struct switch_context *sw);
static int switch_ctlr_pvconn_open(struct switch_context *sw);
static int switch_snoop_pvconn_open(struct switch_context *sw);
static void switch_send_barrier(struct switch_context *sw);
static void process_sw_message(struct switch_context *sw, struct ofpbuf *msg);
static void switch_xid_clear__(struct switch_context *sw);

static struct ctlr_context *ctlr_create(struct vconn *vconn,
                                        struct switch_context *sw);
static void ctlr_destroy(struct ctlr_context *ctlr);
static void ctlr_destroy__(struct ctlr_context *ctlr);
static void ctlr_xid_clear(struct ctlr_context *ctlr);
static void ctlr_run(struct ctlr_context *ctlr);
static void ctlr_wait(struct ctlr_context *ctlr);
static void process_ctlr_message(struct ctlr_context *ctlr,
                                 struct ofpbuf *msg);

static void xid_insert(struct xid_entry *entry);
static void xid_remove(struct xid_entry *entry);
static struct xid_entry *xid_find(struct hmap *xid_map,
                                  uint32_t xid);
static void xid_barrier(struct xid_entry *entry);

static void ofproxy_exit(struct unixctl_conn *conn, int argc,
                         const char *argv[], void *exiting);

/* Options. */
static char *unixctl_path = NULL;
static char *pvconn_name = "ptcp:";
static uint32_t version_mask = 0;
static long long barrier_interval = 5;
static bool snoop = false;

static void
xid_insert(struct xid_entry *entry)
{
    ovs_list_push_back(&entry->sw->xid_list, &entry->sw_node);
    hmap_insert(&entry->sw->xid_map, &entry->map_node,
                hash_int(entry->xid, 0));
    if (entry->ctlr) {
        ovs_list_push_back(&entry->ctlr->xid_list, &entry->ctlr_node);
    }
}

static void
xid_remove(struct xid_entry *entry)
{
    ovs_list_remove(&entry->sw_node);
    hmap_remove(&entry->sw->xid_map, &entry->map_node);
    if (entry->ctlr) {
        ovs_list_remove(&entry->ctlr_node);
    }
}

static struct xid_entry *
xid_find(struct hmap *xid_map, uint32_t xid)
{
    struct xid_entry *entry;
    HMAP_FOR_EACH_WITH_HASH (entry, map_node,
                             hash_int(xid, 0), xid_map) {
        if (entry->xid == xid) {
            return entry;
        }
    }
    return NULL;
}

/* Flushes all prior XIDs. Called when BARRIER_REPLY is received. */
static void
xid_barrier(struct xid_entry *entry)
{
    struct xid_entry *curr, *next;
    LIST_FOR_EACH_SAFE (curr, next, sw_node, &entry->sw->xid_list) {
        if (curr == entry) {
            break;
        } else {
            xid_remove(curr);
            free(curr);
        }
    }
}

static struct switch_context *
switch_create(struct vconn *vconn)
{
    struct switch_context *sw = xzalloc(sizeof(struct switch_context));

    sw->rconn = rconn_create(0, 0, DSCP_DEFAULT, version_mask);
    rconn_connect_unreliably(sw->rconn, vconn, NULL);
    sw->name = rconn_get_name(sw->rconn);

    ovs_list_init(&sw->ctlrs);
    ovs_list_init(&sw->xid_list);
    hmap_init(&sw->xid_map);

    if (barrier_interval > 0) {
        sw->barrier_timer = time_msec() + barrier_interval;
    }

    return sw;
}

/* Clears all XIDs. Called only when switch is being destroyed. */
static void
switch_xid_clear__(struct switch_context *sw)
{
    struct xid_entry *entry;
    HMAP_FOR_EACH_POP (entry, map_node, &sw->xid_map) {
        free(entry);
    }
    hmap_destroy(&sw->xid_map);
}

static void
switch_destroy(struct switch_context *sw)
{
    if (sw->pvconn) {
        pvconn_close(sw->pvconn);
    }
    rconn_destroy(sw->rconn);

    struct ctlr_context *ctlr;
    LIST_FOR_EACH_POP (ctlr, list_node, &sw->ctlrs) {
        ctlr_destroy__(ctlr);
    }

    switch_xid_clear__(sw);

    free(sw);
}

static void
switch_run(struct switch_context *sw)
{
    rconn_run(sw->rconn);

    /* TODO: Postpone pvconn_open after FEATURES_REPLY. */
    if (sw->state == S_CONNECTING) {
        int version;
        if ((version = rconn_get_version(sw->rconn)) != -1) {
            sw->protocol_version = version;
            VLOG_INFO("switch %s negotiated version: %s",
                      sw->name, ofputil_version_to_string(version));
            if (switch_ctlr_pvconn_open(sw) == 0) {
                sw->state = S_ESTABLISHED;
            } else {
                sw->state = S_ERROR;
            }
            if (snoop) {
                switch_snoop_pvconn_open(sw);
            }
        }
    }

    while (sw->pvconn) {
        struct vconn *new_vconn;
        int error = pvconn_accept(sw->pvconn, &new_vconn);
        if (!error) {
            ctlr_create(new_vconn, sw);
        } else if (error == EAGAIN) {
            break;
        } else {
            VLOG_WARN("pvconn error, switch: %s", sw->name);
            pvconn_close(sw->pvconn);
            sw->pvconn = NULL;
        }
    }

    while (sw->snoop) {
        struct vconn *new_vconn;
        int error = pvconn_accept(sw->snoop, &new_vconn);
        if (!error) {
            rconn_add_monitor(sw->rconn, new_vconn);
        } else if (error == EAGAIN) {
            break;
        } else {
            VLOG_WARN("pvconn error, switch: %s", sw->name);
            pvconn_close(sw->pvconn);
            sw->pvconn = NULL;
        }
    }

    struct ctlr_context *ctlr, *next;
    LIST_FOR_EACH_SAFE (ctlr, next, list_node, &sw->ctlrs) {
        ctlr_run(ctlr);
        if (!rconn_is_alive(ctlr->rconn)) {
            ctlr_destroy(ctlr);
        }
    }

    for (int i = 0; i < 50; i++) {
        struct ofpbuf *msg;
        msg = rconn_recv(sw->rconn);
        if (!msg) {
            break;
        }
        process_sw_message(sw, msg);
        ofpbuf_delete(msg);
    }

    if (barrier_interval > 0 &&
        time_msec() >= sw->barrier_timer) {
        if (!ovs_list_is_empty(&sw->xid_list)) {
            switch_send_barrier(sw);
        }
        sw->barrier_timer = time_msec() + barrier_interval;
    }
}

static void
switch_wait(struct switch_context *sw)
{
    rconn_run_wait(sw->rconn);
    rconn_recv_wait(sw->rconn);
    if (sw->pvconn) {
        pvconn_wait(sw->pvconn);
    }

    struct ctlr_context *ctlr;
    LIST_FOR_EACH (ctlr, list_node, &sw->ctlrs) {
        ctlr_wait(ctlr);
    }

    if (barrier_interval > 0) {
        poll_timer_wait_until(sw->barrier_timer);
    }
}

static char *
switch_ctlr_pvconn_name(struct switch_context *sw)
{
    /* TODO: support user-provided template, like using datapath_id, etc. */
    return xasprintf("punix:%s/%s.proxy", ovs_rundir(), sw->name);
}

static int
switch_ctlr_pvconn_open(struct switch_context *sw)
{
    char *name = switch_ctlr_pvconn_name(sw);
    int error = pvconn_open(name, 1 << sw->protocol_version,
                            DSCP_DEFAULT, &sw->pvconn);
    if (error) {
        VLOG_WARN("failed to listen for controller on: %s", name);
    } else {
        VLOG_INFO("listening for controller on: %s", name);
    }
    free(name);
    return error;
}

static char *
switch_snoop_pvconn_name(struct switch_context *sw)
{
    return xasprintf("punix:%s/%s.snoop", ovs_rundir(), sw->name);
}

static int
switch_snoop_pvconn_open(struct switch_context *sw)
{
    char *name = switch_snoop_pvconn_name(sw);
    int error = pvconn_open(name, 0,
                            DSCP_DEFAULT, &sw->snoop);
    if (error) {
        VLOG_WARN("failed to listen for snooping on: %s", name);
    } else {
        VLOG_INFO("listening for snooping on: %s", name);
    }
    free(name);
    return error;
}

static struct ctlr_context *
ctlr_create(struct vconn *vconn, struct switch_context *sw)
{
    struct ctlr_context *ctlr = xzalloc(sizeof(struct ctlr_context));

    ctlr->sw = sw;
    ctlr->rconn = rconn_create(0, 0, DSCP_DEFAULT, 0);
    rconn_connect_unreliably(ctlr->rconn, vconn, NULL);
    ovs_list_init(&ctlr->xid_list);

    ovs_list_push_back(&sw->ctlrs, &ctlr->list_node);

    return ctlr;
}

static void
ctlr_xid_clear(struct ctlr_context *ctlr)
{
    struct xid_entry *entry, *next;
    LIST_FOR_EACH_SAFE (entry, next, ctlr_node, &ctlr->xid_list) {
        xid_remove(entry);
        free(entry);
    }
}

static void
ctlr_destroy(struct ctlr_context *ctlr)
{
    ovs_list_remove(&ctlr->list_node);
    ctlr_xid_clear(ctlr);
    ctlr_destroy__(ctlr);
}

static void
ctlr_destroy__(struct ctlr_context *ctlr)
{
    rconn_destroy(ctlr->rconn);
    free(ctlr);
}

static void
ctlr_run(struct ctlr_context *ctlr)
{
    rconn_run(ctlr->rconn);

    for (int i = 0; i < 50; i++) {
        struct ofpbuf *msg;
        msg = rconn_recv(ctlr->rconn);
        if (!msg) {
            break;
        }
        process_ctlr_message(ctlr, msg);
        ofpbuf_delete(msg);
    }
}

static void
ctlr_wait(struct ctlr_context *ctlr)
{
    rconn_run_wait(ctlr->rconn);
    rconn_recv_wait(ctlr->rconn);
}

/* Clone ofp message and alter xid */
static struct ofpbuf *
ofp_msg_dup_xid(struct ofpbuf *msg, uint32_t xid)
{
    struct ofpbuf *new_msg = ofpbuf_clone(msg);
    ((struct ofp_header *)new_msg->data)->xid = htonl(xid);
    return new_msg;
}

static void
process_ctlr_message(struct ctlr_context *ctlr, struct ofpbuf *msg)
{
    enum ofptype type;
    const struct ofp_header *header = msg->data;
    if (ofptype_decode(&type, header) == 0) {
        /* TODO: handle controller state change (role, set_async, etc.) */
        if (type == OFPTYPE_ECHO_REQUEST) {
            rconn_send(ctlr->rconn, ofputil_encode_echo_reply(header), NULL);
        } else {
            struct xid_entry *entry =
                xzalloc(sizeof(struct xid_entry));
            entry->xid = ctlr->sw->next_xid++;
            entry->orig_xid = ntohl(header->xid);
            entry->sw = ctlr->sw;
            entry->ctlr = ctlr;
            xid_insert(entry);
            rconn_send(ctlr->sw->rconn,
                       ofp_msg_dup_xid(msg, entry->xid),
                       NULL);
        }
    }
}

static void
process_sw_message(struct switch_context *sw, struct ofpbuf *msg)
{
    enum ofptype type;
    const struct ofp_header *header = msg->data;
    if (ofptype_decode(&type, header) == 0) {
        /* TODO: handle aync messages. */
        if (type == OFPTYPE_ECHO_REQUEST) {
            rconn_send(sw->rconn, ofputil_encode_echo_reply(header), NULL);
        } else {
            uint32_t xid = ntohl(header->xid);
            struct xid_entry *entry = xid_find(&sw->xid_map, xid);
            if (entry) {
                if (type == OFPTYPE_BARRIER_REPLY) {
                    xid_barrier(entry);
                }
                if (entry->ctlr) {
                    rconn_send(entry->ctlr->rconn,
                               ofp_msg_dup_xid(msg, entry->orig_xid),
                               NULL);
                } else {
                    xid_remove(entry);
                }
            }
        }
    }
}

static void
switch_send_barrier(struct switch_context *sw)
{
    struct xid_entry *entry = xzalloc(sizeof(struct xid_entry));
    entry->xid = sw->next_xid++;
    entry->sw = sw;
    xid_insert(entry);
    struct ofpbuf *msg = ofputil_encode_barrier_request(sw->protocol_version);
    ((struct ofp_header *)msg->data)->xid = htonl(entry->xid);
    rconn_send(sw->rconn, msg, NULL);
}

static void
ofproxy_exit(struct unixctl_conn *conn, int argc OVS_UNUSED,
             const char *argv[] OVS_UNUSED, void *exiting)
{
    *(bool *)exiting = true;
    unixctl_command_reply(conn, NULL);
}

static void
parse_options(int argc, char *argv[])
{
    enum {
        OPT_UNIXCTL = UCHAR_MAX + 1,
        OPT_BARRIER_INTERVAL,
        OPT_SNOOP,
        DAEMON_OPTION_ENUMS,
        OFP_VERSION_OPTION_ENUMS,
        VLOG_OPTION_ENUMS,
        SSL_OPTION_ENUMS,
    };

    static const struct option long_options[] = {
        {"unixctl", required_argument, NULL,  OPT_UNIXCTL},
        {"barrier-interval", required_argument, NULL, OPT_BARRIER_INTERVAL},
        {"enable-snoop", no_argument, NULL, OPT_SNOOP},
        DAEMON_LONG_OPTIONS,
        OFP_VERSION_LONG_OPTIONS,
        VLOG_LONG_OPTIONS,
        STREAM_SSL_LONG_OPTIONS,
        {NULL, 0, NULL, 0},
    };
    char *short_options = ovs_cmdl_long_options_to_short_options(long_options);

    for (;;) {
        int c;

        c = getopt_long(argc, argv, short_options, long_options, NULL);
        if (c == -1) {
            break;
        }

        switch (c) {
            case OPT_UNIXCTL:
                unixctl_path = optarg;
                break;

            case OPT_BARRIER_INTERVAL:
                barrier_interval = (long long)atoi(optarg) * 1000;
                break;

            case OPT_SNOOP:
                snoop = true;
                break;

                DAEMON_OPTION_HANDLERS
                OFP_VERSION_OPTION_HANDLERS
                VLOG_OPTION_HANDLERS
                STREAM_SSL_OPTION_HANDLERS

            case '?':
                exit(EXIT_FAILURE);

            case 0:
                break;

            default:
                ovs_abort(0, "unknow option");
        }
    }

    free(short_options);

    version_mask = get_allowed_ofp_versions();

    if (argc > optind) {
        pvconn_name = argv[optind];
    }
}



int
main(int argc, char *argv[])
{
    int error;
    bool exiting = false;

    struct unixctl_server *server = NULL;
    struct ovs_list switches = OVS_LIST_INITIALIZER(&switches);

    set_program_name(argv[0]);
    ovs_cmdl_proctitle_init(argc, argv);
    service_start(&argc, &argv);
    parse_options(argc, argv);
    fatal_ignore_sigpipe();

    daemon_become_new_user(false);

    struct pvconn *pvconn;
    error = pvconn_open(pvconn_name, version_mask, DSCP_DEFAULT, &pvconn);
    if (error) {
        ovs_fatal(0, "failed to listen");
    }

    daemonize_start(false);
    if (unixctl_path) {
        error = unixctl_server_create(unixctl_path, &server);
        if (error) {
            ovs_fatal(error, "failed to create unixctl server");
        }
        unixctl_command_register("exit", "", 0, 0, ofproxy_exit, &exiting);
    }
    daemonize_complete();

    while (pvconn || !ovs_list_is_empty(&switches)) {
        while (pvconn) {
            struct vconn *new_vconn;
            error = pvconn_accept(pvconn, &new_vconn);
            if (!error) {
                struct switch_context *sw = switch_create(new_vconn);
                ovs_list_insert(&switches, &sw->list_node);
                VLOG_INFO("switch %s connected", sw->name);
            } else if (error == EAGAIN) {
                break;
            } else {
                VLOG_WARN("pvconn error");
                pvconn_close(pvconn);
                pvconn = NULL;
            }
        }

        struct switch_context *sw, *next;
        LIST_FOR_EACH_SAFE (sw, next, list_node, &switches) {
            switch_run(sw);
            if (!rconn_is_alive(sw->rconn)) {
                VLOG_INFO("switch %s disconnected", sw->name);
                ovs_list_remove(&sw->list_node);
                switch_destroy(sw);
            }
        }

        if (server) {
            unixctl_server_run(server);
        }
        if (exiting) {
            break;
        }

        if (pvconn) {
            pvconn_wait(pvconn);
        }
        LIST_FOR_EACH (sw, list_node, &switches) {
            switch_wait(sw);
        }
        if (server) {
            unixctl_server_wait(server);
        }

        poll_block();
    }

    if (pvconn) {
        pvconn_close(pvconn);
    }
    struct switch_context *sw;
    LIST_FOR_EACH_POP (sw, list_node, &switches) {
        switch_destroy(sw);
    }
    if (server) {
        unixctl_server_destroy(server);
    }
    service_stop();

    return 0;
}

