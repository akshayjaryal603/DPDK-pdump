/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright(c) 2010-2016 Intel Corporation
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <sys/types.h>
#include <sys/queue.h>
#include <netinet/in.h>
#include <setjmp.h>
#include <stdarg.h>
#include <ctype.h>
#include <errno.h>
#include <getopt.h>
#include <signal.h>
#include <stdbool.h>
#include <unistd.h>

#include <rte_common.h>
#include <rte_log.h>
#include <rte_malloc.h>
#include <rte_memory.h>
#include <rte_memcpy.h>
#include <rte_eal.h>
#include <rte_launch.h>
#include <rte_atomic.h>
#include <rte_cycles.h>
#include <rte_prefetch.h>
#include <rte_lcore.h>
#include <rte_per_lcore.h>
#include <rte_branch_prediction.h>
#include <rte_interrupts.h>
#include <rte_random.h>
#include <rte_debug.h>
#include <rte_ether.h>
#include <rte_ethdev.h>
#include <rte_mempool.h>
#include <rte_mbuf.h>
#include <rte_ring.h>
#include <rte_pdump.h>

FILE * f; 

static void print_stats(void);

static volatile bool force_quit;
//static volatile int quit = 0;

/* MAC updating enabled by default */
static int mac_updating = 1;

#define NUM_MBUFS 1024
#define MBUF_CACHE_SIZE 250

#define RTE_LOGTYPE_L2FWD RTE_LOGTYPE_USER1

#define MAX_PKT_BURST 32
#define BURST_TX_DRAIN_US 100 /* TX drain every ~100us */
#define MEMPOOL_CACHE_SIZE 256

/*SET COLORS CODE*/



/*
 * Configurable number of RX/TX ring descriptors
 */
#define RTE_TEST_RX_DESC_DEFAULT 1024
#define RTE_TEST_TX_DESC_DEFAULT 1024
/*static uint16_t nb_rxd = RTE_TEST_RX_DESC_DEFAULT;
static uint16_t nb_txd = RTE_TEST_TX_DESC_DEFAULT;*/

/*------------------------------------------------------------------------*/

volatile struct app_stats {
        struct {
                uint64_t rx_pkts;
                uint64_t enqueue_pkts;
                uint64_t enqueue_failed_pkts;
        } rx __rte_cache_aligned;
        struct {
                uint64_t dequeue_pkts;
                uint64_t enqueue_pkts;
                uint64_t enqueue_failed_pkts;
        } wkr __rte_cache_aligned;
        struct {
                uint64_t dequeue_pkts;
                /* Too early pkts transmitted directly w/o reordering */
                uint64_t early_pkts_txtd_woro;
                /* Too early pkts failed from direct transmit */
                uint64_t early_pkts_tx_failed_woro;
                uint64_t ro_tx_pkts;
                uint64_t ro_tx_failed_pkts;
        } tx __rte_cache_aligned;
} app_stats;

/*-----------------------------------------------------------------*/

/* ethernet addresses of ports 
static struct ether_addr l2fwd_ports_eth_addr[RTE_MAX_ETHPORTS];*/

/* mask of enabled ports */

static uint32_t l2fwd_enabled_port_mask = 0;

/* list of enabled ports */
static uint32_t l2fwd_dst_ports[RTE_MAX_ETHPORTS];

static unsigned int l2fwd_rx_queue_per_lcore = 1;

#define MAX_RX_QUEUE_PER_LCORE 16
#define MAX_TX_QUEUE_PER_PORT 16
struct lcore_queue_conf {
	unsigned n_rx_port;
	unsigned rx_port_list[MAX_RX_QUEUE_PER_LCORE];
} __rte_cache_aligned;
struct lcore_queue_conf lcore_queue_conf[RTE_MAX_LCORE];

//static struct rte_eth_dev_tx_buffer *tx_buffer[RTE_MAX_ETHPORTS];

/*static struct rte_eth_conf port_conf = {
	.rxmode = {
		.split_hdr_size = 0,
	},
	.txmode = {
		.mq_mode = ETH_MQ_TX_NONE,
	},
};*/

struct rte_mempool * l2fwd_pktmbuf_pool = NULL;

/* Per-port statistics struct */
struct l2fwd_port_statistics {
	uint64_t tx;
	uint64_t rx;
	uint64_t dropped;
} __rte_cache_aligned;
struct l2fwd_port_statistics port_statistics[RTE_MAX_ETHPORTS];

#define MAX_TIMER_PERIOD 86400 /* 1 day max */
/* A tsc-based timer responsible for triggering statistics printout */
static uint64_t timer_period = 10; /* default period is 10 seconds */

/* display usage */
static void
l2fwd_usage(const char *prgname)
{
	printf("%s [EAL options] -- -p PORTMASK [-q NQ]\n"
	       "  -p PORTMASK: hexadecimal bitmask of ports to configure\n"
	       "  -q NQ: number of queue (=ports) per lcore (default is 1)\n"
		   "  -T PERIOD: statistics will be refreshed each PERIOD seconds (0 to disable, 10 default, 86400 maximum)\n"
		   "  --[no-]mac-updating: Enable or disable MAC addresses updating (enabled by default)\n"
		   "      When enabled:\n"
		   "       - The source MAC address is replaced by the TX port MAC address\n"
		   "       - The destination MAC address is replaced by 02:00:00:00:00:TX_PORT_ID\n",
	       prgname);
}

static int
l2fwd_parse_portmask(const char *portmask)
{
	char *end = NULL;
	unsigned long pm;

	/* parse hexadecimal string */
	pm = strtoul(portmask, &end, 16);
	if ((portmask[0] == '\0') || (end == NULL) || (*end != '\0'))
		return -1;

	if (pm == 0)
		return -1;

	return pm;
}

static unsigned int
l2fwd_parse_nqueue(const char *q_arg)
{
	char *end = NULL;
	unsigned long n;

	/* parse hexadecimal string */
	n = strtoul(q_arg, &end, 10);
	if ((q_arg[0] == '\0') || (end == NULL) || (*end != '\0'))
		return 0;
	if (n == 0)
		return 0;
	if (n >= MAX_RX_QUEUE_PER_LCORE)
		return 0;

	return n;
}

static int
l2fwd_parse_timer_period(const char *q_arg)
{
	char *end = NULL;
	int n;

	/* parse number string */
	n = strtol(q_arg, &end, 10);
	if ((q_arg[0] == '\0') || (end == NULL) || (*end != '\0'))
		return -1;
	if (n >= MAX_TIMER_PERIOD)
		return -1;

	return n;
}

static const char short_options[] =
	"p:"  /* portmask */
	"q:"  /* number of queues */
	"T:"  /* timer period */
	;

#define CMD_LINE_OPT_MAC_UPDATING "mac-updating"
#define CMD_LINE_OPT_NO_MAC_UPDATING "no-mac-updating"

enum {
	/* long options mapped to a short option */

	/* first long only option value must be >= 256, so that we won't
	 * conflict with short options */
	CMD_LINE_OPT_MIN_NUM = 256,
};

static const struct option lgopts[] = {
	{ CMD_LINE_OPT_MAC_UPDATING, no_argument, &mac_updating, 1},
	{ CMD_LINE_OPT_NO_MAC_UPDATING, no_argument, &mac_updating, 0},
	{NULL, 0, 0, 0}
};

/* Parse the argument given in the command line of the application */
static int
pdump_parse_args(int argc, char **argv)
{
	int opt, ret, timer_secs;
	char **argvopt;
	int option_index;
	char *prgname = argv[0];

	argvopt = argv;

	while ((opt = getopt_long(argc, argvopt, short_options,
				  lgopts, &option_index)) != EOF) {

		switch (opt) {
		/* portmask */
		case 'p':
			l2fwd_enabled_port_mask = l2fwd_parse_portmask(optarg);
			if (l2fwd_enabled_port_mask == 0) {
				printf("invalid portmask\n");
				l2fwd_usage(prgname);
				return -1;
			}
			break;

		/* nqueue */
		case 'q':
			l2fwd_rx_queue_per_lcore = l2fwd_parse_nqueue(optarg);
			if (l2fwd_rx_queue_per_lcore == 0) {
				printf("invalid queue number\n");
				l2fwd_usage(prgname);
				return -1;
			}
			break;

		/* timer period */
		case 'T':
			timer_secs = l2fwd_parse_timer_period(optarg);
			if (timer_secs < 0) {
				printf("invalid timer period\n");
				l2fwd_usage(prgname);
				return -1;
			}
			timer_period = timer_secs;
			break;

		/* long options */
		case 0:
			break;

		default:
			l2fwd_usage(prgname);
			return -1;
		}
	}
	return ret;
}
/*-------------------------------Eth stats------------------------------------*/

static void
print_stats(void)
{
        uint16_t i;
        struct rte_eth_stats eth_stats;
        printf("\nRX thread stats:\n");
        printf(" - Pkts rxd:                            %"PRIu64"\n",
                                                app_stats.rx.rx_pkts);
        printf(" - Pkts enqd to workers ring:           %"PRIu64"\n",
                                                app_stats.rx.enqueue_pkts);
        printf("\nWorker thread stats:\n");
        printf(" - Pkts deqd from workers ring:         %"PRIu64"\n",
                                                app_stats.wkr.dequeue_pkts);
        printf(" - Pkts enqd to tx ring:                %"PRIu64"\n",
                                                app_stats.wkr.enqueue_pkts);
        printf(" - Pkts enq to tx failed:               %"PRIu64"\n",
                                                app_stats.wkr.enqueue_failed_pkts);
        printf("\nTX stats:\n");
        printf(" - Pkts deqd from tx ring:              %"PRIu64"\n",
                                                app_stats.tx.dequeue_pkts);
        printf(" - Ro Pkts transmitted:                 %"PRIu64"\n",
                                                app_stats.tx.ro_tx_pkts);
        printf(" - Ro Pkts tx failed:                   %"PRIu64"\n",
                                                app_stats.tx.ro_tx_failed_pkts);
        printf(" - Pkts transmitted w/o reorder:        %"PRIu64"\n",
                                                app_stats.tx.early_pkts_txtd_woro);
        printf(" - Pkts tx failed w/o reorder:          %"PRIu64"\n",
                                                app_stats.tx.early_pkts_tx_failed_woro);
        RTE_ETH_FOREACH_DEV(i) {
                rte_eth_stats_get(i, &eth_stats);
                printf("\nPort %u stats:\n", i);
                printf(" - Pkts in:   %"PRIu64"\n", eth_stats.ipackets);
                printf(" - Pkts out:  %"PRIu64"\n", eth_stats.opackets);
                printf(" - In Errs:   %"PRIu64"\n", eth_stats.ierrors);
                printf(" - Out Errs:  %"PRIu64"\n", eth_stats.oerrors);
                printf(" - Mbuf Errs: %"PRIu64"\n", eth_stats.rx_nombuf);
        }
}


/*--------------------------------signal handler--------------------------------------*/

static void
signal_handler(int signum)
{
	if (signum == SIGINT || signum == SIGTERM) {
		printf("\n\nSignal %d received, preparing to exit...\n",
				signum);
		force_quit = true;
	}
}
/*------------------------------------------------------------------------------------*/	

int
main(int argc, char **argv)
{

	int ret;
	uint16_t nb_ports;
	uint16_t portid, last_port;
	unsigned nb_ports_in_mask = 0;
	struct rte_ring *mbuf_ring;
	struct rte_mempool *mem_pool; 
	int rte_pdump;
	//struct rte_eth_stats * eth_stats; 
	
	/* init EAL */
	ret = rte_eal_init(argc, argv);

	if (ret < 0)
		rte_exit(EXIT_FAILURE, "Invalid EAL arguments\n");
	argc -= ret;
	argv += ret;
	
	force_quit = false;
	signal(SIGINT, signal_handler);
	signal(SIGTERM, signal_handler);
	printf("EAL Arguments Passed");
	ret = pdump_parse_args(argc, argv);

	/*if (ret < 0)
		rte_exit(EXIT_FAILURE, "Invalid L2FWD arguments\n");*/


	/* convert to number of cycles */
	timer_period *= rte_get_timer_hz();

	/*----------------------------------------------------------------------------*/
	#ifdef RTE_LIBRTE_PDUMP
		/* initialize packet capture framework */
		rte_pdump_init();
	#endif
	/*----------------------------------------------------------------------------*/

	nb_ports = rte_eth_dev_count_avail();
	if (nb_ports == 0)
		rte_exit(EXIT_FAILURE, "No Ethernet ports - bye\n");


	/* check port mask to possible port mask */
	if (l2fwd_enabled_port_mask & ~((1 << nb_ports) - 1))
		rte_exit(EXIT_FAILURE, "Invalid portmask; possible (0x%x)\n",
			(1 << nb_ports) - 1);


	/*
	 * Each logical core is assigned a dedicated TX queue on each port.
	 */
	RTE_ETH_FOREACH_DEV(portid) {
		/* skip ports that are not enabled */
		if ((l2fwd_enabled_port_mask & (1 << portid)) == 0)
			continue;

		if (nb_ports_in_mask % 2) {
			l2fwd_dst_ports[portid] = last_port;
			l2fwd_dst_ports[last_port] = portid;
		}
		else
			last_port = portid;

		nb_ports_in_mask++;
	}

	if (nb_ports_in_mask % 2) {
		printf("Notice: odd number of ports in portmask.\n");
		l2fwd_dst_ports[last_port] = last_port;
	}

	/*------------------------------------------------------------------------------*/

	
	/* Creates a new ring in memory to hold the packets. */
	/*rte_ring_create(const char * name, unsigned count, int socket_id, unsigned flags)*/ 
	
	mbuf_ring = rte_ring_create("NEW_RING111", NUM_MBUFS*2 , 0, 0);

	printf("\n*****Ring created Successfully\n");

	if (mbuf_ring == NULL)
		rte_exit(EXIT_FAILURE, "Cannot create mbuf ring\n");

 		
	/*------------------------------------------------------------------------------*/

	/* Creates a new mempool in memory to hold the mbufs. */


	/*rte_mempool_create ( const char *  name,unsigned n, unsigned elt_size,unsigned cache_size, unsigned private_data_size,
		rte_mempool_ctor_t *  mp_init, void *  mp_init_arg, rte_mempool_obj_cb_t * obj_init, void * obj_init_arg,
		int socket_id, unsigned flags ) */
	

	mem_pool = rte_mempool_create ("Memory_pool", 2000, 0, 0, 0, NULL, NULL, NULL, NULL , 0, 0);

	printf("\n*****Mempool created Successfully\n");

	if (mem_pool == NULL)
		rte_exit(EXIT_FAILURE, "Cannot create mbuf pool\n");
	/*------------------------------------------------------------------------------*/

	rte_pdump = rte_pdump_enable(1, 0, RTE_PDUMP_FLAG_RX, mbuf_ring, mem_pool, NULL);

	//rte_pdump = rte_pdump_enable_by_deviceid("fedora" , 0, RTE_PDUMP_FLAG_RX, mbuf_ring, mem_pool, NULL);

	printf("%d\n",  rte_errno);

	if (rte_pdump == 0)
		printf("Pdump enable created sucessfully\n");	
	else
		rte_exit(EXIT_FAILURE, "Cannot create pdump enable\n");

	printf("\n*****After pdump_enable\n");

	f = fopen("Dump.txt","w+");

	/*----------------------------------------------------------------------------*/

	printf("\n*****Text file created Successfully\n");

	/*----------------------------------------------------------------------------*/

	printf("%u\n", rte_ring_get_size(mbuf_ring));
	
	printf("%u\n", rte_ring_count(mbuf_ring));
	
	printf("%u\n", rte_ring_free_count(mbuf_ring));

	printf("%d\n", rte_ring_full(mbuf_ring));

	printf("%u\n", rte_ring_get_capacity(mbuf_ring));	

	while (!force_quit)
	{ 
        	void *packet;

		//rte_ring_dequeue (struct rte_ring *r, void **obj_p)

                if (rte_ring_dequeue(mbuf_ring, &packet) < 0)  
		{
                        usleep(2);
			
                        continue;
			printf("****Inside If statement");
       		}
		
		printf("****outside while loop\n");
		print_stats();
                fprintf(f ,"Received '%s'\n", (char *)packet);

                rte_mempool_put(mem_pool, packet);
        
	}
       /*----------------------------------------------------------------------------*/
        
	//rte_ring_dump( f, *mbuf_ring );
	
	if(f == NULL) 
		printf("\nUnable to create file.\n");
	else
		printf("\nSucessfully created.\n");

	
	/*----------------------------------------------------------------------------*/

	rte_ring_free(mbuf_ring);
	printf("Ring free sucessfully\n");

	rte_mempool_free(mem_pool);
	printf("Mempool free sucessfully\n");

	rte_pdump_disable(1, 0, RTE_PDUMP_FLAG_RX);
	printf("pdump disabled\n");


	return ret;		
	
}
