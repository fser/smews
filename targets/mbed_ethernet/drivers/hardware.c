/*
* Copyright or © or Copr. 2011, Michael Hauspie
* 
* Author e-mail: michael.hauspie@lifl.fr
* 
* This software is a computer program whose purpose is to design an
* efficient Web server for very-constrained embedded system.
* 
* This software is governed by the CeCILL license under French law and
* abiding by the rules of distribution of free software.  You can  use, 
* modify and/ or redistribute the software under the terms of the CeCILL
* license as circulated by CEA, CNRS and INRIA at the following URL
* "http://www.cecill.info". 
* 
* As a counterpart to the access to the source code and  rights to copy,
* modify and redistribute granted by the license, users are provided only
* with a limited warranty  and the software's author,  the holder of the
* economic rights,  and the successive licensors  have only  limited
* liability. 
* 
* In this respect, the user's attention is drawn to the risks associated
* with loading,  using,  modifying and/or developing or reproducing the
* software by the user in light of its specific status of free software,
* that may mean  that it is complicated to manipulate,  and  that  also
* therefore means  that it is reserved for developers  and  experienced
* professionals having in-depth computer knowledge. Users are therefore
* encouraged to load and test the software's suitability as regards their
* requirements in conditions enabling the security of their systems and/or 
* data to be ensured and,  more generally, to use and operate it in the 
* same conditions as regards security. 
* 
* The fact that you are presently reading this means that you have had
* knowledge of the CeCILL license and that you accept its terms.
*/
/*
  Author: Michael Hauspie <michael.hauspie@univ-lille1.fr>
  Created: 2011-07-13
  Time-stamp: <2011-09-14 16:22:40 (hauspie)>
*/

/* RFLPC includes */
#include <rflpc17xx/drivers/uart.h>
#include <rflpc17xx/drivers/ethernet.h>
#include <rflpc17xx/drivers/rit.h>
#include <rflpc17xx/drivers/timer.h>
#include <rflpc17xx/debug.h>
#include <rflpc17xx/printf.h>

/* Smews core includes */
#include "memory.h"
#include "connections.h"

/* Mbed port includes */
#include "target.h"
#include "mbed_debug.h"
#include "eth_input.h"
#include "protocols.h"

/* transmission descriptors */
rfEthDescriptor _tx_descriptors[TX_DESCRIPTORS] __attribute__ ((aligned(4)));
/* reception descriptors */
rfEthDescriptor _rx_descriptors[RX_DESCRIPTORS] __attribute__ ((aligned(4)));;

/* transmission status */
rfEthTxStatus   _tx_status[TX_DESCRIPTORS] __attribute__ ((aligned(4)));;
/* reception status */
rfEthRxStatus   _rx_status[RX_DESCRIPTORS] __attribute__ ((aligned(4)));;


/* Reception buffers */
uint8_t _rx_buffers[RX_DESCRIPTORS*RX_BUFFER_SIZE] __attribute__ ((section(".out_ram")));;

int putchar(int c)
{
    static int uart_init = 0;
    RFLPC_ASSERT_STACK();
    if (!uart_init)
    {
	rflpc_uart0_init();
	uart_init = 1;
    }
    rflpc_uart0_putchar(c);
    return c;
}

int mbed_garbage_buffers()
{
    int i;
    int collected = 0;
  /* Free sent packets. This loop will be executed on RX IRQ and on TX IRQ */
    for (i = 0 ; i <= LPC_EMAC->TxDescriptorNumber ; ++i)
    {
	if (_tx_descriptors[i].packet == _arp_reply_buffer) /* this one is static */
	    continue;
	if (_tx_status[i].status_info != PACKET_BEEING_SENT_MAGIC && _tx_descriptors[i].packet != NULL)
	{
	    mem_free(_tx_descriptors[i].packet, _tx_descriptors[i].control & 0x7FF);
	    _tx_descriptors[i].packet = NULL;
	    collected++;
	}
    }
    return collected;
 }

RFLPC_IRQ_HANDLER _eth_irq_handler()
{
    rfEthDescriptor *d;
    rfEthRxStatus *s;
 	
    rflpc_irq_global_disable();
    if (rflpc_eth_irq_get_status() & RFLPC_ETH_IRQ_EN_RX_DONE) /* packet received */
    {
    	while (rflpc_eth_get_current_rx_packet_descriptor(&d, &s))
    	{
	    /*mbed_dump_packet(d, s, 0);*/
	    if (mbed_process_input(d->packet, rflpc_eth_get_packet_size(s->status_info)) == ETH_INPUT_FREE_PACKET)
		rflpc_eth_done_process_rx_packet();
	    else
		break;
	}
    }
    mbed_garbage_buffers();
    rflpc_eth_irq_clear(rflpc_eth_irq_get_status());
    rflpc_irq_global_enable();

}

RFLPC_IRQ_HANDLER _uart_irq()
{
    char c = rflpc_uart0_getchar();
    int i;
    switch (c)
    {
	case 'd':
	    MBED_DEBUG("Memory left: %d bytes\r\n", get_free_mem());
	    MBED_DEBUG("RxDescriptor: %p\r\n", _rx_descriptors);
	    MBED_DEBUG("TxDescriptor: %p\r\n", _tx_descriptors);
	    for (i = 0 ; i < RX_DESCRIPTORS ; ++i)
	    {
		MBED_DEBUG("Buffer %d: %p\r\n", i, _rx_descriptors[i].packet);
	    }
	    rflpc_eth_dump_internals();
	    break;
	case 'c':
	    MBED_DEBUG("Forcing output buffer collection\r\n");
	    MBED_DEBUG("%d collected\r\n", mbed_garbage_buffers());
	    break;
	case 's':
	    MBED_DEBUG("Emmergency stop!\r\n");
	    MBED_DEBUG("Memory left: %d bytes\r\n", get_free_mem());
	    MBED_DEBUG("RxDescriptor: %p\r\n", _rx_descriptors);
	    MBED_DEBUG("TxDescriptor: %p\r\n", _tx_descriptors);
	    for (i = 0 ; i < RX_DESCRIPTORS ; ++i)
	    {
		MBED_DEBUG("Buffer %d: %p\r\n", i, _rx_descriptors[i].packet);
	    }
	    rflpc_eth_dump_internals();
	    while (1){}
	default:
	    break;
    }
}

static void _init_buffers()
{
    int i;
    RFLPC_ASSERT_STACK();
    for (i = 0 ; i < RX_DESCRIPTORS ; ++i)
    {
	_rx_descriptors[i].packet = _rx_buffers + RX_BUFFER_SIZE*i;
	_rx_descriptors[i].control = (RX_BUFFER_SIZE - 1) | (1 << 31); /* -1 encoding and enable irq generation on packet reception */
    }
    for (i = 0 ; i < TX_DESCRIPTORS ; ++i)
    {
	_tx_descriptors[i].packet = NULL;
    }
    rflpc_eth_set_tx_base_addresses(_tx_descriptors, _tx_status, TX_DESCRIPTORS);
    rflpc_eth_set_rx_base_addresses(_rx_descriptors, _rx_status, RX_DESCRIPTORS);
    rflpc_eth_set_irq_handler(_eth_irq_handler);
    rflpc_eth_irq_enable_set(RFLPC_ETH_IRQ_EN_RX_DONE);
}

EthAddr local_eth_addr;
void mbed_eth_hardware_init(void)
{
    /* Configure and start the timer. Timer 0 will be used for timestamping */
    rflpc_timer_enable(RFLPC_TIMER0);
    /* Clock the timer with the slower clock possible. Enough for millisecond precision */
    rflpc_timer_set_clock(RFLPC_TIMER0, RFLPC_CCLK_8);
    /* Set the pre scale register so that timer counter is incremented every 1ms */
    rflpc_timer_set_pre_scale_register(RFLPC_TIMER0, rflpc_clock_get_system_clock() / 8000);
    /* Start the timer */
    rflpc_timer_start(RFLPC_TIMER0);

    printf(" #####                                          #     # ######  ####### ######\r\n");
    printf("#     #  #    #  ######  #    #   ####          ##   ## #     # #       #     #\r\n");
    printf("#        ##  ##  #       #    #  #              # # # # #     # #       #     #\r\n");
    printf(" #####   # ## #  #####   #    #   ####          #  #  # ######  #####   #     #\r\n");
    printf("      #  #    #  #       # ## #       #         #     # #     # #       #     #\r\n");
    printf("#     #  #    #  #       ##  ##  #    #         #     # #     # #       #     #\r\n");
    printf(" #####   #    #  ######  #    #   ####          #     # ######  ####### ######\r\n");
    printf("\r\n");


    /* Set the MAC addr from the local ip */
    /* @todo: use hardware ID chip from MBED */
    local_eth_addr.addr[0] = 2;
    local_eth_addr.addr[1] = 3;
    local_eth_addr.addr[2] = local_ip_addr[3];
    local_eth_addr.addr[3] = local_ip_addr[2];
    local_eth_addr.addr[4] = local_ip_addr[1];
    local_eth_addr.addr[5] = local_ip_addr[0];

    printf("ETH Init...");
    rflpc_eth_init();
    rflpc_eth_set_mac_address(local_eth_addr.addr);
    _init_buffers();

    while (!rflpc_eth_link_state());
    printf(" done! Link is up\r\n");
    printf("My ip: %d.%d.%d.%d\r\n", local_ip_addr[3], local_ip_addr[2], local_ip_addr[1], local_ip_addr[0]);
    printf("Starting system takes %d ms\r\n", rflpc_timer_get_counter(RFLPC_TIMER0));
    rflpc_uart0_set_rx_callback(_uart_irq);
}