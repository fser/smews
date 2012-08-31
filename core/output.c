/*
* Copyright or © or Copr. 2008, Simon Duquennoy
* 
* Author e-mail: simon.duquennoy@lifl.fr
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

#include "output.h"
#include "types.h"
#include "checksum.h"
#include "timers.h"
#include "coroutines.h"
#include "smews.h"
#include "connections.h"
#include "memory.h"
#include "input.h" /* for *_HEADER_SIZE defines */
#include "handlers.h"
#include "random.h"

#ifndef DISABLE_TLS
	#include "tls.h"
	#include "hmac.h"
#endif

#ifndef DISABLE_POST
	#include "defines.h"
#endif

/* IPV6 Common values */
#ifdef IPV6

#define IP_VTRAFC_FLOWL ((uint32_t)0x60000000)
#define IP_NH_TTL ((uint16_t)0x0640)

#endif

/* Common values used for IP and TCP headers */
#define MSS_OPT 0x0204
#define IP_VHL_TOS ((uint16_t)0x4500)
#define IP_ID 0x0000
#define IP_OFFSET 0x0000
#define IP_TTL_PROTOCOL 0x4006
#define TCP_SRC_PORT 0x0050
#define TCP_HTTP_PORT 80
#define TCP_HTTPS_PORT 443
#define TCP_WINDOW 0x1000
#define TCP_URGP 0x0000

/* Pre-calculated partial IP checksum (for outgoing packets) */
#define BASIC_IP_CHK 0x8506

/* Pre-calculated partial TCP checksum (for outgoing packets) */
#ifndef DISABLE_TLS
	/* Constant parts are : Window + IP_PROTO_TCP(6) */
	#define BASIC_TCP_CHK 0x1006
#else
	#define BASIC_TCP_CHK 0x1056
#endif

/* Maximum output size depending on the MSS */
#define MAX_OUT_SIZE(mss) ((mss) & (~0 << (CHUNCKS_NBITS)))

/* Macros for static resources partial checksum blocks */
#define CHUNCKS_SIZE (1 << CHUNCKS_NBITS)
#define DIV_BY_CHUNCKS_SIZE(l) ((l) >> CHUNCKS_NBITS)
#define MODULO_CHUNCKS_SIZE(l) ((l) & ~(~0 << (CHUNCKS_NBITS)))
#define GET_NB_BLOCKS(l) (DIV_BY_CHUNCKS_SIZE(l) + (MODULO_CHUNCKS_SIZE(l) != 0))

/* Connection handler callback */
#ifndef DISABLE_ARGS
#define HANDLER_CALLBACK(connection,handler) { \
	if(CONST_ADDR(GET_GENERATOR((connection)->output_handler).handlers.get.handler) != NULL) \
		((generator_ ## handler ## _func_t*)CONST_ADDR(GET_GENERATOR((connection)->output_handler).handlers.get.handler))((connection)->protocol.http.args);}
#else
#define HANDLER_CALLBACK(connection,handler) { \
	if(CONST_ADDR(GET_GENERATOR((connection)->output_handler).handlers.get.handler) != NULL) \
		((generator_ ## handler ## _func_t*)CONST_ADDR(GET_GENERATOR((connection)->output_handler).handlers.get.handler))(NULL);}
#endif

/* Partially pre-calculated HTTP/1.1 header with checksum */
static CONST_VAR(char, serviceHttpHeader[]) = "HTTP/1.1 200 OK\r\nContent-Length:";
static CONST_VAR(char, serviceHttpHeaderPart2[]) = "\r\nContent-Type: text/plain\r\n\r\n";
static CONST_VAR(char, serviceHttpHeaderChunked[]) = "HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nTransfer-Encoding:chunked\r\n\r\n";

#define SERVICE_HTTP_HEADER_CHK 0x1871u
#define SERVICE_HTTP_HEADER_CHUNKED_CHK 0x2876u

#define MIN(a,b) ((a) < (b) ? (a) : (b))

struct curr_output_t {
	struct generator_service_t *service;
	char *buffer;
	unsigned char checksum[2];
	uint16_t content_length;
	uint16_t max_bytes;
	unsigned char next_outseqno[4];
	enum service_header_e service_header: 2;
};
static struct curr_output_t curr_output;

/* default DEV_PUT16 */
void dev_put16(unsigned char *word) {
	DEV_PUT(word[1]);
	DEV_PUT(word[0]);
}

void dev_put16_val(uint16_t word) {
	DEV_PUT(word >> 8);
	DEV_PUT(word);
}

/* default DEV_PUT32 */
void dev_put32(unsigned char *dword) {
	DEV_PUT16(dword+2);
	DEV_PUT16(dword);
}
	#define DEV_PUT32(dw) dev_put32(dw)

#ifdef IPV6
static void dev_put32_val(uint32_t word) {
	DEV_PUT(word >> 24);
	DEV_PUT(word >> 16);
	DEV_PUT(word >> 8);
	DEV_PUT(word);
}
#define DEV_PUT32_VAL(w) dev_put32_val(w)
#endif

/* default DEV_PUTN */
#ifndef DEV_PUTN
	#define DEV_PUTN(ptr,n) { uint16_t i; \
		for(i = 0; i < (n); i++) { \
			DEV_PUT(ptr[i]); \
		} \
	}
#endif

/* default DEV_PUTN_CONST */
#ifndef DEV_PUTN_CONST
	#define DEV_PUTN_CONST(ptr,n) { uint16_t i; \
		for(i = 0; i < (n); i++) { \
			DEV_PUT(CONST_READ_UI8((ptr) + i)); \
		} \
	}
#endif

#define CONTENT_LENGTH_SIZE 6
#define CHUNK_LENGTH_SIZE 4

static uint8_t _service_headers_size(enum service_header_e service_header)
{
	uint8_t size = 0;
	switch(service_header) {
		case header_standard:
			size += sizeof(serviceHttpHeader) - 1 + sizeof(serviceHttpHeaderPart2) - 1 + CONTENT_LENGTH_SIZE;
			break;
		case header_chunks:
			size += sizeof(serviceHttpHeaderChunked) - 1;
		case header_none:
			size += CHUNK_LENGTH_SIZE + 4;
			break;
		default:
			break;
	}
	return size;
}

/*-----------------------------------------------------------------------------------*/
char out_c(char c) {
	/* Must not generate a segment that is more than mss */
	if(curr_output.content_length == curr_output.max_bytes) {
#ifndef DISABLE_GP_IP_HANDLER
		if (curr_output.service == NULL) /* no service generator is when out is called from a dopacketout */
			return 0;
#endif
		cr_run(NULL
#ifndef DISABLE_POST
				,cor_type_get
#endif
				);
	}
#ifndef DISABLE_GP_IP_HANDLER
	if (curr_output.service != NULL) /* only compute checksum for http generator, not for gpip */
#endif
		checksum_add(c);
	curr_output.buffer[curr_output.content_length++] = c;
	return 1;
}

/*-----------------------------------------------------------------------------------*/
void smews_send_packet(struct connection *connection) {
	uint32_t index_in_file;
	uint16_t segment_length;
	unsigned char *ip_addr;
	unsigned char *port;
	unsigned char *next_outseqno;
	unsigned char *current_inseqno;
	const struct output_handler_t * /*CONST_VAR*/ output_handler;
	enum handler_type_e handler_type;
	/* buffer used to store the current content-length */
	#define CONTENT_LENGTH_SIZE 6 /* fser */
	#define CHUNK_LENGTH_SIZE 4   /* fser */
	char content_length_buffer[CONTENT_LENGTH_SIZE];
	unsigned char source_port[2];


#ifndef DISABLE_TLS
	/* used to construct TLS record */
	uint8_t *tls_record;
	//uint16_t record_length;

	/* shameless variable TODO revise */
	uint8_t *record_buffer;
#endif

#ifdef IPV6
	/* Full IPv6 adress of the packet */
	unsigned char full_ipv6_addr[16];
#endif

#ifdef SMEWS_SENDING
	SMEWS_SENDING;
#endif

	if(connection) {
#ifndef DISABLE_TIMERS
		connection->protocol.http.transmission_time = last_transmission_time;
#endif
#ifdef IPV6
		ip_addr = decompress_ip(connection->ip_addr+1,full_ipv6_addr,connection->ip_addr[0]);
#else
		ip_addr = connection->ip_addr;
#endif

		if (IS_HTTP(connection))
		{
			port = connection->protocol.http.port;
			next_outseqno = connection->protocol.http.next_outseqno;
			current_inseqno = connection->protocol.http.current_inseqno;
		}
		output_handler = connection->output_handler;
		/* Missing IFNDEF ?? fser */
		if(connection->tls_active == 1){
			UI16(source_port) = TCP_HTTPS_PORT;
		} else {
			UI16(source_port) = TCP_HTTP_PORT;
		}
	} else {
	  printf("Not HTTP case (fser) \n");
		ip_addr = rst_connection.ip_addr;
		port = rst_connection.port;
		next_outseqno = rst_connection.next_outseqno;
		current_inseqno = rst_connection.current_inseqno;
		output_handler = &ref_rst;
		/* Missing IFNDEF ?? fser */
		if(rst_connection.tls_active == 1){
			UI16(source_port) = TCP_HTTPS_PORT;
		} else {
			UI16(source_port) = TCP_HTTP_PORT;
		}
	}
	handler_type = CONST_UI8(output_handler->handler_type);

	/* compute the length of the TCP segment to be sent */
	printf("switch length (fser)Handler_type = ");
	switch(handler_type) {
		case type_control:
		  printf("type_control\n");
			segment_length = CONST_UI8(GET_CONTROL(output_handler).length);
			break;
		case type_file: {
		  printf("type_file\n");
			uint16_t max_out_size;
			uint32_t file_remaining_bytes;
			max_out_size = MAX_OUT_SIZE(connection->protocol.http.tcp_mss);
			file_remaining_bytes = UI32(connection->protocol.http.final_outseqno) - UI32(next_outseqno);
			segment_length = file_remaining_bytes > max_out_size ? max_out_size : file_remaining_bytes;
			index_in_file = CONST_UI32(GET_FILE(output_handler).length) - file_remaining_bytes;

#ifndef DISABLE_TLS
			if(connection->tls_active == 1){

				/* we reposition taking in account that remaining_bytes contains all TLS OVERHEAD */
				index_in_file = CONST_UI32(GET_FILE(output_handler).length) -
						(file_remaining_bytes - TLS_OVERHEAD*((file_remaining_bytes +  MAX_OUT_SIZE((uint16_t)connection->protocol.http.tcp_mss) - 1) / MAX_OUT_SIZE((uint16_t)connection->protocol.http.tcp_mss)));
				//printf("index in file %d\n",index_in_file);

			}
#endif

			break;
		}
		case type_generator:
		  printf("type_generator\n");
			segment_length = curr_output.content_length;
			segment_length += _service_headers_size(curr_output.service_header);
			break;
#ifndef DISABLE_GP_IP_HANDLER
		case type_general_ip_handler:
		  printf("type_generail_ip_handler\n");
			/* "cheat" the segment_length variable to reflect what needs to be sent
			 * the trick is used so that the code below can be reused
			 */
			segment_length = curr_output.content_length - TCP_HEADER_SIZE;
			break;
#endif

#ifndef DISABLE_TLS
		case type_tls_handshake:
		  printf("type_tls_handshake\n");
			switch(connection->tls->tls_state) {
				case server_hello:
					/* todo limitation of mss discuss(fie las asa ceea ce nu ar putea fi o pb, fie il fac dynamic content) */
					segment_length = TLS_HELLO_CERT_DONE_LEN;
					break;

				/* sending the CCS & Finished message in one segment */
				case ccs_fin_send:
					segment_length = TLS_CHANGE_CIPHER_SPEC_LEN + TLS_FINISHED_MSG_LEN + TLS_RECORD_HEADER_LEN;
					break;

			}

			break;
#endif
	}

	DEV_PREPARE_OUTPUT(segment_length + IP_HEADER_SIZE + TCP_HEADER_SIZE);

	/* start to send IP header */
#ifdef IPV6

	/* We are IPv6 (yeah!), without traffic class or flow label */
	DEV_PUT32_VAL(IP_VTRAFC_FLOWL);

	/* our payload length is */
	DEV_PUT16_VAL(segment_length + TCP_HEADER_SIZE);

	/* We have TCP inside and Hop Limit is 64 */
#ifndef DISABLE_GP_IP_HANDLER
	if (IS_GPIP(connection))
	{
		/* do not use TCP as Next Header but the protocol value of the gp_ip connection */
		DEV_PUT16_VAL((0xFF) | (connection->protocol.gpip.protocol << 8));
	}
	else
#endif
	DEV_PUT16_VAL(IP_NH_TTL);

	/* Put source & dest IP */
	DEV_PUT32(&local_ip_addr[12]);
	DEV_PUT32(&local_ip_addr[8]);
	DEV_PUT32(&local_ip_addr[4]);
	DEV_PUT32(&local_ip_addr[0]);

	DEV_PUT32(&ip_addr[12]);
	DEV_PUT32(&ip_addr[8]);
	DEV_PUT32(&ip_addr[4]);
	DEV_PUT32(&ip_addr[0]);
#else
	/* send vhl, tos, IP header length */
	DEV_PUT16_VAL(IP_VHL_TOS);

	/* send IP packet length */
	DEV_PUT16_VAL(segment_length + IP_HEADER_SIZE + TCP_HEADER_SIZE);

	/* send IP ID, offset, ttl and protocol (TCP) */
	DEV_PUT16_VAL(IP_ID);
	DEV_PUT16_VAL(IP_OFFSET);
#ifndef DISABLE_GP_IP_HANDLER
	if (IS_GPIP(connection))
	{
		/* do not use TCP as protocol number but the protocol value of the gpip connection */
		DEV_PUT16_VAL(0xFF00 | connection->protocol.gpip.protocol);
	}
	else
#endif
	DEV_PUT16_VAL(IP_TTL_PROTOCOL);

	/* complete IP precalculated checksum */
	checksum_init();
#ifndef DISABLE_GP_IP_HANDLER
	if (IS_GPIP(connection))
	{
		checksum_add16(IP_VHL_TOS);
		checksum_add16(IP_ID);
		checksum_add16(IP_OFFSET);
		/* The BASIC_IP_CHK can not be used here as we changed the protocol number */
		checksum_add16(0xFF00 | connection->protocol.gpip.protocol);
	}
	else
#endif
	UI16(current_checksum) = BASIC_IP_CHK;
	checksum_add32(local_ip_addr);
	checksum_add16(segment_length + IP_HEADER_SIZE + TCP_HEADER_SIZE);

	checksum_add32(ip_addr);
	checksum_end();

	/* send IP checksum */
	DEV_PUT16_VAL(~UI16(current_checksum));

	/* send IP source address */
	DEV_PUT32(local_ip_addr);

	/* send IP destination address */
	DEV_PUT32(ip_addr);
#endif

	/* if the connection is for gpip, send the payload and return */
#ifndef DISABLE_GP_IP_HANDLER
	if (IS_GPIP_HANDLER(output_handler))
	{
		DEV_PUTN(curr_output.buffer, curr_output.content_length);
		DEV_OUTPUT_DONE;
		return;
	}
#endif

	/* start to send TCP header */

	/* send TCP source port */
	DEV_PUT16(source_port);

	/* send TCP destination port */
	DEV_PUT16(port);

	/* send TCP sequence number */
	DEV_PUT32(next_outseqno);

	/* send TCP acknowledgement number */
	DEV_PUT32(current_inseqno);

	/* send TCP header length & flags */
	DEV_PUT(GET_FLAGS(output_handler) & TCP_SYN ? 0x60 : 0x50);
	DEV_PUT(GET_FLAGS(output_handler));

	/* send TCP window */
	DEV_PUT16_VAL(TCP_WINDOW);

	/* complete precalculated TCP checksum */

	checksum_init();
	/* start to construct TCP checksum starting from a precalculated value */
	UI16(current_checksum) = BASIC_TCP_CHK;
#ifdef IPV6
	checksum_add32(&local_ip_addr[0]);
	checksum_add32(&local_ip_addr[4]);
	checksum_add32(&local_ip_addr[8]);
	checksum_add32(&local_ip_addr[12]);
#else
	checksum_add32(local_ip_addr);
#endif

	checksum_add16(segment_length + 20);

	checksum_add32(next_outseqno);

	checksum_add(GET_FLAGS(output_handler) & TCP_SYN ? 0x60 : 0x50);
	checksum_add(GET_FLAGS(output_handler));

#ifdef IPV6
	checksum_add32(&ip_addr[0]);
	checksum_add32(&ip_addr[4]);
	checksum_add32(&ip_addr[8]);
	checksum_add32(&ip_addr[12]);
#else
	checksum_add32(ip_addr);
#endif

	/* checksum source port */
	checksum_add16(UI16(source_port)); /* Must be useless since already given as initializer (fser) */
	
	/* checksum destination port */
	checksum_add16(UI16(port));

	checksum_add32(current_inseqno);

	/* HTTP contents checksum part */
	switch(handler_type) {
		case type_generator:
			/* add service checksum */
			checksum_add16(UI16(curr_output.checksum));
			/* add HTTP header checksum */
			switch(curr_output.service_header) {
				uint16_t length;
				int16_t i;
				case header_standard:
					checksum_add16(SERVICE_HTTP_HEADER_CHK);
					/* create the HTTP Content-Length string on a even number of chars and start computing service checksum */
					checksum_add(0); /* odd bytes alignement */
					length = curr_output.content_length;
					for(i = CONTENT_LENGTH_SIZE - 1; i >= 0; i--) {
						unsigned char c = (length % 10) + '0';
						content_length_buffer[i]= c;
						checksum_add(c);
						length /= 10;
					}
					checksum_add(0); /* remove odd bytes alignement */
					break;
				case header_chunks:
					checksum_add16(SERVICE_HTTP_HEADER_CHUNKED_CHK);
					break; // fser
				case header_none:
					checksum_add(0); /* odd bytes alignement */
					length = curr_output.content_length;
					for(i = CHUNK_LENGTH_SIZE - 1; i >= 0; i--) {
						unsigned char c = (length & 0x0f) + '0';
						if(c > '9')
							c += -'0' + 'a' - 10;
						content_length_buffer[i]= c;
						checksum_add(c);
						length >>= 4;
					}
					checksum_add(0); /* remove odd bytes alignement */
					checksum_add16(0x0d0a);
					if(curr_output.content_length % 2) {
						checksum_add16(0x0a0d);
					} else {
						checksum_add16(0x0d0a);
					}
					break;
			}
			break;
		case type_control:
			if(GET_FLAGS(output_handler) & TCP_SYN){ /* Checksum the syn ack tcp options (MSS) */
				checksum_add16(MSS_OPT);
				checksum_add16((uint16_t)connection->protocol.http.tcp_mss);
			}
			break;
		case type_file: {
			#ifndef DISABLE_TLS
			if(connection->tls_active == 1){
				uint16_t i;
				uint16_t data_length = segment_length - TLS_OVERHEAD;
				const char *tmpptr = (const char*)(CONST_ADDR(GET_FILE(output_handler).data) + index_in_file);
				tls_record = mem_alloc(data_length);
				tls_record = CONST_READ_NBYTES(tls_record,tmpptr,data_length);

				printf("Sending %d from a total of %d static file\n",data_length,(output_handler->handler_data).file.length);
				printf("\n\nTCP data before sending (part of file contents) (%d bytes) :",data_length);
				for (i = 0 ; i < data_length; i++){
					printf("%02x", tls_record[i]);
				}
				printf("\n");

				/* preparing the HMAC hash for calculation */
				hmac_init(SHA1,connection->tls->server_mac,SHA1_KEYSIZE);
				hmac_preamble(connection->tls, data_length, ENCODE);

				/* checksuming TLS Record header */
				checksum_add(TLS_CONTENT_TYPE_APPLICATION_DATA);
				checksum_add(TLS_SUPPORTED_MAJOR);
				checksum_add(TLS_SUPPORTED_MINOR);
				checksum_add((data_length + MAC_KEYSIZE) >> 8);
				checksum_add((uint8_t)(data_length + MAC_KEYSIZE));

				/* Hash, encrypt and checksum data */
				for(i = 0; i < data_length; i++){
					//diferenta s-ar putea sa fie la marimea cat fac hmac
					hmac_update(tls_record[i]);
					rc4_crypt(&tls_record[i],MODE_ENCRYPT);
					checksum_add(tls_record[i]);

				}
				hmac_finish(SHA1);

				/* checksuming MAC */
				for(i = 0; i < MAC_KEYSIZE; i++){
					rc4_crypt(&sha1.buffer[i],MODE_ENCRYPT);
					checksum_add(sha1.buffer[i]);
				}


			} else
#endif
			{
				uint16_t i;
				uint32_t tmp_sum = 0;
				uint16_t *tmpptr = (uint16_t *)CONST_ADDR(GET_FILE(output_handler).chk) + DIV_BY_CHUNCKS_SIZE(index_in_file);

				for(i = 0; i < GET_NB_BLOCKS(segment_length); i++) {
					tmp_sum += CONST_READ_UI16(tmpptr++);
				}
				checksum_add32((const unsigned char*)&tmp_sum);
				break;
			}
		}
#ifndef DISABLE_TLS
		case type_tls_handshake:

			switch(connection->tls->tls_state) {
				uint16_t i;
				case server_hello:

					init_rand(0xABCDEF12); /* TODO move random init somewhere else */
					rand_next(connection->tls->server_random.lfsr_int);

					/* checksumming handshake records
					 * TODO this should be precalculated */
					for(i = 0; i < TLS_HELLO_CERT_DONE_LEN - 32; i++) {
						checksum_add(s_hello_cert_done[i]);
					}

					/* checksumming random value */
					for(i = 0; i < 32 ; i++){
						checksum_add(connection->tls->server_random.lfsr_char[i]);
					}


					break;

				case ccs_fin_send:
					/* calculating checksum for CCS */
					for(i = 0; i < TLS_CHANGE_CIPHER_SPEC_LEN; i++) {
						checksum_add(tls_ccs_msg[i]);
					}
					/* calculating checksum for Finished message */
					record_buffer = mem_alloc(TLS_FINISHED_MSG_LEN + START_BUFFER);
					build_finished(connection->tls,record_buffer);
					checksum_add(TLS_CONTENT_TYPE_HANDSHAKE);
					checksum_add(TLS_SUPPORTED_MAJOR);
					checksum_add(TLS_SUPPORTED_MINOR);
					checksum_add(0);
					checksum_add(TLS_FINISHED_MSG_LEN);
					for(i = 0; i < TLS_FINISHED_MSG_LEN; i++)
						checksum_add(record_buffer[START_BUFFER + i]);

					break;



			}
			break;
#endif

	}
	
	checksum_end();

	/* send TCP checksum (complemented)*/
	DEV_PUT16_VAL(~UI16(current_checksum));

	/* send TCP urgent pointer */
	DEV_PUT16_VAL(TCP_URGP);

	/* start sending HTTP contents */
	printf("switch (http contents fser) handler_type: ");
	switch(handler_type) {
		case type_generator:
		  printf("type_generator\n");
		  printf("curr_output.service_header = ");
			switch(curr_output.service_header) {
			  
				case header_standard:
				  printf("header_standard\n");
					DEV_PUTN_CONST(serviceHttpHeader, sizeof(serviceHttpHeader)-1);
					DEV_PUTN(content_length_buffer, CONTENT_LENGTH_SIZE);
					DEV_PUTN_CONST(serviceHttpHeaderPart2, sizeof(serviceHttpHeaderPart2)-1);
					break;
				case header_chunks:
				  printf("header_chunks\n");
					DEV_PUTN_CONST(serviceHttpHeaderChunked, sizeof(serviceHttpHeaderChunked)-1);
				case header_none:
				  printf("header_none\n");
					DEV_PUTN(content_length_buffer, CHUNK_LENGTH_SIZE);
					DEV_PUT16_VAL(0x0d0a);
					break;
			}
			DEV_PUTN(curr_output.buffer, curr_output.content_length);
			if(curr_output.service_header != header_standard) {
				DEV_PUT16_VAL(0x0d0a);
			}
			break;
		case type_control:
		  printf("type_control\n");
			if(GET_FLAGS(output_handler) & TCP_SYN) {
				/* Send the syn ack tcp options (MSS) */
				DEV_PUT16_VAL(MSS_OPT);
				DEV_PUT16_VAL((uint16_t)connection->protocol.http.tcp_mss);
			}
			break;
		case type_file: {
		  printf("type_file\n");
			/* Send the payload of the packet */
#ifndef DISABLE_TLS
			if(connection->tls_active == 1){

				uint16_t i;
				uint16_t record_len = segment_length - TLS_RECORD_HEADER_LEN;
				/* sending TLS Record Header */
				DEV_PUT(TLS_CONTENT_TYPE_APPLICATION_DATA);
				DEV_PUT(TLS_SUPPORTED_MAJOR);
				DEV_PUT(TLS_SUPPORTED_MINOR);
				DEV_PUT((record_len) >> 8);
				DEV_PUT((uint8_t)(record_len));

				/* sending TLS Payload */
				printf("Sending TLS data to network (%d bytes)\n ",record_len);
				/* fser
				  for(i = 0; i < (record_len - MAC_KEYSIZE); i++){
					DEV_PUT(tls_record[i]);
					printf("%02x",tls_record[i]);
				}
				*/
				DEV_PUTN(tls_record, (record_len - MAC_KEYSIZE));

				/* sending MAC */
				/* fser
				   for(i = 0; i < MAC_KEYSIZE; i++){
					DEV_PUT(sha1.buffer[i]);
					printf("%02x",sha1.buffer[i]);
				}
				printf("\n");
				*/
				DEV_PUTN(sha1.buffer, MAC_KEYSIZE);

				/* free payload allocated for bringing data from external memory */
				mem_free(tls_record, record_len - MAC_KEYSIZE);

				/* update number of record sent */
				connection->tls->encode_seq_no.long_int++;

			} else

#endif
			{
				const char *tmpptr = (const char*)(CONST_ADDR(GET_FILE(output_handler).data) + index_in_file);
				DEV_PUTN_CONST(tmpptr, segment_length);
				break;
			}
			break; // fser
			// fser		}
		default: /* Should never happen but avoid warnings*/
		  printf("this should never happen (fser)");
			return;
	}

#ifndef DISABLE_TLS
		case type_tls_handshake:

			switch(connection->tls->tls_state) {
				case server_hello:
					tls_send_hello_cert_done(connection->tls);
					connection->tls->tls_state = key_exchange;
					break;

				case ccs_fin_send:

					tls_send_change_cipher(connection->tls);
					tls_send_finished(record_buffer + START_BUFFER);

					connection->tls->tls_state = established;
					mem_free(record_buffer,TLS_FINISHED_MSG_LEN + START_BUFFER);
					break;
			}
#endif

	}
	
	/* update next sequence number and inflight segments */
	if(GET_FLAGS(output_handler) & TCP_SYN) {
		UI32(connection->protocol.http.next_outseqno)++;
	} else if(connection) {
		UI32(connection->protocol.http.next_outseqno) += segment_length;
#ifndef DISABLE_TLS
		//if(connection->tls_active == 1) UI32(connection->protocol.http.next_outseqno)+= MAC_KEYSIZE + TLS_RECORD_HEADER_LEN;
#endif
		UI16(connection->protocol.http.inflight) += segment_length;
#ifndef DISABLE_TLS
		//if(connection->tls_active == 1) UI16(connection->inflight) += MAC_KEYSIZE + TLS_RECORD_HEADER_LEN;
#endif

		if(handler_type == type_generator) {
			if(curr_output.service_header == header_standard || curr_output.content_length == 0) {
				/* set final_outseqno as soon as it is known */
				UI32(connection->protocol.http.final_outseqno) = UI32(connection->protocol.http.next_outseqno);
			}
		}
	}

	if(handler_type==type_generator){
		static int cpt=0;
		if(++cpt==2)return;
	}

	DEV_OUTPUT_DONE;
}

/*-----------------------------------------------------------------------------------*/
static inline int32_t able_to_send(const struct connection *connection) {
	if (!something_to_send(connection))
		return 0;
#ifndef DISABLE_GP_IP_HANDLER
	if (IS_GPIP(connection))
		return 1;
#endif
#ifndef DISABLE_COMET
	if (connection->protocol.http.comet_passive)
		return 0;
#endif
	return UI16(connection->protocol.http.inflight) + (uint16_t)connection->protocol.http.tcp_mss <= UI16(connection->protocol.http.cwnd);
}

#ifndef DISABLE_GP_IP_HANDLER
static char gpip_output_buffer[OUTPUT_BUFFER_SIZE];
#endif

/*-----------------------------------------------------------------------------------*/
char smews_send(void) {
	struct connection *connection = NULL;
	const struct output_handler_t * /*CONST_VAR*/ old_output_handler = NULL;


	/* sending reset has the highest priority */
	if(UI16(rst_connection.port)) {
		smews_send_packet(NULL);
		UI16(rst_connection.port) = 0;
		return 1;
	}

	/* we first choose a valid connection */
		FOR_EACH_CONN(conn, {
		if(able_to_send(conn)) {
			connection = conn;
			break;
		}
	})

	if(connection == NULL) {
		return 0;
	}
	/* enable a round robin */
	all_connections = connection->next;
#ifndef DISABLE_GP_IP_HANDLER
	if (IS_GPIP(connection))
	{
		curr_output.buffer = gpip_output_buffer;/* mem_alloc(OUTPUT_BUFFER_SIZE); */
#ifndef DEV_MTU
		curr_output.max_bytes = OUTPUT_BUFFER_SIZE;
#else
		curr_output.max_bytes = (OUTPUT_BUFFER_SIZE + IP_HEADER_SIZE > DEV_MTU) ? DEV_MTU - IP_HEADER_SIZE : OUTPUT_BUFFER_SIZE;
#endif
		if (curr_output.buffer == NULL) /* no more memory */
			return 0;
		curr_output.content_length = 0;
		curr_output.service = NULL;
		connection->output_handler->handler_data.generator.handlers.gp_ip.dopacketout(connection);
		connection->protocol.gpip.want_to_send = 0;
		smews_send_packet(connection);
		/* mem_free(curr_output.buffer, OUTPUT_BUFFER_SIZE); */
		free_connection(connection);
		return 0;
	}
#endif

	if(!connection->protocol.http.ready_to_send){
		old_output_handler = connection->output_handler;
		connection->output_handler = &ref_ack;
	}
#ifndef DISABLE_COMET
	/* do we need to acknowledge a comet request without answering it? */
	else if(connection->protocol.http.comet_send_ack == 1) {
		old_output_handler = connection->output_handler;
		connection->output_handler = &ref_ack;
	}
#endif

	/* get the type of web applicative resource */
	switch(CONST_UI8(connection->output_handler->handler_type)) {
		case type_control:
			/* preparing to send TCP control data */
			smews_send_packet(connection);
			connection->output_handler = NULL;
			if(connection->protocol.http.tcp_state == tcp_closing) {
				/* WARNING: TODO: check what has to be done after this. In the actual state,
				 * it seems that the freed connection is used after the free...
				 */
				free_connection(connection);
				return 0; /* WARNING: this return has been put to "fix" previous comment. */
			}

			if(old_output_handler && !connection->protocol.http.ready_to_send)
				connection->output_handler = old_output_handler;
#ifndef DISABLE_COMET
			else if(old_output_handler) {
				/* restore the right old output handler */
				connection->output_handler = old_output_handler;
				connection->protocol.http.comet_send_ack = 0;
				UI32(connection->protocol.http.final_outseqno) = UI32(connection->protocol.http.next_outseqno);
				/* call initget (which must not generate any data) */
				HANDLER_CALLBACK(connection,initget);
			}
#endif
			break;
		case type_file:
			smews_send_packet(connection);
			break;
#ifndef DISABLE_TLS
		case type_tls_handshake:
			smews_send_packet(connection);
			connection->output_handler = NULL;
			break;
#endif
		case type_generator: {
			char is_persistent;
			char is_retransmitting;
			char has_ended;
			struct in_flight_infos_t *if_infos = NULL;

			/* Set the maximum available size for generator so that the mss is respected */
			/* The value set here is the needed value for the following segments (i.e. not the first) of a same http data stream
			 * thus, the http header size used is only the no header one (the chunk size).
			 * If the segment that we will generate ends to be the first, the value is lowered in the following if block */
			curr_output.max_bytes = MIN(OUTPUT_BUFFER_SIZE,MAX_OUT_SIZE(connection->protocol.http.tcp_mss) - _service_headers_size(header_none));
			/* creation and initialization of the generator_service if needed */
			if(connection->protocol.http.generator_service == NULL) {
				connection->protocol.http.generator_service = mem_alloc(sizeof(struct generator_service_t)); /* test NULL: done */
				if(connection->protocol.http.generator_service == NULL) {
					return 1;
				}
				curr_output.service = connection->protocol.http.generator_service;
				/* if we create the service, it is the first segment of the answer stream, we need
				 * to reduce its size to fit the mss if the segment is not the last.
				 * Thus, we use the biggest http header size possible to compute the available space for data */
				curr_output.max_bytes = MIN(OUTPUT_BUFFER_SIZE,MAX_OUT_SIZE(connection->protocol.http.tcp_mss) - _service_headers_size(header_chunks));
				/* init generator service */
				curr_output.service->service_header = header_standard;
				curr_output.service->in_flight_infos = NULL;
				curr_output.service->is_persistent = CONST_UI8(GET_GENERATOR(connection->output_handler).prop) == prop_persistent;
				UI32(curr_output.service->curr_outseqno) = UI32(connection->protocol.http.next_outseqno);
				/* init coroutine */
				cr_init(&curr_output.service->coroutine);
#ifndef DISABLE_POST
				if(connection->protocol.http.post_data && connection->protocol.http.post_data->content_type != CONTENT_TYPE_APPLICATION_47_X_45_WWW_45_FORM_45_URLENCODED){
					curr_output.service->coroutine.func.func_post_out = CONST_ADDR(GET_GENERATOR(connection->output_handler).handlers.post.dopostout);
					curr_output.service->coroutine.params.out.content_type = connection->protocol.http.post_data->content_type;
					curr_output.service->coroutine.params.out.post_data = connection->protocol.http.post_data->post_data;
				}
				else{
#endif
					curr_output.service->coroutine.func.func_get = CONST_ADDR(GET_GENERATOR(connection->output_handler).handlers.get.doget);
#ifndef DISABLE_ARGS
					curr_output.service->coroutine.params.args = connection->protocol.http.args;
#endif
#ifndef DISABLE_POST
				}
#endif
				/* we don't know yet the final output sequence number for this service */
				UI32(connection->protocol.http.final_outseqno) = UI32(connection->protocol.http.next_outseqno) - 1;
#ifndef DISABLE_COMET
				/* if this is a comet generator, manage all listenning clients */
				if(CONST_UI8(connection->output_handler->handler_comet)) {
					const struct output_handler_t *current_handler = connection->output_handler;
					/* if this is a comet handler, this connection is active, others are set as passive */
					FOR_EACH_CONN(conn, {
						if(conn->output_handler == current_handler) {
							conn->protocol.http.comet_passive = (conn != connection);
						}
					})
				}
				/* manage streamed comet data */
				if(CONST_UI8(connection->output_handler->handler_stream)) {
					if(connection->protocol.http.comet_streaming) {
						curr_output.service->service_header = header_none;
					}
					connection->protocol.http.comet_streaming = 1;
				}
#endif
			}

			/* init the global curr_output structure (usefull for out_c) */
			curr_output.service = connection->protocol.http.generator_service;
			UI32(curr_output.next_outseqno) = UI32(connection->protocol.http.next_outseqno);

			/* is the service persistent or not? */
			is_persistent = curr_output.service->is_persistent;
			/* are we retransmitting a lost segment? */
			is_retransmitting = UI32(curr_output.next_outseqno) != UI32(curr_output.service->curr_outseqno);

			/* put the coroutine (little) stack in the shared (big) stack if needed.
			 * This step has to be done before before any context_restore or context_backup */
			if(cr_prepare(&curr_output.service->coroutine) == NULL) { /* test NULL: done */
				return 1;
			}

			/* check if the segment need to be generated or can be resent from a buffer */
			if(!is_persistent || !is_retransmitting) { /* segment generation is needed */

				/* setup the http header for this segment */
				if(!is_persistent && is_retransmitting) {
					/* if the current context is not the right one, restore it */
					if_infos = context_restore(curr_output.service, connection->protocol.http.next_outseqno);
					/* if_infos is NULL if the segment to be sent is the last void http chunck */
					if(if_infos != NULL) {
						curr_output.service_header = if_infos->service_header;
					} else {
						curr_output.service_header = header_none;
					}
				} else {
					curr_output.service_header = curr_output.service->service_header;
				}

				/* initializations before generating the segment */
				curr_output.content_length = 0;
				checksum_init();
				curr_output.buffer = NULL;

				has_ended = curr_output.service->coroutine.curr_context.status == cr_terminated;
				/* is has_ended is true, the segment is a void chunk: no coroutine call is needed.
				 * else, run the coroutine to generate one segment */
				if(!has_ended) {
					/* allocate buffer for data generation */
					curr_output.buffer = mem_alloc(OUTPUT_BUFFER_SIZE); /* test NULL: done */
					if(curr_output.buffer == NULL) {
						return 1;
					}

					/* we will generate a segment for the first time, so we will need to store new in-flight information */
					if(!is_retransmitting) {
						if_infos = mem_alloc(sizeof(struct in_flight_infos_t)); /* test NULL: done */
						if(if_infos == NULL) {
							mem_free(curr_output.buffer, OUTPUT_BUFFER_SIZE);
							return 1;
						}
					}

					/* we generate new non persistent data. backup the context before running it */
					if(!is_persistent && !is_retransmitting) {
						if_infos->service_header = curr_output.service_header;
						if(context_backup(curr_output.service, curr_output.next_outseqno, if_infos) == NULL) { /* test NULL: done */
							mem_free(curr_output.buffer, OUTPUT_BUFFER_SIZE);
							mem_free(if_infos, sizeof(struct in_flight_infos_t));
							return 1;
						}
					}

					/* run the coroutine (generate one segment) */
#ifndef DISABLE_POST
					if(connection->protocol.http.post_data && connection->protocol.http.post_data->content_type != CONTENT_TYPE_APPLICATION_47_X_45_WWW_45_FORM_45_URLENCODED)
						cr_run(&curr_output.service->coroutine,cor_type_post_out);
					else
#endif
						cr_run(&curr_output.service->coroutine
#ifndef DISABLE_POST
								,cor_type_get
#endif
								);
					has_ended = curr_output.service->coroutine.curr_context.status == cr_terminated;
#ifndef DISABLE_POST
					/* cleaning post_data */
					if(has_ended && connection->protocol.http.post_data){
						mem_free(connection->protocol.http.post_data,sizeof(struct post_data_t));
						connection->protocol.http.post_data = NULL;
					}
#endif
					/* save the generated buffer after generation if persistent */
					if(is_persistent) {
						/* add it to the in-flight segments list */
						if_infos->service_header = curr_output.service_header;
						UI32(if_infos->next_outseqno) = UI32(connection->protocol.http.next_outseqno);
						if_infos->infos.buffer = curr_output.buffer;
						if_infos->next = curr_output.service->in_flight_infos;
						curr_output.service->in_flight_infos = if_infos;

					}
				}

				/* finalizations after the segment generation */
				checksum_end();
				UI16(curr_output.checksum) = UI16(current_checksum);
				/* save the current checksum in the in flight segment infos */
				if(if_infos) {
					UI16(if_infos->checksum) = UI16(current_checksum);
				}
			} else { /* the segment has to be resent from a buffer: restore it */
				if_infos = if_select(curr_output.service, connection->protocol.http.next_outseqno);
				curr_output.buffer = if_infos->infos.buffer;
				curr_output.service_header = if_infos->service_header;
				UI16(curr_output.checksum) = UI16(if_infos->checksum);
			}

			/* select the right HTTP header */
			switch(curr_output.service_header) {
				case header_standard:
					if(!has_ended || CONST_UI8(connection->output_handler->handler_stream)) {
						curr_output.service_header = header_chunks;
					}
					break;
				case header_chunks:
					curr_output.service_header = header_none;
					break;
				default:
					break;
			}

			/* send the segment */
#ifndef DISABLE_COMET
			/* if this is a comet handler, send the segment to all listenning clients */
			if(CONST_UI8(connection->output_handler->handler_comet)) {
				const struct output_handler_t *current_handler = connection->output_handler;
				FOR_EACH_CONN(conn, {
					if(conn->output_handler == current_handler && able_to_send(conn)) {
						if(!CONST_UI8(conn->output_handler->handler_stream)) {
							smews_send_packet(conn);
						} else {
							if(curr_output.content_length > 0) {
								smews_send_packet(conn);
							}
							if(has_ended) {
								UI32(conn->protocol.http.final_outseqno) = UI32(conn->protocol.http.next_outseqno);
							}
						}
					}
				})
			} else
#endif
			{
			/* simply send the segment */
				smews_send_packet(connection);
			}

			/* free the tmp buffer used for non persistent data generation */
			if(!is_persistent) {
				mem_free(curr_output.buffer, OUTPUT_BUFFER_SIZE);
			}

			if(!is_retransmitting) {
				/* update next_outseqno for the current context */
				curr_output.service->service_header = curr_output.service_header;
				UI32(curr_output.service->curr_outseqno) = UI32(connection->protocol.http.next_outseqno);
			}

#ifndef DISABLE_COMET
			/* clean comet service here (this is quite dirty) */
			if(CONST_UI8(connection->output_handler->handler_stream) && has_ended && UI16(connection->protocol.http.inflight) == 0) {
				clean_service(connection->protocol.http.generator_service, NULL);
				mem_free(connection->protocol.http.generator_service, sizeof(struct generator_service_t));
				connection->protocol.http.generator_service = NULL;
			}
#endif
			break;
		}
	}
#ifdef SMEWS_ENDING
	SMEWS_ENDING;
#endif
	return 1;
}
