/* Builds the SBR and PS Huffman tables as FFmpeg n8.1's init_sbr_tables
 * (libavcodec/aac/aacdec_tab.c) and ff_ps_init_common (libavcodec/aacps_common.c) do, with
 * FFmpeg's own libavcodec/vlc.c, and prints them, one line per table:
 *   T <sbr|ps> <k> <entries> <bytes in hex...>
 * Compiled by gen.py against an FFmpeg source tree given on the command line (nothing of
 * FFmpeg is copied here). `sbr_data.inc` is the block of SBR table definitions that gen.py
 * cuts out of aacdec_tab.c. */
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include "libavcodec/vlc.c"
#include "libavutil/reverse.c"

void av_log(void *avcl, int level, const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vfprintf(stderr, fmt, ap);
  va_end(ap);
}
void avpriv_request_sample(void *avc, const char *msg, ...) {
  fprintf(stderr, "request_sample: %s\n", msg);
  exit(2);
}
void *av_malloc(size_t n) { return malloc(n ? n : 1); }
void *av_mallocz(size_t n) { return calloc(1, n ? n : 1); }
void *av_malloc_array(size_t a, size_t b) { return malloc(a * b ? a * b : 1); }
void av_free(void *p) { free(p); }
void av_freep(void *p) {
  void **q = p;
  free(*q);
  *q = NULL;
}
void *av_realloc_f(void *p, size_t a, size_t b) {
  void *r = realloc(p, a * b ? a * b : 1);
  if (!r) free(p);
  return r;
}

#include "sbr_data.inc"
#include "libavcodec/aacpsdata.c"

static void dump(const char *set, int k, const VLCElem *t, unsigned n) {
  printf("T %s %d %u", set, k, n);
  const unsigned char *b = (const unsigned char *)t;
  for (unsigned i = 0; i < 4 * n; i++) printf(" %02x", b[i]);
  printf("\n");
}

int main(void) {
  {
    /* init_sbr_tables */
    static VLCElem vlc_buf[(1098 + 1092 + 768 + 1026 + 1058 + 1052 + 544 + 544 + 592 + 512)];
    VLCInitState state = VLC_INIT_STATE(vlc_buf);
    const uint8_t (*tab)[2] = sbr_huffman_tab;
    for (int i = 0; i < 10; i++) {
      VLCElem *before = state.table;
      const VLCElem *t = ff_vlc_init_tables_from_lengths(&state, 9, sbr_huffman_nb_codes[i],
          &tab[0][1], 2, &tab[0][0], 2, 1, sbr_vlc_offsets[i], 0);
      if (t != before) return 1;
      dump("sbr", i, t, (unsigned)(state.table - before));
      tab += sbr_huffman_nb_codes[i];
    }
    if (state.size != 0) return 1;
  }
  {
    /* ff_ps_init_common */
    static VLCElem vlc_buf[(1544 + 832 + 1024 + 1036) + (544 + 544) + (32 + 32 + 32 + 32)];
    VLCInitState state = VLC_INIT_STATE(vlc_buf);
    const uint8_t (*tab)[2] = aacps_huff_tabs;
    for (int i = 0; i < 10; i++) {
      VLCElem *before = state.table;
      const VLCElem *t = ff_vlc_init_tables_from_lengths(&state, i <= 5 ? 9 : 5, huff_sizes[i],
          &tab[0][1], 2, &tab[0][0], 2, 1, huff_offset[i], 0);
      if (t != before) return 1;
      dump("ps", i, t, (unsigned)(state.table - before));
      tab += huff_sizes[i];
    }
    if (state.size != 0) return 1;
  }
  return 0;
}
