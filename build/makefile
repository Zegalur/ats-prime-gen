
OUT = prog
CC = patscc
BDIR = ../bin
ODIR = ../obj
SDIR = ../src
CFLAGS = #-O2

_OBJS = main_dats.o isqrt_dats.o prime_dats.o \
        divmod_dats.o mul_dats.o
OBJS = $(patsubst %,$(ODIR)/%,$(_OBJS))

SATSS := $(shell find $(SDIR) -name '*.sats')



$(BDIR)/$(OUT): $(OBJS)
	$(CC) -o $@ $(OBJS)

$(ODIR)/%_dats.o: $(SDIR)/%.dats $(SATSS)
	$(CC) $(CFLAGS) -IIATS $(SDIR) -IIATS $(ODIR) -o $@ -c $< -cleanaft



.PHONY: clean

clean:
	rm -f $(ODIR)/*.* $(BDIR)/$(OUT) *.c
