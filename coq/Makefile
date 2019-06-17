all: Helpers.v Packet.v TFTP.v Extraction.v
	coqc Helpers.v
	coqc Packet.v
	coqc TFTP.v
	coqc Extraction.v

clean:
	rm -f *.o *.vo *.glob .*.aux
	rm -f *.ml *.mli
