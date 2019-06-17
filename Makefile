all: extract server


.PHONY: extract
.PHONY: server

extract:
	$(MAKE) -C coq

server:
	ocamlbuild -r -I coq -pkg unix -tag thread main.byte

%.vo: %.v
	coqc $<

clean:
	rm -f *.o *.cmi *.cmo *.cmx *.vo
	rm -rf _build main.byte
	$(MAKE) -C coq clean
