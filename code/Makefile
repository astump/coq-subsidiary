all: clean Makefile.coq
	+make -f Makefile.coq all

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject: ;

Makefile: ;

clean:
	@rm -f *.vo   &
	@rm -f *.glob &
	@rm -f .*.aux  &
	@rm -f *.vok  &
	@rm -f *.vos &
	@rm -f Makefile.coq &
	@rm -f Makefile.coq.conf &
	@rm -f .Makefile.coq.d &
	@rm -f CoqMakefile.conf &
	@rm -f .CoqMakefile.d &
