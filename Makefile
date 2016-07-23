.PHONY: clean

all: sketch.vo

sketch.vo: Word.vo sketch.v ContractSem.vo
	coqc sketch.v

ContractSem.vo: Word.vo ContractSem.v
	coqc ContractSem.v

Word.vo: Word.v
	coqc Word.v

clean:
	rm -rf *.vo
