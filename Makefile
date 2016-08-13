.PHONY: clean

all: sketch.vo AbstractExamples.vo


sketch.vo: Word.vo sketch.v ContractSem.vo
	coqc sketch.v


AbstractExamples.vo: Word.vo AbstractExamples.v ContractSem.vo
	coqc AbstractExamples.v

ContractSem.vo: Word.vo ContractSem.v
	coqc ContractSem.v

Word.vo: Word.v
	coqc Word.v

clean:
	rm -rf *.vo *.glob
