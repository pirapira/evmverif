.PHONY: clean

all: sketch.vo AbstractExamples.vo example/call_but_fail_on_reentrance.vo


sketch.vo: Word.vo sketch.v ContractSem.vo ConcreteWord.vo
	coqc sketch.v

example/call_but_fail_on_reentrance.vo: example/call_but_fail_on_reentrance.v ContractSem.vo Word.vo ConcreteWord.vo
	coqc example/call_but_fail_on_reentrance.v

ConcreteWord.vo: ConcreteWord.v Word.vo
	coqc ConcreteWord.v

AbstractExamples.vo: Word.vo AbstractExamples.v ContractSem.vo
	coqc AbstractExamples.v

ContractSem.vo: Word.vo ContractSem.v
	coqc ContractSem.v

Word.vo: Word.v
	coqc Word.v

clean:
	rm -rf *.vo *.glob
	rm -rf example/*.vo example/*.glob
