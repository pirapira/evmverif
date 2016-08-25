.PHONY: all clean

all: sketch.vo example/AbstractExamples.vo example/call_but_fail_on_reentrance.vo example/managed_account_with_accumulators.vo

sketch.vo: Word.vo sketch.v ContractSem.vo ConcreteWord.vo
	coqc sketch.v

example/call_but_fail_on_reentrance.vo: example/call_but_fail_on_reentrance.v ContractSem.vo Word.vo ConcreteWord.vo
	coqc example/call_but_fail_on_reentrance.v

example/managed_account_with_accumulators.vo: example/managed_account_with_accumulators.v ContractSem.vo Word.vo ConcreteWord.vo
	coqc example/managed_account_with_accumulators.v

ConcreteWord.vo: ConcreteWord.v Word.vo
	coqc ConcreteWord.v

example/AbstractExamples.vo: Word.vo example/AbstractExamples.v ContractSem.vo
	coqc example/AbstractExamples.v

ContractSem.vo: Word.vo ContractSem.v
	coqc ContractSem.v

Word.vo: Word.v
	coqc Word.v

clean:
	rm -rf *.vo *.glob
	rm -rf example/*.vo example/*.glob
