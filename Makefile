all: sketch.vo

sketch.vo: Word.vo sketch.v
	coqc sketch.v

Word.vo: Word.v
	coqc Word.v
