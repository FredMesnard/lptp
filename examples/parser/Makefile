PROOFS = pr/parser.pr \
	pr/axioms.pr \
	pr/precedence.pr \
	pr/grammar.pr \
	pr/soundness.pr \
	pr/completeness.pr \
	pr/uniqueness.pr \
	pr/termination.pr \
	pr/write.pr	

SOURCES = pr/axioms.pl \
	src/grammar.pl \
	src/read.pl \
	src/write.pl

html: $(PROOFS) $(SOURCES)
	/bin/rm -rf html
	mkdir html
	../../etc/pl2html.perl -o html $(SOURCES)
	../../etc/pr2html.perl -o html $(PROOFS)
