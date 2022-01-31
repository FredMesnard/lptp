PROOFS = axioms.pr \
	ordered.pr \
	set.pr \
	termination.pr \
	balanced.pr \
	existence.pr \
	avl.pr	

SOURCES = avl.pl

html: $(PROOFS) $(SOURCES)
	/bin/rm -rf html
	mkdir html
	../../etc/pl2html.perl -o html $(SOURCES)
	../../etc/pr2html.perl -o html $(PROOFS)
