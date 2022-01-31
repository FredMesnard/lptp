#   Author: Robert F. Staerk <robert.staerk@unifr.ch> 
#  Created: Tue Nov  5 17:45:28 1996 
# Updated: Wed Jul 21 14:55:05 1999
# Abstract: Create the HTML library

# The variables LIBPR and SORTPR contain all `.pr' files of the library.
LIBPR =		nat/nat.pr \
		nat/ackermann.pr \
		nat/gcd.pr \
		nat/int.pr \
		list/list.pr \
		list/permutation.pr \
		list/reverse.pr \
		list/suffix.pr \
		graph/transitiveclosure.pr

SORTPR =	sort/sort.pr \
		sort/mergesort.pr \
		builtin/integeraxioms.pr \
		builtin/callsort.pr \
		builtin/callsortexample.pr \
		builtin/bubble.pr


# The variables LIBPL and SORTPL contain all `.pl' files of the library.
LIBPL =	nat/nat.pl \
		nat/ackermann.pl \
		nat/gcd.pl \
		nat/int.pl \
		list/list.pl \
		list/permutation.pl \
		list/reverse.pl \
		list/suffix.pl \
		graph/transitiveclosure.pl

SORTPL = 	sort/sort.pl \
		sort/mergesort.pl \
		builtin/callsort.pl \
		builtin/bubble.pl


# Create the HTML version of the library.
html: $(LIBPR) $(SORTPR) $(LIBPL) $(SORTPL)
	/bin/rm -rf html
	mkdir html
	../etc/pl2html.perl -o html $(LIBPL) $(SORTPL)
	../etc/pr2html.perl -o html $(LIBPR) $(SORTPR)

wc: $(LIBPR) $(SORTPR) $(LIBPL) $(SORTPL)
	wc $(LIBPL)
	wc $(LIBPR)
	wc $(SORTPL)
	wc $(SORTPR)

clean:
	/bin/rm -rf html TAGS *~

tags:
	../etc/lptp-tags $(LIBPR) $(SORTPR)
