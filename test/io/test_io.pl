:- dynamic r/1.
r(0).

test_io :-
	thm_file($(test)/io/f1),
	io__tell(thm), write(':- '),
	write(assert(r(1))),
	write('.'), nl,
	io__close(thm),
	thm_file($(test)/io/f2),
	io__tell(thm),
	write(':- '),
	write(assert(r(2))),
	write('.'), nl,
	io__close(thm),
	needs_thm($(test)/io/f1),
	needs_thm($(test)/io/f2),
	assert(r(3)),
	bagof(X,r(X),L), L = [0,1,2,3],
	write('*** test_io o.k.'), nl.

:- initialization(test_io).
