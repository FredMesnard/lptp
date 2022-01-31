
	
mgu__term1(N,[f|T]) :-
	mgu__term1(N,[var(x(0))],T).

mgu__term1(0,T,T).
mgu__term1(N1,T1,T2) :-
	0 < N1, N2 is N1 - 1,
	mgu__term1(N2,[var(x(N2)),var(y(N2))|T1],T2).

mgu__term2(N,[f|T]) :-
	mgu__term2(N,[var(y(0))],T).

mgu__term2(0,T,T).
mgu__term2(N1,T1,T2) :-
	0 < N1, N2 is N1 - 1,
	mgu__term2(N2,[[f,var(x(N1)),var(x(N1))],[f,var(y(N1)),var(y(N1))]|T1],T2).

a(N) :-
	mgu__term1(N,T1),
	mgu__term2(N,T2),
	X1 is cputime,
	mgu(T1,T2,_),
	X2 is cputime,
	Z is X2 - X1, write(N:Z), nl.
	
test :- not b(0).

b(N) :- a(N), fail.
b(N) :- M is N + 1, b(M).


	
