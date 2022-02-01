permutation([],[]).
permutation(L1,[X|L3]) :-
	delete(X,L1,L2),
	permutation(L2,L3).

same_occ(L1,L2) :- not not_same_occ(L1,L2).

not_same_occ(L1,L2) :-
	member2(X,L1,L2),
	occ(X,L1,N1),
	occ(X,L2,N2),
	not(N1 = N2).

occ(X,[],0).
occ(X,[X|L],s(N)) :- occ(X,L,N).
occ(X,[Y|L],N) :- not(X = Y), occ(X,L,N).

member2(X,L1,L2) :- member(X,L1).
member2(X,L1,L2) :- member(X,L2).
