member(X,[X|_]).
member(X,[_|L]) :- member(X,L).

append([],L,L).
append([X|L1],L2,[X|L3]) :- append(L1,L2,L3).

a.
a :- b1, b2, b3.
a :- c1.
a :- d1, d2.

list([]).
list([_|L]) :- list(L).

notsubset(L1,L2) :- member(X,L1), not member(X,L2).

subset(L1,L2) :- not notsubset(L1,L2).
