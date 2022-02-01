int(X) :- nat(X).
int(-s(X)) :- nat(X).

negative(-s(X)).

minus(X,Y,Z) :-
	plus(Y,Z,X),
	\+ negative(Z).
minus(X,Y,-s(Z)) :- 
	plus(X,s(Z),Y).

minus(s(X),-s(X)).
minus(0,0).
minus(-X,X).
