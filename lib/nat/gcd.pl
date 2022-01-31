gcd(X,Y,D) :-
	(	X @=< Y ->
		gcd_leq(X,Y,D)
	;	gcd_leq(Y,X,D)
	).

gcd_leq(X,Y,D) :-
	(	X = 0 ->
		D = Y
	;	plus(X,Z,Y),
		gcd(X,Z,D)
	).
