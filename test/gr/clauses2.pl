member(X,[X|_]).
member(X,[_|L]) :- member(X,L).

member_check(X,[Y|L]) :-
	(X = Y -> true; member_check(X,L)).
