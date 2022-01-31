arithmetic(X) :-
	integer(X).
arithmetic(X + Y) :-
	arithmetic(X),
	arithmetic(Y).
arithmetic(X - Y) :-
	arithmetic(X),
	arithmetic(Y).
arithmetic(X * Y) :-
	arithmetic(X),
	arithmetic(Y).
arithmetic(X / Y) :-
	arithmetic(X),
	arithmetic(Y).
arithmetic(- X) :-
	arithmetic(X).

numeric(X) :-
	number(X).
numeric(X + Y) :-
	numeric(X),
	numeric(Y).
numeric(X - Y) :-
	numeric(X),
	numeric(Y).
numeric(X * Y) :-
	numeric(X),
	numeric(Y).
numeric(X / Y) :-
	numeric(X),
	numeric(Y).
numeric(- X) :-
	numeric(X).



