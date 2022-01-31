% The following examples are from:
%
%	AUTHOR = {Peter Ru\v{z}i\v{c}ka and Igor Pr\'{\i}vara},
%	TITLE = {An Almost Linear Robinson Unification Algorithm},
%	JOURNAL = {Acta Informatica},
%	YEAR = {1989},
%	VOLUME = {27},
%	PAGES = {61--71}

% Create the terms for the unification problems.

uni_f1(0,A,[n(A,0)]).
uni_f1(N,A,[n(f,2),T,var(x(N))]) :-
	0 < N, M is N - 1,
	uni_f1(M,A,T).

uni_f2(0,A,[n(A,0)]).
uni_f2(N,A,[n(f,2),var(x(N)),T]) :-
	0 < N, M is N - 1,
	uni_f2(M,A,T).

uni_g_unary(1,X,[n(g,1),var(X)]).
uni_g_unary(N,X,[n(g,1),T]) :-
	1 < N, M is N - 1,
	uni_g_unary(M,X,T).

uni_g_binary(1,X,[n(g,1),var(X),var(X)]).
uni_g_binary(N,X,[n(g,1),var(X),T]) :-
	1 < N, M is N - 1,
	uni_g_binary(M,X,T).
	
uni_term1(1,N,T) :- uni_f1(N,a,T).
uni_term2(1,N,T) :- uni_f2(N,a,T).
	
uni_term1(2,N,[n(f,2),var(z),T]) :-
	uni_g_unary(N,x,T).
uni_term2(2,N,[n(f,2),[n(g,1),var(z)],T]) :-
	uni_g_unary(N,y,T).

uni_term1(3,N,[n(f,3),var(x),T,var(x)]) :-
	uni_g_binary(N,x,T).
uni_term2(3,N,[n(f,3),T,var(y),var(y)]) :-
	uni_g_binary(N,y,T).

uni_term1(4,N,T) :- uni_f1(N,a,T).
uni_term2(4,N,T) :- uni_f2(N,b,T).

uni_term1(5,N,[n(f,3),var(x),T,var(x)]) :-
	uni_g_unary(N,x,T).
uni_term2(5,N,[n(f,3),T,var(y),var(y)]) :-
	uni_g_unary(N,y,T).

uni_term1(6,N,T) :- uni_g_unary(N,x,T).
uni_term2(6,N,T) :- uni_g_unary(N,y,T).

uni_term1(7,N,[n(f,2),T,var(z)]) :-
	uni_f1(N,a,T).
uni_term2(7,N,[n(f,2),T,[n(g,1),var(z)]]) :-
	uni_f2(N,a,T).

uni_term1(8,N,[f|T]) :-
	mgu__term1(N,[var(x(0))],T).

uni_term2(8,N,[f|T]) :-
	mgu__term2(N,[var(y(0))],T).

mgu__term1(0,T,T).
mgu__term1(N1,T1,T2) :-
	0 < N1, N2 is N1 - 1,
	mgu__term1(N2,[var(x(N2)),var(y(N2))|T1],T2).

mgu__term2(0,T,T).
mgu__term2(N1,T1,T2) :-
	0 < N1, N2 is N1 - 1,
	mgu__term2(N2,[[f,var(x(N1)),var(x(N1))],[f,var(y(N1)),var(y(N1))]|T1],T2).


% Create the unification problems.

uni_problem(K,N) :-
	uni_term1(K,N,T1),
	uni_term2(K,N,T2),
	X is cputime,
	(mgu(T1,T2,_) -> true; true),
	Y is cputime,
	Z is Y - X,
	write(p(K,N):Z), nl.
	
% Run the unification problems.

test(N) :- not uni_loop(N,1).

uni_loop(N,M) :- 
	uni_problem(N,M), fail.
uni_loop(N,M) :- 
	K is M + 1, uni_loop(N,K).

% p(K,N) :-
% 	uni_term1(K,N,T1),
% 	uni_term2(K,N,T2),
% 	(mgu__sub(T1,T2,S) -> i2e__sub_L(S,X); X = no),
% 	write(X), nl.

% l(K,N) :- uni_term1(K,N,T), i2e__expression(T,X), write(X), nl.
% r(K,N) :- uni_term2(K,N,T), i2e__expression(T,X), write(X), nl.
