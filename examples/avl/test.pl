%********************************************************************************
% (1) Specification of AVL trees
%********************************************************************************
% AVL trees are subject to the Adelson-Velskii-Landis balance criterion:
%   
% 	A tree is balanced iff for every node the heights of its
% 	two subtrees differ by at most 1.
% 
% The empty tree is represented as t.
% A tree with value V, left subtree L and right subtree R is
% represented as t(V,X,L,R). 
% X is the difference of the height of R and the height of L.
% X can be -1, 0 or 1.
%
% See: Niklaus Wirth, "Algorithmen und Datenstrukturen", 5.4


% The trees are ordered with respect to a total ordering r/2 on a domain a/1.
%
% Example:

a(X) :- integer(X).
r(X,Y) :- X =< Y.

% avl(T) means: T is a AVL tree.

avl(T) :- ordered(T), balanced(T,_).

% balanced(T,N) means: T is balanced and has height N.

balanced(t,0).
balanced(t(_,X,T1,T2),N) :-
	balanced(T1,N1),
	balanced(T2,N2),
	diff(N1,N2,X,N).

diff(N,N,0,s(N)).
diff(N,s(N),1,s(s(N))).
diff(s(N),N,-1,s(s(N))).

% ordered(T) means: T is an ordered tree.

ordered(t).
ordered(t(V,_,T1,T2)) :-
	a(V),
	ordered(T1),
	ordered(T2),
	upper_bound(T1,V),
	lower_bound(T2,V).

% upper_bound(T,V) means: V is an upper bound of the elements of T.

upper_bound(t,_).
upper_bound(t(U,_,T1,T2),V) :-
	r(U,V),
	upper_bound(T1,V),
	upper_bound(T2,V).

% lower_bound(T,V) means: V is a lower bound of the elements of T.

lower_bound(t,_).
lower_bound(t(U,_,T1,T2),V) :-
	r(V,U),
	lower_bound(T1,V),
	lower_bound(T2,V).

% in(V,T) means: V is an element of the tree T.

in(V,t(V,_,_,_)).
in(V,t(_,_,T,_)) :- in(V,T).
in(V,t(_,_,_,T)) :- in(V,T).


%********************************************************************************
% (2) Implementation (following Wirth)
%********************************************************************************

% addavl(V,T1,T2) means: Insert element V into the AVL tree T1. Result is T2.

addavl(V,T1,T2) :- insert(V,T1,T2,_).

% insert(V,T1,T2,stable) means: The result of inserting V in T1 is T2.
% The heigth of T1 is equal to the height of T2.

% insert(V,T1,T2,grows) means: The result of inserting V in T1 is T2.
% The height of T2 grows by 1.

insert(U,t,t(U,0,t,t),grows).
insert(U,t(V,B,T1,T2),T,G) :-
	(	r(U,V) ->
		insert(U,T1,T3,G1),
		(	G1 = stable ->
			T = t(V,B,T3,T2),
			G = stable
		;	left_combine(B,T3,V,T2,T,G)
		)
	;	insert(U,T2,T3,G1),
		(	G1 = stable ->
			T = t(V,B,T1,T3),
			G = stable
		;	right_combine(B,T1,V,T3,T,G)
		)
	).

left_combine(1,T1,V,T2,t(V,0,T1,T2),stable).
left_combine(0,T1,V,T2,t(V,-1,T1,T2),grows).
left_combine(-1,t(U,-1,S1,S2),V,T2,
	t(U,0,S1,t(V,0,S2,T2)),stable).
left_combine(-1,t(U,1,S1,t(W,B,S2,S3)),V,T2,
	t(W,0,t(U,B1,S1,S2),t(V,B2,S3,T2)),stable) :- flip(B,B1,B2).

right_combine(-1,T1,V,T2,t(V,0,T1,T2),stable).
right_combine(0,T1,V,T2,t(V,1,T1,T2),grows).
right_combine(1,T1,V,t(U,1,S1,S2),
	t(U,0,t(V,0,T1,S1),S2),stable).
right_combine(1,T1,V,t(U,-1,t(W,B,S1,S2),S3),
	t(W,0,t(V,B1,T1,S1),t(U,B2,S2,S3)),stable) :- flip(B,B1,B2).

flip(1,-1,0).
flip(0,0,0).
flip(-1,0,1).

%********************************************************************************
% (3) Tests an debugging
%********************************************************************************

% write_tree(T) means: print tree T on the screen. You have to turn the head
% to the left.

write_tree(T) :- write_tree(T,[]).

write_tree(t,_).

write_tree(t(U,B,T1,T2),L1) :-
	left(L1,L2),
	right(L1,L3),
	write_tree(T2,[/|L2]),
	write_index(L1),
	write(=), write(U), write(:), write(B), nl,
	write_tree(T1,[\|L3]).	

left([],[' ']).
left([/|L],[' ',' '|L]).
left([\|L],[' ',\|L]).

right([],[' ']).
right([/|L],[' ',/|L]).
right([\|L],[' ',' '|L]).

write_index([]).
write_index([X|L]) :-
	write_index(L),
	write(X).

% test([N1,N2,...,Nk],T) means: Generate tree T with nodes N1,N2,...,Nk.

test(L,T) :-
	gen(L,t,T),
	(	avl(T) ->
		true
	;	write('! Error: '),
		write(T), 
		write(' is not an AVL tree.'), nl
	).

test(L) :-
	test(L,T),
	write_tree(T).

% test1(L) means: Generate all possible permutations L1 of L and perform test(L1).

test1(L) :-
	perm(L,L1),
	nl, write(L1), nl,
	test(L1),
	fail.

test2(L) :-
	perm(L,L1),
	test(L1,_),
	fail.

gen([],T,T).
gen([V|L],T1,T3) :-
	addavl(V,T1,T2),
	gen(L,T2,T3).

delete(X,[X|L],L).
delete(X,[Y|L1],[Y|L2]) :- delete(X,L1,L2).

perm([],[]).
perm(L1,[X|L3]) :-
	delete(X,L1,L2),
	perm(L2,L3).

% avl.pl ends here
