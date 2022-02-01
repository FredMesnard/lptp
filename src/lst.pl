/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: Fri Dec  2 15:53:24 1994 */
/* Filename: lst.pl */
/* Abstract: List processing predicates. */

%%d lst__member(any,any)

lst__member(X,[X|_]).
lst__member(X,[_|L]) :- lst__member(X,L).

%%d lst__member_check(any,any)

lst__member_check(X,[Y|L]) :-
	(	X = Y ->
		true
	;	lst__member_check(X,L)
	).

%%d lst__concat(any,any,any)

lst__concat(L1,L2,L3) :-
	(	L2 = [] ->
		L3 = L1
	;	lst__append(L1,L2,L3)
	).

%%d lst__append(any,any,any)

lst__append([],L,L).
lst__append([X|L1],L2,[X|L3]) :- lst__append(L1,L2,L3).

%%d lst__append_set(grL::in,grL::in,grL::out)

lst__append_set([],L,L).
lst__append_set([X|L1],L2,L4) :-
	lst__append_set(L1,L2,L3),
	lst__add_element(X,L3,L4).

%%d lst__add_element(gr::in,grL::in,grL::out)

lst__add_element(X,L1,L2) :- 
	(	lst__member_check(X,L1) -> 
		L2 = L1
	; 	L2 = [X|L1]
	).

%%d lst__delete(any,any,any)

lst__delete(X,[X|L],L).
lst__delete(X,[Y|L1],[Y|L2]) :-
	lst__delete(X,L1,L2).

%%d lst__permutation(any,any)

lst__permutation([],[]).
lst__permutation(L1,[X|L3]) :-
	lst__delete(X,L1,L2),
	lst__permutation(L2,L3).

%%d lst__singleton(gr::in)

lst__singleton([_]).

%%d lst__two_elements(gr::in)

lst__two_elements([_,_]).

%%d lst__subset(grL::in,grL::in)

lst__subset(L1,L2) :- \+ lst__not_subset(L1,L2).

%%d lst__not_subset(grL::in,grL::in)

lst__not_subset(L1,L2) :-
	lst__member(X,L1),
	\+ lst__member(X,L2).

%%d lst__reverse(any,any)

lst__reverse(L1,L2) :-
	lst__reverse(L1,[],L2).

%%d lst__reverse(any,any,any)

lst__reverse([],L,L).
lst__reverse([X|L1],L2,L3) :- lst__reverse(L1,[X|L2],L3).

%%d lst__disjoint(grL::in,grL::in)

lst__disjoint(L1,L2) :-
	\+ lst__not_disjoint(L1,L2).

%%d lst__not_disjoint(grL::in,grL::in)

lst__not_disjoint(L1,L2) :-
	lst__member(X,L1), lst__member(X,L2).

%%d lst__list_form(gr::in)

lst__list_form([]).
lst__list_form([_|_]).

%%d lst__set_minus(grL::in,grL::in,grL::out)

lst__set_minus([],_,[]).
lst__set_minus([X|L1],L2,L4) :-
	(	lst__member_check(X,L2) ->
		L4 = L3
	;	L4 = [X|L3]
	),
	lst__set_minus(L1,L2,L3).

%%d lst__member_con(any,any)

lst__member_con(X,[[&|L]|_]) :- lst__member(X,L).
lst__member_con(X,[X|_]).
lst__member_con(X,[_|L]) :- lst__member_con(X,L).

%%d lst__member_con_check(any,any)

lst__member_con_check(X,[Y|L1]) :-
	(	X = Y ->
		true
	;	Y = [&|L2],
		lst__member_check(X,L2) ->
		true
	;	lst__member_con_check(X,L1)
	).

%%d lst__delete_con(any,any,any)

lst__delete_con(X,[X|L],L).
lst__delete_con(X,[[&|M1]|L],[[&|M2]|L]) :-
	lst__delete(X,M1,M2).
lst__delete_con(X,[Y|L1],[Y|L2]) :-
	lst__delete_con(X,L1,L2).

% lst.pl ends here

