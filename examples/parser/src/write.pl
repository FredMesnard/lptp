/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 6/23/95, 12:43 PM */
/* Filename: write.pl */
/* Abstract: The predicate un_parse/2 transforms a parse tree into a list
   of tokens in such a way that the predicate parse/2 of ``read.pl'' transforms
   the token list back into the same parse tree. The predicates symbol_op/1,
   prefix_op/1, infix_op/1, postfix_op/1, prefix_prec/3, infixprec/4,
   postfix_prec/4 are definedn in ``read.pl''.*/


un_parse(T,L) :- un_parse(T,1200,[],L).

un_parse(variable(X),_,L,[variable(X)|L]).
un_parse(integer(X),_,L,[integer(X)|L]).
un_parse(float_number(X),_,L,[float_number(X)|L]).
un_parse(char_code_list(X),_,L,[char_code_list(X)|L]).
un_parse(con(X),_,L1,L2) :-
	(	X = [] ->
		L2 = [open_list,close_list|L1]
	;	X = '{}' ->
		L2 = [open_curly,close_curly|L1]
	;	symbol_op(X) -> 
		L2 = [open(nolayout),name(X),close|L1]
	;	L2 = [name(X)|L1]
	).
un_parse(fun(X,[T1|Ts]),N1,L1,L5) :-
	(	Ts = [],
		prefix_op(X),
		\+ X = (-) ->
		prefix_prec(X,N2,N3),
		close_par(N1,N2,L1,L2),
		un_parse(T1,N3,L2,L3),
		add_layout(L3,L4),
		open_par(N1,N2,[name(X)|L4],L5)
	;	singleton(Ts),
		infix_op(X) ->
		infix_prec(X,N2,N3,N4),
		Ts = [T2],
		close_par(N1,N2,L1,L2),
		un_parse(T2,N4,L2,L3),
		(	X = ',' -> 
			Y = comma
		; 	Y = name(X)
		),
		un_parse(T1,N3,[Y|L3],L4),
		open_par(N1,N2,L4,L5)
	;	Ts = [],
		postfix_op(X) ->
		postfix_prec(X,N2,N3),
		close_par(N1,N2,L1,L2),
		un_parse(T1,N3,[name(X)|L2],L3),
		open_par(N1,N2,L3,L5)
	;	singleton(Ts),
		X = '.' ->
		Ts = [T2],
		un_list_tail(T2,L1,L2),
		un_one_arg(T1,L2,L3),
		L5 = [open_list|L3]
	; 	Ts = [],
		X = '{}' ->
		un_parse(T1,1200,[close_curly|L1],L2),
		L5 = [open_curly|L2]
	;	un_arg_seq(Ts,L1,L2),
		un_one_arg(T1,L2,L3),
		L5 = [name(X),open(nolayout)|L3]
	).


singleton([_]).


un_one_arg(T,L1,L2) :-
	(	con_tree(T) ->
		T = con(X),
		L2 = [name(X)|L1]
	; 	un_parse(T,999,L1,L2)
	).


con_tree(con(_)).


un_arg_seq([],L,[close|L]).
un_arg_seq([T|A],L1,[comma|L3]) :-
	un_arg_seq(A,L1,L2),
	un_one_arg(T,L2,L3).
	

un_list_tail(T,L1,L4) :-
	(	T = con([]) ->
		L4 = [close_list|L1]
	;	list_tree(T) ->
		T = fun('.',[T1,T2]),
		un_list_tail(T2,L1,L2),
		un_one_arg(T1,L2,L3),
		L4 = [comma|L3]
	;	un_one_arg(T,[close_list|L1],L2),
		L4 = [head_tail_sep|L2]
	).


list_tree(fun('.',[_,_])).


open_par(M,N,L1,L2) :-
	(	M < N -> 
		L2 = [open(nolayout)|L1]
	; 	L2 = L1
	).


close_par(M,N,L1,L2) :-
	(	M < N -> 
		L2 = [close|L1]
	; 	L2 = L1
	).


add_layout([X|L1],L2) :-
	(	X = open(nolayout) ->
		L2 = [open(layout)|L1]
	;	L2 = [X|L1]
	).

% End of write.pl
