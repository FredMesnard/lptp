/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 6/23/95, 12:37 PM */
/* Filename: read.pl */
/* Abstract: A verified parser for ISO standard Prolog (cf. grammar.pl). The
main predicates of this file is the predicate parse/2. It takes a list of
tokens that ends with the ``end'' token and transforms it into a parse tree.
The definition of tokens and parse trees are in the file ``grammar.pl''. If
there is a syntax error, then instead of a parse tree an error is
returned. The error contains the list of remaining tokens together with a
message. */


infix_op(X) :- current_op(_,xfx,X).
infix_op(X) :- current_op(_,xfy,X).
infix_op(X) :- current_op(_,yfx,X).


infix_prec(X,N1,N2,N2) :-
	current_op(N1,xfx,X),
	N2 is N1 - 1.
infix_prec(X,N1,N2,N1) :-
	current_op(N1,xfy,X),
	N2 is N1 - 1.
infix_prec(X,N1,N1,N2) :-
	current_op(N1,yfx,X),
	N2 is N1 - 1.


prefix_op(X) :- current_op(_,fx,X).
prefix_op(X) :- current_op(_,fy,X).


prefix_prec(X,N1,N2) :-
	current_op(N1,fx,X),
	N2 is N1 - 1.
prefix_prec(X,N,N) :-
	current_op(N,fy,X).


postfix_op(X) :- current_op(_,xf,X).
postfix_op(X) :- current_op(_,yf,X).


postfix_prec(X,N1,N2) :-
	current_op(N1,xf,X),
	N2 is N1 - 1.
postfix_prec(X,N,N) :-
	current_op(N,yf,X).


symbol_op(X) :- 
	current_op(_,_,X),
	\+ (X = ',').

parse(L,T) :- 
	term(L,1200,L1,T1),
	(	L1 = [end] ->
		T = T1
	;	error(L1) ->
		T = L1
	; 	T = error(parse/L)
	).


error(error(_)).


term([variable(X)|L1],N,L2,T) :-
	more(L1,0,N,variable(X),L2,T).
term([integer(X)|L1],N,L2,T) :-
	more(L1,0,N,integer(X),L2,T).
term([float_number(X)|L1],N,L2,T) :-
	more(L1,0,N,float_number(X),L2,T).
term([char_code_list(X)|L1],N,L2,T) :-
	more(L1,0,N,char_code_list(X),L2,T).
term([name(X),Y|L1],N1,L4,T2) :-
	(	Y = open(nolayout) ->
		one_arg(L1,L2,T1),
		arg_seq(L2,L3,Ts),
		more(L3,0,N1,fun(X,[T1|Ts]),L4,T2)
	;	prefix_op(X) ->
		(	X = (-),
			number_token(Y) ->
			minus_number_tree(Y,T1),
			more(L1,0,N1,T1,L4,T2)
		;	prefix_prec(X,N2,N3),
			(	N2 =< N1 ->
				term([Y|L1],N3,L2,T1),
				more(L2,N2,N1,fun(X,[T1]),L4,T2)
			;	L4 = error(prefix_prec/[name(X),Y|L1]),
				T2 = error
			)
		)
	;	(	symbol_op(X) -> 
			L4 = error(operator/[name(X),Y|L1]),
			T2 = error
		; 	more([Y|L1],0,N1,con(X),L4,T2)
		)
	).
term([open_list,Y|L1],N,L4,T3) :-
	(	Y = close_list -> 
		more(L1,0,N,con([]),L4,T3)
	;	one_arg([Y|L1],L2,T1),
		list_tail(L2,L3,T2),
		more(L3,0,N,fun('.',[T1,T2]),L4,T3)
	).
term([open(_),X,Y|L1],N,L4,T2) :-
	( 	name_token(X),
		Y = close ->
		X = name(Z),
		more(L1,0,N,con(Z),L4,T2)
	;	term([X,Y|L1],1200,L2,T1),
		expect(L2,close,L3),
		more(L3,0,N,T1,L4,T2)
	).
term([open_curly,Y|L1],N,L4,T2) :-
	(	Y = close_curly ->
		more(L1,0,N,con('{}'),L4,T2)
	;	term([Y|L1],1200,L2,T1),
		expect(L2,close_curly,L3),
		more(L3,0,N,fun('{}',[T1]),L4,T2)
	).
term(error(X),_,error(X),error).
term(L,_,error(term_begin/L),error) :-
	\+ term_begin(L).


term_begin([variable(_)|_]).
term_begin([integer(_)|_]).
term_begin([float_number(_)|_]).
term_begin([char_code_list(_)|_]).
term_begin([name(_),_|_]).
term_begin([open(_),_,_|_]).
term_begin([open_list,_|_]).
term_begin([open_curly,_|_]).
term_begin(error(_)).


name_token(name(_)).


number_token(integer(_)).
number_token(float_number(_)).


minus_number_tree(integer(X),integer(Y)) :- 
	Y is -(X).
minus_number_tree(float_number(X),float_number(Y)) :- 
	Y is -(X).


expect([Y|L1],X,L2) :-
	(	X = Y -> 
		L2 = L1
	;	L2 = error(expect(X)/[Y|L1])
	).
expect([],X,error(expect(X)/[])).
expect(error(X),_,error(X)).


sep_token(comma).
sep_token(close).
sep_token(head_tail_sep).
sep_token(close_list).


one_arg([X,Y|L1],L2,T) :-
	( 	name_token(X),
		sep_token(Y) ->
		X = name(Z),
		L2 = [Y|L1], 
		T = con(Z)
	; 	term([X,Y|L1],999,L2,T)
	).
one_arg([X],error(arg/[X]),error).
one_arg([],error(arg/[]),error).
one_arg(error(X),error(X),error).
	

arg_seq([X|L1],L3,Ts2) :-
	(	X = close ->
		L3 = L1, 
		Ts2 = []
	;	X = comma ->
		one_arg(L1,L2,T),
		arg_seq(L2,L3,Ts1),
		Ts2 = [T|Ts1]
	;	L3 = error(arg_seq/[X|L1]),
		Ts2 = error
	).
arg_seq([],error(arg_seq/[]),error).
arg_seq(error(X),error(X),error).


list_tail([X|L1],L3,T3) :-
	(	X = close_list ->
		L3 = L1, 
		T3 = con([])
	;	X = comma ->
		one_arg(L1,L2,T1),
		list_tail(L2,L3,T2),
		T3 = fun('.',[T1,T2])
	;	X = head_tail_sep ->
		one_arg(L1,L2,T3),
		expect(L2,close_list,L3)
	; 	L3 = error(tail_begin/[X|L1]),
		T3 = error
	).
list_tail([],error(tail_begin/[]),error).
list_tail(error(X),error(X),error).


more([name(X)|L1],N1,N2,T1,L3,T3) :-
	(	infix_op(X) ->
		infix_prec(X,N3,N4,N5),
		(	N3 =< N2 ->
			(	N1 =< N4 ->
				term(L1,N5,L2,T2),
				more(L2,N3,N2,fun(X,[T1,T2]),L3,T3)
			;	L3 = error(more_infix_prec/[name(X)|L1]),
				T3 = error
			)
		; 	L3 = [name(X)|L1], 
			T3 = T1
		)
	;	postfix_op(X) ->
		postfix_prec(X,N3,N4),
		(	N3 =< N2 ->
			(	N1 =< N4 ->
				more(L1,N3,N2,fun(X,[T1]),L3,T3)
			;	L3 = error(more_postfix_prec/[name(X)|L1]),
				T3 = error
			)
		; 	L3 = [name(X)|L1],
			T3 = T1
		)
	; 	L3 = [name(X)|L1], 
		T3 = T1
	).
more([comma|L1],N1,N2,T1,L3,T3) :-		% op(1000,xfy,',')
	(	1000 =< N2 ->
		(	N1 =< 999 ->
			term(L1,1000,L2,T2),
			more(L2,1000,N2,fun(',',[T1,T2]),L3,T3)
		;	L3 = error(more_comma_as_infix/[comma|L1]),
			T3 = error
		)
	;	L3 = [comma|L1], 
		T3 = T1
	).
more(L,_,_,T,L,T) :-
	\+ more_begin(L).


more_begin([name(_)|_]).
more_begin([comma|_]).

% End of read.pl
