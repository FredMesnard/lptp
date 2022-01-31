/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 6/15/95, 12:04 AM */
/* Filename: dcg_grammar.pl */
/* Abstract: This file contains a definite clause grammar (DCG) of ISO
standard Prolog. The DCG rules are non-standard. We use ==> instead of -->.
At the end of this file there is an interpreter for our rules which makes the
DCG grammar executable under Prolog (but very, very slow). The file
``grammar.pl'' contains the translation of the DCG grammar into definite Horn
clauses. The predicates infix_prec/4, prefix_prec/3, postfix_prec/3 and
symbol_op/1 are defined in the file ``read.pl'' which contains a deterministic
(verified) parser.  The predicates token/1, token_list/1 and parse_tree/1 are
defined in ``grammar.pl''. In the DCG an expression term(N,T,E) stands for a
list of tokens of precedence N representing the parse tree T with leftmost
token E. The predicate dcg_parse/2 could be used to parse a token list into a
tree. */

:- op(1200,xfx,==>).

% (1) variables

term(0,T,E) ==> [variable(X)],
	{ T = variable(X), E = variable(X) }.

% (2) numbers and strings

term(0,T,E) ==> [integer(X)],
	{ T = integer(X), E = integer(X) }.

term(0,T,E) ==> [float_number(X)],
	{ T = float_number(X), E = float_number(X) }.

term(0,T,E) ==> [char_code_list(X)], 
	{ T = char_code_list(X), E = char_code_list(X) }.

% (3) names as constants

term(0,T,E) ==>  [name(X)], 
	{ \+ symbol_op(X),
	  T = con(X), E = name(X) }.

% (4) functor and arguments

term(0,T,E) ==> [name(X),open(nolayout)], one_arg(T1), arg_seq(Ts),
	{ T = fun(X,[T1|Ts]), E = name(X) }.

% (5) lists

term(0,T,E) ==> [open_list,close_list],
	{ T = con([]), E = open_list }.

term(0,T,E) ==> [open_list], one_arg(T1), list_tail(T2),
	{ T = fun('.',[T1,T2]), E = open_list }.

% (6) term in parenthesis

term(0,T,E) ==> [open(X)], term(N,T,_), [close],
	{ E = open(X), N =< 1200 }.

% (7) term in curly braces

term(0,T,E) ==> [open_curly,close_curly],
	{ T = con('{}'), E = open_curly }.

term(0,T,E) ==> [open_curly], term(N,T1,_), [close_curly],
	{ T = fun('{}',[T1]), E = open_curly, N =< 1200 }.

% (8) operator as atoms

term(0,T,E) ==> [open(X),name(Y),close],
	{ symbol_op(Y), T = con(Y), E = open(X) }.

% (9) prefix operators

term(N,T,E) ==> [name(X)], term(K1,T1,E1),
	{ prefix_prec(X,N,M1), K1 =< M1,
	  \+ E1 = open(nolayout), \+ (X = (-), number_token(E1)),
	  T = fun(X,[T1]), E = name(X) }.

% (10) infix operators

term(N,T,E) ==> term(K1,T1,E), [name(X)], term(K2,T2,_),
	{ infix_prec(X,N,M1,M2), K1 =< M1, K2 =< M2,
	  T = fun(X,[T1,T2]) }.

% (11) comma as infix operator: op(1000,xfy,',')

term(1000,T,E) ==> term(K1,T1,E), [comma], term(K2,T2,_),
	{ K1 =< 999, K2 =< 1000, T = fun(',',[T1,T2]) }.

% (12) postfix operators

term(N,T,E) ==> term(K1,T1,E), [name(X)], 
	{ postfix_prec(X,N,M1), K1 =< M1, T = fun(X,[T1]) }.

% (13) negative numbers

term(0,T,E) ==> [name(-),integer(X)],
	{ Y = - X, T = integer(Y), E = name(-) }.

term(0,T,E) ==> [name(-),float_number(X)],
	{ Y = - X, T = float_number(Y), E = name(-) }.

% (14) argument

one_arg(T) ==> term(N,T,_),
	{ N =< 999 }.
	
one_arg(T) ==> [name(X)],
	{ symbol_op(X), T = con(X) }.

% (15) list of arguments

arg_seq(Ts) ==> [close],
	{ Ts = [] }.

arg_seq(Ts) ==> [comma], one_arg(T), arg_seq(Ts1),
	{ Ts = [T|Ts1] }.

% (16) tail of a list

list_tail(T) ==> [close_list],
	{ T = con([]) }.

list_tail(T) ==> [comma], one_arg(T1), list_tail(T2),
	{ T =fun('.',[T1,T2]) }.

list_tail(T) ==> [head_tail_sep], one_arg(T), [close_list].



% A non-standard DCG interpreter.

dcg([],L,L).			% terminals
dcg([X|Xs],[X|L1],L2) :- 	% terminals
	append(Xs,L2,L1).
dcg((A,B),L1,L3) :-		% compound bodies
	\+ dcg_special(B),
	dcg(A,L1,L2),
	dcg(B,L2,L3).
dcg({A},L,L) :- 		% side conditions
	call(A).
dcg((A,[X],B),L1,L4) :-		% special case (for termination)
	append(L2,[X|L3],L1),
	dcg(A,L2,[]),
	dcg(B,L3,L4).
dcg(A,L1,L2) :-			% non terminals
	(A ==> B),
	dcg(B,L1,L2).


dcg_special(([_],_)).


dcg_parse(L,T) :- 
	dcg(term(N,T,_),L,[]),
	N =< 1200.

% End of dcg_grammar.pl

