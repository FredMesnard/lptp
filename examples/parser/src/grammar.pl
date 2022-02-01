/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 6/23/95, 12:40 PM */
/* Filename: grammar.pl */
/* Abstract: A specification of the syntax of ISO standard Prolog. The
specification is valid under the condition that the predicate consistent_op/0
succeeds. The predicates infix_prec/4, prefix_prec/3, postfix_prec/3,
infix_op/1, prefix_op/1, postfix_op/1 and symbol_op/1 are defined in the file
``read.pl'' which contains the verified deterministic parser. The file
``dcg_grammar.pl'' contains a definite clause grammar (DCG) for ISO standard
Prolog corresponding to the specification in this file. The main predicate of
this file is the predicate wf_term/3 which defines well-formed Prolog terms. 
The predicate append/3 has the usual definition. */

consistent_op :- 
	\+ inconsistent_op,
	current_op(1000,xfy,','),	% comma is predefined
	current_op(500,fx,-).		% minus is predefined

inconsistent_op :-		% operators have unique precedence
	current_op(N1,T,X),
	current_op(N2,T,X),
	\+ N1 = N2.
inconsistent_op :-		% infix operators have unique type
	current_op(_,T1,X),
	infix_type(T1),
	current_op(_,T2,X),
	infix_type(T2),
	\+ T1 = T2.
inconsistent_op :-		% prefix operators have unique type
	current_op(_,fx,X),
	current_op(_,fy,X).
inconsistent_op :-		% postfix operators have unique type
	current_op(_,xf,X),
	current_op(_,yf,X).
inconsistent_op :-		% no infix and postfix operators
	infix_op(X),
	postfix_op(X).
inconsistent_op :-		% '[]' cannot be an operator
	current_op(_,_,'[]').
inconsistent_op :-		% '{}' cannot be an operator
	current_op(_,_,'{}').
inconsistent_op :-		% comma has only one definition
	current_op(_,T,','),
	\+ T = xfy.
inconsistent_op :-		% xfy and yfx operators have different prec
	current_op(N,yfx,_),	% (not contained in ISO standard, why not?)
	current_op(N,xfy,_).
inconsistent_op :-		% fy and yfx operators have different prec
	current_op(N,fy,_),	% (not contained in ISO standard, why not?)
	current_op(N,yfx,_).
inconsistent_op :-		% yf and xfy operators have different prec
	current_op(N,yf,_),	% (not contained in ISO standard, why not?)
	current_op(N,xfy,_).
inconsistent_op :-		% fy and yf operators have different prec
	current_op(N,fy,_),	% (not contained in ISO standard, why not?)
	current_op(N,yf,_).


infix_type(xfx).
infix_type(xfy).
infix_type(yfx).


token(name(X)) :-		% ',' yields name(',')
	atom(X).
token(variable(X)) :-
	atomic(X).
token(integer(X)) :-
	integer(X).
token(float_number(X)) :-
	number(X).
token(char_code_list(X)) :-
	char_code_list(X).
token(open(nolayout)).
token(open(layout)).
token(close).			% )
token(open_list).		% [
token(close_list).		% ]
token(open_curly).		% {
token(close_curly).		% }
token(head_tail_sep).		% |
token(comma).			% , yields comma
token(end).			% .


token_list([]).
token_list([X|L]) :-
	token(X),
	token_list(L).


parse_tree(variable(X)) :-
	atomic(X).
parse_tree(integer(X)) :-
	integer(X).
parse_tree(float_number(X)) :-
	number(X).
parse_tree(char_code_list(X)) :- 
	char_code_list(X).
parse_tree(con(X)) :-
	atom(X).
parse_tree(fun(X,Ts)) :- 
	atom(X),
	parse_tree_list(Ts).
	

parse_tree_list([]).
parse_tree_list([T|Ts]) :-
	parse_tree(T),
	parse_tree_list(Ts).


dcg(L,T) :-
	wf_term(L,N,T), 
	N =< 1200.

% (1) variables

wf_term([variable(X)],0,variable(X)).

% (2) numbers and strings

wf_term([integer(X)],0,integer(X)).
wf_term([float_number(X)],0,float_number(X)).
wf_term([char_code_list(X)],0,char_code_list(X)).

% (3) names as constants
	
wf_term([name(X)],0,con(X)) :- \+ symbol_op(X).

% (4) functor with arguments

wf_term(L,0,fun(X,[T|Ts])) :-
	append([name(X),open(nolayout)|L1],L2,L),
	wf_one_arg(L1,T),
	wf_arg_seq(L2,Ts).

% (5) lists

wf_term([open_list,close_list],0,con([])).
wf_term(L,0,fun('.',[T1,T2])) :-
	append([open_list|L1],L2,L),
	wf_one_arg(L1,T1),
	wf_list_tail(L2,T2).

% (6) term in parenthesis

wf_term(L,0,T) :-
	append([open(_)|L1],[close],L),
	wf_term(L1,N,T),
	N =< 1200.

% (7) term in curly braces

wf_term([open_curly,close_curly],0,con('{}')).
wf_term(L,0,fun('{}',[T])) :-
	append([open_curly|L1],[close_curly],L),
	wf_term(L1,N,T),
	N =< 1200.

% (8) operator as atoms

wf_term([open(_),name(X),close],0,con(X)) :- symbol_op(X).

% (9) prefix operators

wf_term([name(X),Y|L],N,fun(X,[T]))  :-
	prefix_prec(X,N,M),
	\+ Y = open(nolayout),
	\+ (X = (-), number_token(Y)),
	wf_term([Y|L],K,T),
	K =< M.

% (10) infix operators

wf_term(L,N,fun(X,[T1,T2])) :-
	append(L1,[name(X)|L2],L),
	infix_prec(X,N,M1,M2),
	wf_term(L1,K1,T1), 
	K1 =< M1,
	wf_term(L2,K2,T2),
	K2 =< M2.

% (11) comma as infix operator: op(1000,xfy,',')

wf_term(L,1000,fun(',',[T1,T2])) :-
	append(L1,[comma|L2],L),
	wf_term(L1,K1,T1),
	K1 =< 999,
	wf_term(L2,K2,T2),
	K2 =< 1000.

% (12) postfix operators

wf_term(L,N,fun(X,[T])) :-
	append(L1,[name(X)],L),
	postfix_prec(X,N,M),
	wf_term(L1,K,T),
	K =< M.

% (13) negative numbers

wf_term([name(-),integer(X)],0,integer(Y)) :-
	Y is -(X).
wf_term([name(-),float_number(X)],0,float_number(Y)) :-
	Y is -(X).

% (14) argument

wf_one_arg(L,T) :- 
	wf_term(L,N,T),
	N =< 999.
wf_one_arg([name(X)],con(X)) :-
	symbol_op(X).

% (15) list of arguments

wf_arg_seq([close],[]).
wf_arg_seq(L,[T|Ts]) :-
	append([comma|L1],L2,L),
	wf_one_arg(L1,T),
	wf_arg_seq(L2,Ts).

% (16) tail of a list

wf_list_tail([close_list],con([])).
wf_list_tail(L,fun('.',[T1,T2])) :-
	append([comma|L1],L2,L),
	wf_one_arg(L1,T1),
	wf_list_tail(L2,T2).
wf_list_tail(L,T) :-
	append([head_tail_sep|L1],[close_list],L),
	wf_one_arg(L1,T).


% The predicates start_token/1 and sep_token_cons/1 are used in the
% correctness proof.

start_token(name(_)).
start_token(variable(_)).
start_token(integer(_)).
start_token(float_number(_)).
start_token(char_code_list(_)).
start_token(open(_)).
start_token(open_list).
start_token(open_curly).


sep_token_cons([X|_]) :- sep_token(X).

% End of grammar.pl

