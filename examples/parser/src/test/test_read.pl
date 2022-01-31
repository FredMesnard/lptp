/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 6/8/95, 4:51 PM */
/* Filename: test_read.pl */
/* Abstract: Needs grammar.pl, read.pl, dcg_grammar.pl and write.pl . */

:- op(100,yf,++).
:- op(100,xf,!).
:- op(10,fy,&).
:- op(10,xf,&).

:- op(10,fx,fx10).
:- op(10,xfy,xfy10).
:- op(10,xf,xf10).
:- op(5,yfx,yfx5).
:- op(5,yf,yf5).

test(L,T) :- test(L,T,L).

test(L1,T1,L2) :-
	token_list(L1),				% type check
	parse_tree(T1),				% type check
	token_list(L2),				% type check
%	bagof(T2,wf_parse(L1,T2),L3),		% grammar
%	L3 = [T1],				% grammar
	append(L1,[end],L4),			% grammar
	bagof(T3,parse(L4,T3),L5),		% parse
	L5 = [T1],				% parse
	bagof(L6,un_parse(T1,L6),L7),		% unparse
	L7 = [L2],				% unparse
	bagof(L8,term(L4,1200,L8,_),L9),	% parse
	L9 = [[end]].				% parse
%	bagof(T3,dcg_parse(L1,T3),L10),		% dcg_parse
%	L10 = [T1].				% dcg_parse


test_error(L1,L2) :-
	token_list(L1),
	append(L1,[end],L3),
	term(L3,1200,L4,_),
	L2 = L4.	

t(L) :-
	token_list(L),
	bagof(T1,wf_parse(L,T1),L1),
	nl, writeq(L1),
	append(L,[end],L2),
	bagof(T2,parse(L2,T2),L3),
	nl, writeq(L3),
	L3 = [T3],
	bagof(L4,un_parse(T3,L4),L5),
	nl, writeq(L5),
	bagof(L6,term(L2,1200,L6,_),L7),
	nl, writeq(L7), nl.

test_dcg(L) :-
	token_list(L),
	bagof(T,dcg_parse(L,T),L1),
	nl, writeq(L1).

x(L1) :-
	(token_list(L1) ->
		term(L1,1200,L2,_),
		writeq(L2), nl
	;	write('*** not a token list'), nl).

% standard terms

:- test([variable(1)],variable(1)).

:- test([integer(1)],integer(1)).

:- test([name(c)],con(c),[name(c)]).

:- test([name(f),open(nolayout),name(a1),comma,name(a2),close],
	fun(f,[con(a1),con(a2)])).

% lists

:- test([open_list,close_list],con([])).

:- test([open_list,name(a1),close_list],fun('.',[con(a1),con([])])).

:- test([open_list,name(a1),comma,name(a2),close_list],fun('.',[con(a1),fun('.',[con(a2),con([])])])).

:- test([open_list,name(a1),head_tail_sep,name(a2),close_list],fun('.',[con(a1),con(a2)])).

:- test([open_list,name(a1),comma,name(a2),head_tail_sep,name(a3),close_list],
	fun('.',[con(a1),fun('.',[con(a2),con(a3)])])).

% parentheses

:- test([open(nolayout),open_list,open(nolayout),name(a1),close,close_list,close],fun('.',[con(a1),con([])]),
	[open_list,name(a1),close_list]).

% operators

:- test([name(a1),name(+),name(a2),name(+),name(a3)],
	fun(+,[fun(+,[con(a1),con(a2)]),con(a3)])).

:- test([name(a1),name(+),open(nolayout),name(a2),name(+),name(a3),close],
	fun(+,[con(a1),fun(+,[con(a2),con(a3)])])).

:- test([open(nolayout),name(a1),name(+),name(a2),close,name(+),name(a3)],
	fun(+,[fun(+,[con(a1),con(a2)]),con(a3)]),
	[name(a1),name(+),name(a2),name(+),name(a3)]).

:- test([name(a1),name(*),variable(2),name(+),name(a3),name(*),variable(4)],
	fun(+,[fun(*,[con(a1),variable(2)]),fun(*,[con(a3),variable(4)])])).

:- test([open(nolayout),name(a1),name(+),variable(2),close,name(*),open(nolayout),name(a3),name(+),variable(4),close],
	fun(*,[fun(+,[con(a1),variable(2)]),fun(+,[con(a3),variable(4)])])).

:- test([name(\+),name(\+),name(a1)],fun(\+,[fun(\+,[con(a1)])])).

:- test([name(\+),name(a1),name(+),name(a2)],fun(\+,[fun(+,[con(a1),con(a2)])])).

:- test([open(nolayout),name(\+),name(a1),close,name(+),name(a2)],fun(+,[fun(\+,[con(a1)]),con(a2)])).

:- test([name(+),name(a1),name(+),name(a2)],fun(+,[fun(+,[con(a1)]),con(a2)])).

:- test([name(a1),name(*),name(a2),name(++),name(++)],
	fun(*,[con(a1),fun(++,[fun(++,[con(a2)])])])).
	
:- test([name(a1),name(!),name(*),name(a2),name(!)],
	fun(*,[fun(!,[con(a1)]),fun(!,[con(a2)])])).

% operators as atoms

:- test([name(f),open(nolayout),name(+),comma,name(++),close],
	fun(f,[con(+),con(++)])).

:- test([open_list,name(+),comma,name(\+),comma,name(++),close_list],
	fun('.',[con(+),fun('.',[con(\+),fun('.',[con(++),con([])])])])).

:- test([open_list,name(+),comma,name(\+),head_tail_sep,name(++),close_list],
	fun('.',[con(+),fun('.',[con(\+),con(++)])])).

:- test([open(nolayout),name(\+),close,name(+),open(nolayout),name(++),close],
	fun(+,[con(\+),con(++)])).

% comma as operator

:- test([name(f),open(nolayout),open(nolayout),name(a1),comma,name(a2),close,comma,name(a3),close],
	fun(f,[fun(',',[con(a1),con(a2)]),con(a3)])).

:- test([open_list,open(nolayout),name(a1),name((:-)),name(a2),comma,name(a3),comma,name(a4),close,close_list],
	fun('.',[fun((:-),[con(a1),fun(',',[con(a2),fun(',',[con(a3),con(a4)])])]),con([])])).

:- test([name(a1),name((:-)),name(a2),comma,name(a3),comma,name(a4)],
	fun((:-),[con(a1),fun(',',[con(a2),fun(',',[con(a3),con(a4)])])])).

:- test([name(a),name(','),name(b),name(','),name(c)],
	fun(',',[con(a),fun(',',[con(b),con(c)])]),
	[name(a),comma,name(b),comma,name(c)]).

:- test([name(a),comma,name(b),comma,name(c)],
	fun(',',[con(a),fun(',',[con(b),con(c)])])).

:- test([name(f),open(nolayout),name(','),close],
	fun(f,[con(',')])).

:- test([name(a),comma,name(b)],fun(',',[con(a),con(b)])).

:- test([name(a),name(','),name(b)],
	fun(',',[con(a),con(b)]),
	[name(a),comma,name(b)]).

:- test([name(','),open(nolayout),name(a),comma,name(b),close],
	fun(',',[con(a),con(b)]),
	[name(a),comma,name(b)]).

:- test_error([name(f),open(nolayout),comma,close],
	error(term_begin/[comma,close,end])).

:- test_error([comma,open(nolayout),name(a),comma,name(b),close],
	error(term_begin/[comma,open(nolayout),name(a),comma,name(b),close,end])).

% prefix operator with and without space

:- test([name((:-)),open(layout),name(a1),comma,name(a2),close,name(;),
	name(a3)],
	fun((:-),[fun(;,[fun(',',[con(a1),con(a2)]),con(a3)])]),
	[name((:-)),name(a1),comma,name(a2),name(;),name(a3)]).

:- test([name((:-)),open(nolayout),name(a1),comma,name(a2),close,name(;),
	name(a3)],
	fun(;,[fun((:-),[con(a1),con(a2)]),con(a3)]),
	[open(nolayout),name(a1),name((:-)),name(a2),close,name(;),name(a3)]).

:- test([name(-),open(layout),name(','),open(nolayout),name(a),comma,name(b),
	close,close],
	fun(-,[fun(',',[con(a),con(b)])]),
	[name(-),open(nolayout),open(nolayout),name(a),comma,name(b),close,
	close]).

:- test([name(-),open(layout),name(a),comma,name(b),close],
	fun(-,[fun(',',[con(a),con(b)])]),
	[name(-),open(nolayout),open(nolayout),name(a),comma,name(b),close,
	close]).

% negative numbers

:- test([name(-),integer(1)],integer(-1),[integer(-1)]).
:- test([name(-),open(layout),integer(1),close],fun(-,[integer(1)]),
	[name(-),open(nolayout),integer(1),close]).


% terms with braces

:- test([open_curly,name(a1),close_curly],fun('{}',[con(a1)])).

:- test([open_curly,name(a1),comma,name(a2),close_curly],
	fun('{}',[fun(',',[con(a1),con(a2)])])).

:- test([name('{}'),open(nolayout),name(a1),name(+),name(a2),close],
	fun('{}',[fun(+,[con(a1),con(a2)])]),
	[open_curly,name(a1),name(+),name(a2),close_curly]).

% prefix and postfix

:- test([name(&),name(a),name(&)],
	fun(&,[fun(&,[con(a)])]),
	[name(&),name(&),name(a)]).

:- test([name(&),name(&),name(a)],
	fun(&,[fun(&,[con(a)])])).

:- test([open(nolayout),name(&),name(a),close,name(&)],
	fun(&,[fun(&,[con(a)])]),
	[name(&),name(&),name(a)]).

:- test([open(nolayout),name(a),name(&),close,name(&)],
	fun(&,[fun(&,[con(a)])]),
	[name(&),name(&),name(a)]).

:- test_error([name(a),name(&),name(&)],
	error(more_postfix_prec/[name(&),end])).

% Error messages

:- test_error([name(fx10),name(a),name(xfy10),name(b)],
	error(more_infix_prec/[name(xfy10),name(b),end])).

:- test_error([name(fx10),name(a),name(xf10)],
	error(more_postfix_prec/[name(xf10),end])).

:- test_error([name(a),name(xf10),name(yfx5),name(b)],
	error(more_infix_prec/[name(yfx5),name(b),end])).

:- test_error([name(a),name(xf10),name(yf5)],
	error(more_postfix_prec/[name(yf5),end])).

:- write('*** Test O.K.'), nl.

% End of test_read.pl

