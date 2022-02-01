/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 7/20/95, 10:21 PM */
/* Filename: test_parse.pl */
/* Abstract: Testfile for tokens.pl and read.pl .
   Input from test_parse.in . */

:- op(100,yf,++).
:- op(100,xf,!).
:- op(10,fy,&).
:- op(10,xf,&).

:- op(10,fx,fx10).
:- op(10,xfy,xfy10).
:- op(10,xf,xf10).
:- op(5,yfx,yfx5).
:- op(5,yf,yf5).

ok(variable('XYZ')).					%  1
ok(variable('__A__')).					%  2
ok(variable('_')).					%  3
ok(integer(1963)).					%  4
ok(integer(1963)).					%  5
ok(integer(1963)).					%  6
ok(integer(1963)).					%  7
ok(integer(1963)).					%  8
ok(integer(1963)).					%  9
ok(con(identifier_1)).					% 10
ok(con(//~@#^&*-++:<>\?.)).				% 11 (Why no ^ $)
ok(fun(!,[con(';')])).					% 12
ok(char_code_list([32,39,32,39,32,34,32,34,32,96,32,96,32,32,92])). % 13
ok(fun(f,[con(a1),con(a2)])).				% 14
ok(con([])).						% 15
ok(fun('.',[con(a1),con([])])).				% 16
ok(fun('.',[con(a1),fun('.',[con(a2),con([])])])).	% 17
ok(fun('.',[con(a1),con(a2)])).				% 18
ok(fun('.',[con(a1),fun('.',[con(a2),con(a3)])])).	% 19
ok(fun('.',[con(a1),con([])])).				% 20
ok(fun(+,[fun(+,[con(a1),con(a2)]),con(a3)])).		% 21
ok(fun(+,[con(a1),fun(+,[con(a2),con(a3)])])).		% 22
ok(fun(+,[fun(+,[con(a1),con(a2)]),con(a3)])).		% 23
ok(fun(+,[fun(*,[con(a1),con(a2)]),fun(*,[con(a3),con(a4)])])). % 24
ok(fun(*,[fun(+,[con(a1),variable('A2')]),fun(+,[con(a3),variable('A4')])])).	% 25
ok(fun(\+,[fun(\+,[con(a1)])])).			% 26
ok(fun(\+,[fun(+,[con(a1),con(a2)])])).		% 27
ok(fun(+,[fun(\+,[con(a1)]),con(a2)])).		% 28
ok(fun(+,[fun(+,[con(a1)]),con(a2)])).			% 29
ok(fun(*,[con(a1),fun(++,[fun(++,[con(a2)])])])).	% 30
ok(fun(*,[fun(!,[con(a1)]),fun(!,[con(a2)])])).		% 31
ok(fun(f,[con(+),con(++)])).				% 32
ok(fun('.',[con(+),fun('.',[con(\+),fun('.',[con(++),con([])])])])).	% 33
ok(fun('.',[con(+),fun('.',[con(\+),con(++)])])).	% 34
ok(fun(+,[con(\+),con(++)])).				% 35
ok(fun(f,[fun(',',[con(a1),con(a2)]),con(a3)])).	% 36
ok(fun('.',[fun((:-),[con(a1),fun(',',[con(a2),fun(',',[con(a3),con(a4)])])]),con([])])).   % 37
ok(fun((:-),[con(a1),fun(',',[con(a2),fun(',',[con(a3),con(a4)])])])).	% 38
ok(fun(',',[con(a),fun(',',[con(b),con(c)])])).		% 39
ok(fun(',',[con(a),fun(',',[con(b),con(c)])])).		% 40
ok(fun(f,[con(',')])).					% 41
ok(fun(',',[con(a),con(b)])).				% 42
ok(fun(',',[con(a),con(b)])).				% 43
ok(fun(',',[con(a),con(b)])).				% 44
ok(error(term_begin/[comma,close,end])).		% 45
ok(error(term_begin/[comma,open(layout),name(a),comma,name(b),close,end])). % 46
ok(fun((:-),[fun(';',[fun(',',[con(a1),con(a2)]),con(a3)])])).	% 47
ok(fun(';',[fun((:-),[con(a1),con(a2)]),con(a3)])).	% 48
ok(fun(-,[fun(',',[con(a),con(b)])])).			% 49
ok(fun(-,[fun(',',[con(a),con(b)])])).			% 50
ok(fun('{}',[con(a1)])).				% 51
ok(fun('{}',[fun(',',[con(a1),con(a2)])])).		% 52
ok(fun('{}',[fun(+,[con(a1),con(a2)])])).		% 53
ok(con('{}')).						% 54
ok(fun(&,[fun(&,[con(a)])])).				% 55
ok(fun(&,[fun(&,[con(a)])])).				% 56
ok(fun(&,[fun(&,[con(a)])])).				% 57
ok(fun(&,[fun(&,[con(a)])])).				% 58
ok(error(more_postfix_prec/[name(&),end])).		% 59
ok(fun(-,[integer(1),integer(2)])).			% 60
ok(integer(-2)).					% 61
ok(error(more_infix_prec/[name(xfy10),name(b),end])).	% 62
ok(error(more_postfix_prec/[name(xf10),end])).		% 63
ok(error(more_infix_prec/[name(yfx5),name(b),end])).	% 64
ok(error(more_postfix_prec/[name(yf5),end])).		% 65		
ok(con(end_of_file)).

:- see('test_parse.in'),
	repeat,
	ok(T1),
	pread(T2),
	(	T1 = T2 -> 
		(	T1 = con(end_of_file) -> 
			seen
		; 	fail
		)
    	;	write('*** Error: '), nl, 
		writeq(T1), nl, 
		writeq(T2), nl
	),
    	write('*** Test O.K.'), nl.
    
