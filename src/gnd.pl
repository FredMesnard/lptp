/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 6/11/95, 8:32 PM */
/* Updated: Wed Jul 21 13:41:22 1999 */
/* Filename: gnd.pl */
/* Abstract: Ground representation of programs. */

%% The predicate gnd__compile(F) transforms the clauses of the File <F>.pl into
%% ground facts of the form clauses(_,_) and writes them on the File <F>.gr.
%% It is assumed that the clauses do not contain subterms of the form 'VAR'(_).
%% Op declarations are ignored.

:- dynamic tmp_clause/4.
:- dynamic tmp_predicate_name/1.

%%d gnd__compile(gr::in)

gnd__compile(Path) :-
	io__expand(Path,File),
	concat_atom([File,'.pl'],File_pl),	% append '.pl' to File
	io__get_stream(File_pl,read,Stream_pl),	% open the file File_pl
	io__set_input(Stream_pl),		% set input to File_pl
	abolish(tmp_clause/4),
	abolish(tmp_predicate_name/1),
	once(gnd__read_clauses),		% read the file File_pl
	close(Stream_pl),
	concat_atom([File,'.gr'],File_gr),	% append '.gr' to File
	io__get_stream(File_gr,write,Stream_gr),% open the file File_gr
	io__set_output(Stream_gr),		% set output to File_gr
	setof(R,tmp_predicate_name(R),RL),	% collect all predicates
	gnd__write_clauses(RL),			% write clauses to File_gr
	close(Stream_gr),			% close the file File_gr
	ctl__message([new,file,File_gr]).

%%d gnd__read_clauses

gnd__read_clauses :-
	repeat,
	read_with_variables(Clause,NameL),
	gnd__instantiate_vars(NameL),
	(	Clause = end_of_file ->
		true
	;	once(gnd__convert_clause(Clause)), 
		fail
	).

%%d gnd__instantiate_vars(any)

gnd__instantiate_vars([]).
gnd__instantiate_vars([A = Variable|L]) :-
	name(A,[N|NL]),
	(	65 =< N, 
		N =< 90 ->			% ascii(N) is A-Z
		M is N + 32,			% ascii(M) is a-z
		name(B,[M|NL])
	;	B = A
	),
	Variable = 'VAR'(B),
	gnd__instantiate_vars(L).

%%d gnd__convert_clause(any)

gnd__convert_clause(:-(X,Y)) :-
	gnd__term(X,0,Atom,N1),
	gnd__goal(Y,N1,Goal,N2),
	gnd__assert_clause(X,Atom,Goal,N2).
gnd__convert_clause(X) :-
	\+ gnd__rule_form(X),
	gnd__term(X,0,Atom,N),
	gnd__assert_clause(X,Atom,[&],N).
	
%% op(1100,xfy,;)
%% op(1050,xfy,->)
%% op(100,xfy,',')

%%d gnd__rule_form(any)
%%d gnd__comma_form(any)
%%d gnd__semicolon_form(any)
%%d gnd__implication_form(any)

gnd__rule_form((_ :- _)).
gnd__comma_form((_ , _)).
gnd__comma_form(true).
gnd__semicolon_form((_ ; _)).
gnd__semicolon_form(fail).
gnd__implication_form((_ -> _)).

%%d gnd__goal_form(any)

gnd__goal_form(true).
gnd__goal_form(fail).
gnd__goal_form(_ = _).
gnd__goal_form(not _).
gnd__goal_form(\+ _).
gnd__goal_form((_ , _)).
gnd__goal_form((_ ; _)).

%%d gnd__goal(any,int::in,goal::out,int::out)

gnd__goal(true,N,[&],N).
gnd__goal(fail,N,[\/],N).
gnd__goal(X1 = X2,N1,[=,E1,E2],N3) :-
	gnd__term(X1,N1,E1,N2),
	gnd__term(X2,N2,E2,N3).
gnd__goal(not X,N1,[~,Goal],N2) :-
	gnd__goal(X,N1,Goal,N2).
gnd__goal(\+ X,N1,[~,Goal],N2) :-
	gnd__goal(X,N1,Goal,N2).
gnd__goal((X,Y),N1,[&|Goal2L],N3) :-
	gnd__conjunction(Y,N1,[],N2,Goal1L),
	gnd__conjunction(X,N2,Goal1L,N3,Goal2L).
gnd__goal(X,N1,[\/|GoalL],N2) :-
	gnd__semicolon_form(X),
	gnd__disjunction(X,N1,[],N2,GoalL).
gnd__goal(X,N1,Atom,N2) :-
	\+ gnd__goal_form(X),
	gnd__term(X,N1,Atom,N2).

%%d gnd__conjunction(any,int::in,goalL::out,int::out)

gnd__conjunction((X,Y),N1,Goal1L,N3,Goal3L) :-
	gnd__conjunction(Y,N1,Goal1L,N2,Goal2L),
	gnd__conjunction(X,N2,Goal2L,N3,Goal3L).
gnd__conjunction(true,N,GoalL,N,GoalL).
gnd__conjunction(X,N1,GoalL,N2,[Goal|GoalL]) :-
	\+ gnd__comma_form(X),
	gnd__goal(X,N1,Goal,N2).

%%d gnd__disjunction(any,int::in,goalL::out,int::out)

gnd__disjunction((X;Y),N1,Goal1L,N3,Goal3L) :-
	\+ gnd__implication_form(X),
	gnd__disjunction(Y,N1,Goal1L,N2,Goal2L),
	gnd__disjunction(X,N2,Goal2L,N3,Goal3L).
gnd__disjunction(fail,N,GoalL,N,GoalL).
gnd__disjunction(X,N1,GoalL,N2,[Goal|GoalL]) :-
	\+ gnd__semicolon_form(X),
	gnd__goal(X,N1,Goal,N2).
gnd__disjunction((X -> Y ; Z),N1,Goal1L,N4,Goal2L) :-
	gnd__goal(X,N1,Goal1,N2),
	gnd__goal(Y,N2,Goal2,N3),
	gnd__goal(Z,N3,Goal3,N4),
	gnd__join_conjunctions(Goal1,Goal2,Goal4),
	gnd__join_conjunctions([~,Goal1],Goal3,Goal5),
	Goal2L = [Goal4,Goal5|Goal1L].

%%d gnd__join_conjunctions(goal::in,goal::in,goal::out)

gnd__join_conjunctions(Goal1,Goal2,Goal3) :-
	(	Goal1 = [&|Goal1L] ->
		(	Goal2 = [&|Goal2L] ->
			lst__append(Goal1L,Goal2L,Goal3L),
			Goal3 = [&|Goal3L]
		;	lst__append(Goal1L,[Goal2],Goal3L),
			Goal3 = [&|Goal3L]
		)
	;	(	Goal2 = [&|Goal2L] ->
			Goal3 = [&,Goal1|Goal2L]
		;	Goal3 = [&,Goal1,Goal2]
		)
	).

%%d gnd__term(any,int::in,fml::out,int::out)

gnd__term(X,N1,$(N1),N2) :-		% X is bound to 'VAR'(N1)
	var(X),
	X = 'VAR'(N1),
	N2 is N1 + 1, !.
gnd__term('VAR'(X),N,$(X),N) :-		% 'VAR'(N)
	atomic(X), !.
gnd__term(X,N1,[n(Tag,N)|TermL],N2) :-	% f(T1,...,Tn)
	functor(X,Tag,N),
	X =.. [Tag|XL],
	gnd__termL(XL,N1,TermL,N2).

%%d gnd__termL(any,int::in,tmL::in,int::out)

gnd__termL([],N,[],N).
gnd__termL([X|XL],N1,[Term|TermL],N3) :-
	gnd__term(X,N1,Term,N2),
	gnd__termL(XL,N2,TermL,N3).

%%d gnd__assert_clause(gr::in,atm::in,goal::in,int::in)

gnd__assert_clause(X,Atom,Goal,N) :-
	eq__add_free_qf(Atom,[],V1L),
	eq__add_free_qf(Goal,V1L,V2L),
	lst__reverse(V2L,V3L),
	functor(X,Functor,Arity),
	assert(tmp_clause(n(Functor,Arity),Atom,Goal,V3L/N)),
	assert(tmp_predicate_name(n(Functor,Arity))).

%%d gnd__write_clauses(grL::in)

gnd__write_clauses([]).
gnd__write_clauses([Tag|TagL]) :-
	bagof(clause(Atom,Goal,N),tmp_clause(Tag,Atom,Goal,N),ClauseL),
	nl, write(':- assert_clauses('),
	writeq(Tag),
	write(',['), nl,
	gnd__write_clauseL(ClauseL),
	nl, write(']).'), nl,
	gnd__write_clauses(TagL).

%%d gnd__write_clauseL(clsL::in)

gnd__write_clauseL([]).
gnd__write_clauseL([Clause]) :-
	gnd__write_clause(Clause).
gnd__write_clauseL([Clause1,Clause2|ClauseL]) :-
	gnd__write_clause(Clause1),
	gnd__write_clause_comma([Clause2|ClauseL]).

%%d gnd__write_clause_comma(clsL::in)

gnd__write_clause_comma([]).
gnd__write_clause_comma([Clause|ClauseL]) :-
	write(','), nl,
	gnd__write_clause(Clause),
	gnd__write_clause_comma(ClauseL).

%%d gnd__write_clause(cls::in)

gnd__write_clause(clause(Atom,Goal,N)) :-
	write(' clause('),
	writeq(Atom), write(','), nl,
	write('  '),
	writeq(Goal),
	write(','), nl,
	write('  '),
	writeq(N),
	write(')').
	
% gnd.pl ends here

