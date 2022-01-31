/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: Fri Dec  2 15:55:00 1994 */
/* Updated: Thu Jul 22 10:20:54 1999 */
/* Filename: prt.pl */
/* Abstract: Pretty print (pp). */

%%d prt__indent(int::out)

prt__indent(1).

%%d prt__text_width(int::out)

prt__text_width(76).
%prt__text_width(60).

%%d prt__no_break(gr::in)

prt__no_break(=).
prt__no_break(all).
prt__no_break(ex).
prt__no_break(?).
prt__no_break(succeeds).
prt__no_break(fails).
prt__no_break(terminates).
prt__no_break(:).
prt__no_break(~).
prt__no_break(by).
prt__no_break(<>).
prt__no_break(#<).
prt__no_break(#=<).

%%d prt__prefix_nolayout(gr::in)

prt__prefix_nolayout(?).

%%d prt__indent_infix(gr::in)

prt__indent_infix(:).
prt__indent_infix(by).
prt__indent_infix(=>).

%%d prt__break_args(gr::in)

prt__break_args(assume).
prt__break_args(contra).
prt__break_args(cases).
prt__break_args(cases).
prt__break_args(case).
prt__break_args(indirect).
prt__break_args(exist).
prt__break_args(induction).
prt__break_args(step).
prt__break_args(theorem).
prt__break_args(lemma).
prt__break_args(corollary).

%%d prt__write(gr::in,int::in)

prt__write(X) :-
	prt__text_width(Right),
	prt__write(X,0,Right).

%%d prt__write(gr::in,int::in,int::in)

prt__write(X,Left) :- 
	prt__text_width(Right),
	prt__write(X,Left,Right).

%%d prt__write(gr::in,int::in,int::in)

prt__write(X,Left,Right) :-
	(	prt__term_tree(X,Tree,_) ->
		tab(Left),
		Pos is Left + 1,
		prt__write_tree(Tree,Left,Pos,Right,_)
	;	ctl__error([pretty,print,cannot,print,X])
	).

% %%d prt__tree(gr::in)
% 
% prt__tree(node(Label,N)) :-			% N is the size of the linear
% 	integer(N),				% formatted version of Label
% 	prt__label(Label).
% 
% %%d prt__label(gr::in)
% 
% prt__label(constant(Name)) :-
% 	atomic(Name).
% prt__label(structure(Name,N,TreeL)) :-
% 	atomic(Name),
% 	integer(N),				% N is the length of Name
% 	prt__treeL(TreeL).
% 
% % [nobreak(Tree1,','),nobreak(Tree2,','),nobreak(Tree3,')')]
% % [break(Tree1,','),break(Tree2,','),nobreak(Tree3,')')]
% 
% prt__label(list(TreeL)) :-
% 	prt__treeL(TreeL).
% 
% % [nobreak(T1,','),nobreak(T2,'|'),nobreak(T3,']')]
% 
% prt__label(parenthesis(Tree)) :-
% 	prt__tree(Tree).
% prt__label(infix(Name,N,Tree1,Tree2)) :-
% 	atomic(Name),
% 	integer(N),				% N is the length of Name
% 	prt__tree(Tree1),
% 	prt__tree(Tree2).
% prt__label(prefix(Name,N,Tree)) :-
% 	atomic(Name),
% 	integer(N),				% N is the length of Name
% 	prt__tree(Tree).
% prt__label(postfix(Name,N,Tree)) :-
% 	atomic(Name),
% 	integer(N),				% N is the length of Name
% 	prt__tree(Tree).
% 
% %%d prt__treeL(grL::in)
% 
% prt__treeL([]).
% prt__treeL([X|TreeL]) :-
% 	prt__pair(X),
% 	prt__treeL(TreeL).
% 
% %%d prt__pair(gr::in)
% 
% prt__pair(break(Tree,Sep)) :-
% 	prt__tree(Tree),
% 	atomic(Sep).				% Sep in {',','|',']',')'}
% prt__pair(nobreak(Tree,Sep)) :-
% 	prt__tree(Tree),
% 	atomic(Sep).				% Sep in {',','|',']',')'}

%%d prt__term_tree(gr::in,tree::in,int::in)

prt__term_tree(X,Tree,N) :-
	prt__term_tree(X,1200,Tree,N).

%%d prt__term_tree(gr::in,int::in,tree::in,int::in)

prt__term_tree(X,Prec,Tree2,N3) :-
	(	var(X) ->			% logical variables
		fail
	;	atomic(X) ->			% atoms
		atomic_length(X,N3),
		Tree2 = node(constant(X),N3)
	;	X = [Y|YL] ->			% non-nil lists
		prt__term_tree(Y,999,Tree,N1),
		prt__list_tree(YL,Tree,N1,TreeL,N2),
		N3 is N2 + 1,			% 1 for '['
		Tree2 = node(list(TreeL),N3)
	;	X =.. XL,			% general case ==> univ
		prt__termL_tree(XL,Prec,Tree2,N3)
	).

%%d prt__termL_tree(grL::in,int::in,tree::in,int::in)

prt__termL_tree(L,Prec1,Tree4,N5) :-
	(	L = [Name,X1,X2],
		prt__infix(Name,Prec2,Prec3,Prec4) ->
		atomic_length(Name,N1),
		prt__term_op_tree(X1,Prec3,Tree1,N2),
		prt__term_op_tree(X2,Prec4,Tree2,N3),
		N4 is N1 + 2 + N2 + N3,			% 2 around operator
		Tree3 = node(infix(Name,N1,Tree1,Tree2),N4),
		prt__parenthesize(Prec1,Prec2,Tree3,N4,Tree4,N5)
	;	L = [Name,X1],
		prt__prefix(Name,Prec2,Prec3) ->
		atomic_length(Name,N1),
		prt__term_op_tree(X1,Prec3,Tree1,N2),
		(	prt__prefix_nolayout(Name) ->
			N3 is N1 + N2
		;	N3 is N1 + 1 + N2		% 1 after operator
		),
		Tree2 = node(prefix(Name,N1,Tree1),N3),
		prt__parenthesize(Prec1,Prec2,Tree2,N3,Tree4,N5)
	;	L = [Name,X1],
		prt__postfix(Name,Prec2,Prec3) ->
		atomic_length(Name,N1),
		prt__term_op_tree(X1,Prec3,Tree1,N2),
		N3 is N1 + 1 + N2,			% 1 before operator
		Tree2 = node(postfix(Name,N1,Tree1),N3),
		prt__parenthesize(Prec1,Prec2,Tree2,N3,Tree4,N5)
	;	L = [Name|XL],
		atomic_length(Name,N1),
		(	prt__break_args(Name) ->
			prt__break_args(XL,TreeL,N2)
		;	prt__nobreak_args(XL,TreeL,N2)
		),
		N5 is N1 + N2 + 1,			% 1 for '('
		Tree4 = node(structure(Name,N1,TreeL),N5)
	).

%%d prt__operator(gr::in)

prt__operator(Name) :- current_op(_,_,Name).

%%d prt__term_op_tree(gr::in,int::in,tree::out,int::out)

prt__term_op_tree(X,Prec,Tree,N) :-
	(	atom(X),
		\+ X = (','),
		current_op(_,_,X) ->
		atomic_length(X,N1),
		Tree = node(parenthesis(node(constant(X),N1)),N),
		N is N1 + 2
	;	prt__term_tree(X,Prec,Tree,N)
	).

%%d prt__nobreak_args(grL::in,int::in,grL::out,int::out)

prt__nobreak_args([X],[nobreak(Tree,')')],N2) :-
	prt__term_tree(X,999,Tree,N1),
	N2 is N1 + 1.
prt__nobreak_args([X1,X2|XL],[nobreak(Tree,',')|TreeL],N3) :-
	prt__term_tree(X1,999,Tree,N1),
	prt__nobreak_args([X2|XL],TreeL,N2),
	N3 is N1 + N2 + 1.

%%d prt__break_args(gr::in,int::in,treeL::out,int::out)

prt__break_args([X],[nobreak(Tree,')')],N2) :-
	prt__term_tree(X,999,Tree,N1),
	N2 is N1 + 1.
prt__break_args([X1,X2|XL],[break(Tree,',')|TreeL],N3) :-
	prt__term_tree(X1,999,Tree,N1),
	prt__break_args([X2|XL],TreeL,N2),
	N3 is N1 + N2 + 1.

%%d prt__list_tree(grL::in,fr::in,int::in,grL::out,int::out)

prt__list_tree([],Tree,N1,[nobreak(Tree,']')],N2) :-
	N2 is N1 + 1.
prt__list_tree([X|XL],Tree1,N1,[break(Tree1,',')|TreeL],N4) :-
	prt__term_tree(X,999,Tree2,N2),
	prt__list_tree(XL,Tree2,N2,TreeL,N3),
	N4 is N1 + N3 + 1.
prt__list_tree(X,Tree1,N1,TreeL,N3) :-
	\+ lst__list_form(X),
	prt__term_tree(X,999,Tree2,N2),
	TreeL = [break(Tree1,'|'),nobreak(Tree2,']')],
	N3 is N1 + N2 + 2.

%%d prt__infix(gr::in,int::out,int::out,int::out)

prt__infix(Op,Prec1,Prec2,Prec1) :-
	current_op(Prec1,xfy,Op),
	Prec2 is Prec1 - 1.
prt__infix(Op,Prec1,Prec1,Prec2) :- 
	current_op(Prec1,yfx,Op),
	Prec2 is Prec1 - 1.
prt__infix(Op,Prec1,Prec2,Prec2) :-
	current_op(Prec1,xfx,Op),
	Prec2 is Prec1 - 1.

%%d prt__prefix(gr::in,int::out,int::out)

prt__prefix(Op,Prec,Prec) :-
	current_op(Prec,fy,Op).
prt__prefix(Op,Prec1,Prec2) :-
	current_op(Prec1,fx,Op),
	Prec2 is Prec1 - 1.

%%d prt__postfix(gr::in,int::out,int::out)

prt__postfix(Op,Prec,Prec) :-
	current_op(Prec,yf,Op).
prt__postfix(Op,Prec1,Prec2) :-
	current_op(Prec1,xf,Op),
	Prec2 is Prec1 - 1.

%%d prt__parenthesize(int::in,int::in,tree::in,int::in,tree::out,int::out)

prt__parenthesize(Prec1,Prec2,Tree1,N1,Tree2,N2) :-
	(	Prec2 =< Prec1 ->
		Tree2 = Tree1,
		N2 = N1
	;	N2 is N1 + 2,			% 2 for '(' and ')'
		Tree2 = node(parenthesis(Tree1),N2)
	).

%%d prt__linear(tree::in)

prt__linear(node(constant(Name),_)) :-
	writeq(Name).
prt__linear(node(structure(Name,_,TreeL),_)) :-
	writeq(Name),
	write('('),
	prt__linearL(TreeL).
prt__linear(node(list(TreeL),_)) :-
	write('['),
	prt__linearL(TreeL).
prt__linear(node(parenthesis(Tree),_)) :-
	write('('),
	prt__linear(Tree),
	write(')').
prt__linear(node(infix(Name,_,Tree1,Tree2),_)) :-
	prt__linear(Tree1),
	(	Name = (:) ->
		write(:),
		(	Tree1 = node(constant(_),_) ->
			true
		;	write(' ')
		)
	;	write(' '),
		writeq(Name),
		write(' ')
	),
	prt__linear(Tree2).
prt__linear(node(prefix(Name,_,Tree),_)) :-
	writeq(Name), 
	(	prt__prefix_nolayout(Name) ->
		true
	;	write(' ')
	),
	prt__linear(Tree).
prt__linear(node(postfix(Name,_,Tree),_)) :-
	prt__linear(Tree),
	write(' '),
	writeq(Name).

%%d prt__linearL(treeL::in)

prt__linearL([]).
prt__linearL([nobreak(Tree,Sep)|TreeL]) :-
	prt__linear(Tree),
	write(Sep),
	prt__linearL(TreeL).
prt__linearL([break(Tree,Sep)|TreeL]) :-
	prt__linear(Tree),
	write(Sep),
	prt__linearL(TreeL).

%
% The model of the screen:
%
% +---+---+--------------------------------------------------------+---+
% | 0 | 1 |                                                        | R |
% +---+---+--------------------------------------------------------+---+
%      <--------- screen ----------------------------------------->
%
% +---+---+--------+---+-------+------------+---+------------------+---+
% | 0 | 1 |        | L | L + 1 |            | P |                  | R |
% +---+---+--------+---+-------+------------+---+------------------+---+
%                       <----- screen ---------------------------->
%                                            <---- write --------->
%
% At the beginning: L = 0 and P = 1
%

%%d prt__write_tree(tree::in,int::in,int::in,int::in,int::out)

prt__write_tree(node(Tree,N),L,P1,R,P2) :-
	(	N =< R - P1 ->
		prt__linear(node(Tree,N)),
		P2 is P1 + N
	;	prt__non_linear(node(Tree,N),L,P1,R,P2)
	).

%%d prt__non_linear(tree::in,int::in,int::in,int::in,int::out)

prt__non_linear(node(constant(Name),N),L,P1,_,P2) :-
	prt__nl(L,P1),
	writeq(Name),
	P2 is L + N + 1.
prt__non_linear(node(structure(Name,N,TreeL),_),L1,P1,R,P3) :-
    	prt__nl(L1,P1),
    	writeq(Name), write('('),
	prt__indent(I),
	L2 is (L1 + I) mod R,
	P2 is L1 + N + 2,
	prt__write_treeL(TreeL,L2,P2,R,P3).
prt__non_linear(node(list(TreeL),_),L1,P1,R,P3) :-
	prt__nl(L1,P1),
    	write('['),
	P2 is L1 + 2,
	prt__indent(I),
	L2 is (L1 + I) mod R,
	prt__write_treeL(TreeL,L2,P2,R,P3).
prt__non_linear(node(parenthesis(Tree),_),L1,P1,R,P4) :-
	prt__nl(L1,P1),
    	write('('),
	prt__indent(I),
	L2 is (L1 + I) mod R,
	P2 is L1 + 2,
	prt__write_tree(Tree,L2,P2,R,P3),
	write(')'),
	P4 is P3 + 1.
prt__non_linear(node(infix(Name,N,Tree1,Tree2),_),L1,P1,R,P7) :-
	(	prt__no_break(Name) ->	% Try it on the next line.
		prt__nl(L1,P1),
    		P2 is (L1 + 1) mod R
	;	P2 = P1
	),
	prt__write_tree(Tree1,L1,P2,R,P3),
	(	Name = (:) ->		% Colon is a special case.
		write(:),
		P5 is P3 + 1
	;	N =< 2 ->		% Small operators on the same line.
		write(' '),
		writeq(Name),
		P5 is P3 + N + 1
	;	prt__write_space(P3,R,P4),
		prt__writeq_atom(Name,N,L1,P4,R,P5)
	),
	(	current_op(_,yfx,Name),	% Force a line break.
		Tree2 = node(_,Size),
		R - P5 < Size ->
		P6 = R
	;	prt__write_space(P5,R,P6)
	),
	(	prt__indent_infix(Name) -> 
		prt__indent(I),
		L2 is (L1 + I) mod R
	;	L2 = L1
	),
	prt__write_tree(Tree2,L2,P6,R,P7).
prt__non_linear(node(prefix(Name,N,Tree),_),L,P1,R,P5) :-
	(	prt__no_break(Name) ->
		prt__nl(L,P1),
		P2 is (L + 1) mod R
	;	P2 = P1
	),
	prt__writeq_atom(Name,N,L,P2,R,P3),
	(	prt__prefix_nolayout(Name) ->
		P4 = P3
	;	prt__write_space(P3,R,P4)
	),
	prt__write_tree(Tree,L,P4,R,P5).
prt__non_linear(node(postfix(Name,N,Tree),_),L,P1,R,P4) :-
	prt__write_tree(Tree,L,P1,R,P2),
	prt__write_space(P2,R,P3),
	prt__writeq_atom(Name,N,L,P3,R,P4).

%%d prt__write_treeL(treeL::in,int::in,int::in,int::in,int::out)

prt__write_treeL([],_,P,_,P).
prt__write_treeL([nobreak(Tree,Sep)|TreeL],L,P1,R,P4) :-
	prt__write_tree(Tree,L,P1,R,P2),
	write(Sep),
	P3 is P2 + 1,
	prt__write_treeL(TreeL,L,P3,R,P4).
prt__write_treeL([break(Tree,Sep)|TreeL],L,P1,R,P2) :-
	prt__write_tree(Tree,L,P1,R,_),
	write(Sep),
	prt__write_treeL(TreeL,L,R,R,P2).	% force a line break

%%d prt__write_space(int::in,int::in,int::out)

prt__write_space(P1,R,P2) :-
	(	P1 < R ->
		write(' '),
		P2 is P1 + 1
	;	P2 = P1
	).

%%d prt__writeq_atom(gr::in,int::in,int::in,int::in,int::in,int::out)

prt__writeq_atom(Name,N,L,P1,R,P2) :-
	(	R - P1 < N ->
		prt__nl(L,P1),
		writeq(Name),
		P2 is L + N + 1
	;	writeq(Name),
		P2 is P1 + N
	).

%%d prt__write_atom(gr::in,int::in,int::in,int::in,int::in,int::out)

prt__write_atom(Name,N,L,P1,R,P2) :-
	(	R - P1 < N ->
		prt__nl(L,P1),
		write(Name),
		P2 is L + N + 1
	;	write(Name),
		P2 is P1 + N
	).

%%d prt__nl(int::in,int::in)

prt__nl(L,P) :- 
	(	P is L + 1 -> 
		true
	; 	nl, 
		tab(L)
	).

%%d prt__fact(gr::in,gr::in,gr::in,gr::in)

prt__fact(Kind,Ref,X,Y) :-
	nl, write(':- '),
	write(Kind),
	write('('),
	writeq(Ref),
	write(','), nl,
	prt__write(X),
	(	Y = 'DUMMY' ->
		true
	;	write(','), nl,
		prt__write(Y)
	),
	nl, write(').'), nl.

%%d prt__pred_def(gr::in,int::in,gr::in)

prt__pred_def(Name,N,X) :-
	nl, write(':- definition_pred('),
	write(Name), write(','), write(N), write(','), nl,
	prt__write(X,1), nl,
	write(').'), nl.

%%d prt__definition_fun(gr::in,gr::in,gr::in,gr::in)

prt__definition_fun(Name,N,X,Refex,Refuni) :-
	nl, write(':- definition_fun('),
	write(Name), write(','), write(N), write(','), nl,
	prt__write(X,1), write(','), nl,
	write(' existence by '), write(Refex), write(','), nl,
	write(' uniqueness by '), write(Refuni), nl,
	write(').'), nl.

% prt.pl ends here

