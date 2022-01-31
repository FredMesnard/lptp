/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 6/11/95, 9:58 PM */
/* Updated: Mon Dec 28 20:24:14 1998 */
/* Filename: tex.pl */
/* Abstract: TeX output. */

% We use a TeX-hack for breaking logical formulas at the right places. A
% formula should be broken at positions which are not very deep in the
% formula. But TeX does not know about the depth of a formula. Therefore we
% have to inform TeX about the depth of a formula. For instance, the formula
% "a & b -> c \/ d" is translated into "\1 a\land b\2\to\1 c\lor d\2". The
% macro \1 tells TeX that it goes down one level; the macro \2 tells TeX
% that it goes up one level (cf. proofmacros.tex and 'TeX__bp_formula').
% Thus the formula "a & b -> c \/ d" is broken after -> and not around & or
% \/. Terms are treated differently (cf. 'TeX_term').

%%d 'TeX__non_tt_symbol'(gr::in)

% These symbols are printed in math mode and not in typewriter style.

'TeX__non_tt_symbol'(.).
'TeX__non_tt_symbol'(<).
'TeX__non_tt_symbol'(*).
'TeX__non_tt_symbol'(/).
'TeX__non_tt_symbol'(+).
'TeX__non_tt_symbol'(-).
'TeX__non_tt_symbol'([]).

%%d 'TeX__special_op'(gr::in,gr::out)

% A symbol '!xxx' must be declared as operator in op.pl and as TeX macro \xxx
% in proofmacros.tex!

'TeX__special_op'(=<,2,'!leq').
'TeX__special_op'(sub,2,'!sub').
'TeX__special_op'(**,2,'!app').
'TeX__special_op'(is,2,'!is').
'TeX__special_op'($,2,'!$').
'TeX__special_op'(@<,2,<).
'TeX__special_op'(@=<,2,'!leq').
'TeX__special_op'(@+,2,+).
'TeX__special_op'(@*,2,*).
'TeX__special_op'(//,2,'!apply').
'TeX__special_op'(#+,2,+).
'TeX__special_op'(#-,2,-).
'TeX__special_op'(#-,1,-).
'TeX__special_op'(#*,2,*).
'TeX__special_op'(#<,2,<).
'TeX__special_op'(#=<,2,'!leq').

%%d 'TeX__special_pred'(gr::out,gr::out)

'TeX__special_pred'(<>,'!neq').
'TeX__special_pred'(gr,gr).

%%d 'TeX__term'(tm::in,gr::out)

'TeX__term'($(Name),X) :-			% variables
	'TeX__var'(Name,X).
'TeX__term'([n(Name,_)|TermL],X) :-		% constructors in typewriter
	(	'TeX__special_op'(Name,_,Y) ->
		true
	;	'TeX__atom_tt'(Name,Y)
	),
	'TeX__termL'(TermL,XL),
	X =.. [Y|XL].
'TeX__term'([d(Name,N)|TermL],X) :-		% defined predicates in italic
	(	'TeX__special_op'(Name,N,Y) ->
		true
	;	'TeX__atom_it'(Name,Y)
	),
	'TeX__termL'(TermL,XL),
	X =.. [Y|XL].
'TeX__term'([f(Name,N)|TermL],X) :-		% defined functions in italic
	(	'TeX__special_op'(Name,N,Y) ->
		true
	;	'TeX__atom_it'(Name,Y)
	),
	'TeX__termL'(TermL,XL),
	X =.. [Y|XL].
'TeX__term'([=,Term|TermL],X2) :-		% equations
	'TeX__term'(Term,X1),
	'TeX__term_eq'(TermL,X1,X2).
'TeX__term'([Tag|TermL],X) :-			% special symbols in terms
	'TeX__special_pred'(Tag,Y),
	'TeX__termL'(TermL,XL),
	X =.. [Y|XL].


%%d 'TeX__termL'(tmL::in,grL::out)

'TeX__termL'([],[]).
'TeX__termL'([Term|TermL],[X|XL]) :-
	'TeX__term'(Term,X),
	'TeX__termL'(TermL,XL).

%%d 'TeX__term_eq'(gr::in,expL::in,gr::in,gr::out)

'TeX__term_eq'([],X,X).
'TeX__term_eq'([Term|TermL],X1,X4) :-
	'TeX__term'(Term,X2),
	X3 =.. ['!eq',X1,X2],
	'TeX__term_eq'(TermL,X3,X4).

%%d 'TeX__atom_tt'(gr::in,gr::out)

'TeX__atom_tt'(X,Y) :- 
	(	'TeX__non_tt_symbol'(X) ->
		Y = X
	;	concat_atom(['!Tt{',X ,'}'],Y)
	).

%%d 'TeX__atom_it'(gr::in,gr::out)

'TeX__atom_it'(X,Y) :- 
	(	'TeX__non_tt_symbol'(X) ->
		Y = X
	;	 concat_atom(['!It{',X ,'}'],Y)
	).

%%d 'TeX__is_digit'(int::in)

'TeX__is_digit'(X) :- 48 =< X, X =< 57.

% name('_{}',[95,123,125]).
% name('!It{',[33,73,116,123]).

%%d 'TeX__var'(gr::in,gr::out)

'TeX__var'(X,Y) :-
	(	integer(X) -> 
		concat_atom(['!v{',X,'}'],Y)
	;	name(X,L1),
		lst__reverse(L1,L2),
		L2 = [X1|L3],
		'TeX__is_digit'(X1) ->
		(	L3 = [X2|L4],
			'TeX__is_digit'(X2) ->
			lst__reverse([125,X1,X2,123,95|L4],L5)
		;	lst__reverse([X1,95|L3],L5)		
		),
		name(Y,L5)
	;	Y = X
	).

%%d 'TeX__varL'(grL::in,grL::out)

'TeX__varL'([],[]).
'TeX__varL'([X|XL],[Y|YL]) :-
	'TeX__var'(X,Y),
	'TeX__varL'(XL,YL).

%%d 'TeX__bp_formula'(fml::in)

'TeX__bp_formula'(Form) :-
	write('!0'),
	'TeX__bp_formula'(Form,1200).

%%d 'TeX__bp_formula'(fml::in,int::in)

'TeX__bp_formula'([Op1,Form],N1) :-
	'TeX__bp_unary_op'(Op1,Op2),
	prt__prefix(Op1,N2,N3),
	'TeX__bp_left'(N1,N2),
	write(Op2),
	'TeX__bp_formula'(Form,N3),	
	'TeX__bp_right'(N1,N2).
'TeX__bp_formula'([Op1,Form1,Form2],N1) :-
	'TeX__bp_binary_op'(Op1,Op2),
	prt__infix(Op1,N2,N3,N4),
	'TeX__bp_left'(N1,N2),
	'TeX__bp_formula'(Form1,N3),
	write(Op2),
	'TeX__bp_formula'(Form2,N4),	
	'TeX__bp_right'(N1,N2).
'TeX__bp_formula'([&],_) :- write('!top').
'TeX__bp_formula'([\/],_) :- write('!bot').
'TeX__bp_formula'([Op1,Form|FormL],N1) :-
	'TeX__bp_associative_op'(Op1,Op2),
	current_op(N2,_,Op1),
	'TeX__bp_left'(N1,N2),
	N3 is N2 - 1,
	'TeX__bp_formula'(Form,N3),
	'TeX__bp_list'(FormL,Op2,N3),
	'TeX__bp_right'(N1,N2).
'TeX__bp_formula'([Tag|FormL],_) :-
	\+ 'TeX__bp_special'(Tag),
	'TeX__term'([Tag|FormL],X),
	write(X).
'TeX__bp_formula'(@(Tag1,Var1L,Form),N) :-
	'TeX__bp_quantifier'(Tag1,Tag2),
	'TeX__varL'(Var1L,Var2L),
	'TeX__bp_left'(N,900),
	write(Tag2), write(Var2L), write('!,'),
	'TeX__bp_formula'(Form,900),	
	'TeX__bp_right'(N,900).

%%d 'TeX__bp_list'(fmlL::in,gr::in,int::in)

'TeX__bp_list'([],_,_).
'TeX__bp_list'([Form|FormL],Op,N) :-
	write(Op),
	'TeX__bp_formula'(Form,N),
	'TeX__bp_list'(FormL,Op,N).

%%d 'TeX__bp_left'(int::in,int::in)

'TeX__bp_left'(N1,N2) :-
	write('!1'),
	(	N1 < N2 -> 
		write('(')
	; 	true
	).

%%d 'TeX__bp_right'(int::in,int::in)

'TeX__bp_right'(N1,N2) :-
	(	N1 < N2 -> 
		write(')')
	; 	true
	),
	write('!2').

%%d 'TeX__bp_quantifier'(gr::in,gr::out)

'TeX__bp_quantifier'(all,'!all').
'TeX__bp_quantifier'(ex,'!ex').

%%d 'TeX__bp_unary_op'(gr::in,gr::out)

'TeX__bp_unary_op'(~,'!lnot ').
'TeX__bp_unary_op'(def,'!D ').
'TeX__bp_unary_op'(succeeds,'!S ').
'TeX__bp_unary_op'(fails,'!F ').
'TeX__bp_unary_op'(terminates,'!T ').

%%d 'TeX__bp_binary_op'(gr::in,gr::out)

'TeX__bp_binary_op'(=>,'!to ').
'TeX__bp_binary_op'(<=>,'!eqv ').

%%d 'TeX__bp_associative_op'(gr::in,gr::out)

'TeX__bp_associative_op'(&,'!land ').
'TeX__bp_associative_op'(\/,'!lor ').

%%d 'TeX__bp_special'(gr::in)

'TeX__bp_special'(X) :- 'TeX__bp_unary_op'(X,_).
'TeX__bp_special'(X) :- 'TeX__bp_binary_op'(X,_).
'TeX__bp_special'(X) :- 'TeX__bp_associative_op'(X,_).

%%d 'TeX__preamble'(gr::in)

'TeX__preamble'(Path) :-
	write(\),
	write('input '),
	io__expand($(tex)/'proofmacros.tex',Name1),
	write(Name1), nl,
	io__path_last(Path,Name2),
	write('!title{'),
	write(Name2),
	write('}'), nl.

%%d 'TeX__postamble'

'TeX__postamble' :-
	nl, write('!end'), nl.

%%d 'TeX__write_dollar'(fml::in)

'TeX__write_dollar'(Form) :-
	write('$'),
	'TeX__bp_formula'(Form),
	write('$').

%%d 'TeX__write_dollar_dot'(fml::in)

'TeX__write_dollar_dot'(Form) :-
	'TeX__write_dollar'(Form),
	write('.').

%%d 'TeX__write_braces'(fml::in)

'TeX__write_braces'(Form) :-
	write('{'),
	'TeX__bp_formula'(Form),
	write('}').

%%d 'TeX__write_dollarL'(fmlL::in)

'TeX__write_dollarL'([]) :-
	write('{none}').
'TeX__write_dollarL'([Form|FormL]) :-
	write('{'),
	'TeX__write_dollar'(Form),
	'TeX__write_dollarL_comma'(FormL).

%%d 'TeX__write_dollarL_comma'(fml::in)

'TeX__write_dollarL_comma'([]) :-
	write('}').
'TeX__write_dollarL_comma'([Form|FormL]) :-
	write(' and '),
	'TeX__write_dollar'(Form),
	'TeX__write_dollarL_comma'(FormL).

%%d 'TeX__write_fact'(gr::in,gr::in,fml::in,drv::in)
	
'TeX__write_fact'(Kind,Ref,Form,Deriv) :-
	nl, write(!), write(Kind),
	write('{'), write(Ref), write('}'),
	'TeX__write_braces'(Form), nl,
	(	Deriv = [] ->
		true
	;	write('!Pr{'),
		'TeX__write_derivation'(Deriv),
		write('}'), nl,
		write('!Epr'), nl
	).

%%d 'TeX__write_derivation'(drv::in)

'TeX__write_derivation'([]).
'TeX__write_derivation'([Step|Deriv]) :-
	'TeX__write_derivation_step'(Step),
	'TeX__write_derivation'(Deriv).

%%d 'TeX__write_derivation_step'(dstp::in)

'TeX__write_derivation_step'([Tag|FormL]) :-
	nl, 'TeX__write_dollar_dot'([Tag|FormL]).
'TeX__write_derivation_step'(@(Tag,VarL,Form)) :-
	nl, 'TeX__write_dollar_dot'(@(Tag,VarL,Form)).
'TeX__write_derivation_step'(assume(Form1,Deriv,Form2)) :-
	nl, write('!Ass'),
	'TeX__write_braces'(Form1),
	'TeX__write_derivation'(Deriv), nl,
	write('!Eass'),
	'TeX__write_braces'([=>,Form1,Form2]).
'TeX__write_derivation_step'(contra(Form,Deriv)) :-
	nl, write('!Con'),
	'TeX__write_braces'(Form),
	'TeX__write_derivation'(Deriv), nl,
	write('!Econ'),
	'TeX__write_braces'([~,Form]).
'TeX__write_derivation_step'(cases(CaseL,Form)) :-
	'TeX__write_cases'(CaseL), nl,
	write('!Fin'),
	'TeX__write_braces'(Form).
'TeX__write_derivation_step'(indirect([~,Form],Deriv)) :-
	nl, write('!Dir'),
	'TeX__write_braces'([~,Form]),
	'TeX__write_derivation'(Deriv), nl,
	write('!Edir'),
	'TeX__write_braces'(Form).
'TeX__write_derivation_step'(exist(VarL,Form1,Deriv,Form2)) :-
	nl, write('!Ex'),
	'TeX__varL'(VarL,XL),
	write(XL),
	'TeX__write_braces'(Form1),
	'TeX__write_derivation'(Deriv), nl,
	write('!Eex'),
	'TeX__write_braces'(Form2).
'TeX__write_derivation_step'(by(Form,X)) :-
	nl, 'TeX__write_dollar'(Form),
	'TeX__write_by'(X).
'TeX__write_derivation_step'(induction(FormL,StepL)) :-
	nl, write('!Ind'),
	'TeX__write_dollarL'(FormL),
	'TeX__write_induction_steps'(StepL),
	nl,write('!Eind').

%%d 'TeX__write_cases'(casL::in)

'TeX__write_cases'([]).
'TeX__write_cases'([case(Form,Case)|CaseL]) :-
	nl, write('!Cas'),
	'TeX__write_braces'(Form),
	'TeX__write_derivation'(Case), nl,
	write('!Ecas'),
	'TeX__write_cases'(CaseL).

%%d 'TeX__write_induction_steps'(istpL::in)

'TeX__write_induction_steps'([]).
'TeX__write_induction_steps'([step(_,FormL,Deriv,Form)|StepL]) :-
	nl, write('!Stp'),
	'TeX__write_dollarL'(FormL),
	'TeX__write_derivation'(Deriv), nl,
	write('!Estp'),
	'TeX__write_braces'(Form),
	'TeX__write_induction_steps'(StepL).

%%d 'TeX__write_by'(gr::in)

'TeX__write_by'(X) :-
	(	X = comment(Y) ->
		write('! by~'),
		write(Y),
		write('.')
	;	X = gap ->
		write('! by~{!bf GAP}.')
	;	X = theorem(Ref) ->
		write('!by{Theorem}{'),
		write(Ref),
		write('}.')
	;	X = lemma(Ref) ->
		write('!by{Lemma}{'),
		write(Ref),
		write('}.')
	;	X = corollary(Ref) ->
		write('!by{Corollary}{'),
		write(Ref),
		write('}.')
	;	X = axiom(Ref) ->
		write('!by{Axiom}{'),
		write(Ref),
		write('}.')
	;	(	X = elimination(Name,N)
		; 	X = introduction(Name,N)
		;	X = existence(Name,N)
		;	X = uniqueness(Name,N)
		) ->
		write('!by{Definition}{'),
		write(Name),
		write(/),
		write(N),
		write('}.')
	;	write('! by~'),
		write(X), 
		write('.')
	).

%%d 'TeX__write_def'(gr::in,int::in,fml::in)

'TeX__write_def'(Name,N,Form) :-
	nl, write('!definition{'),
	write(Name),
	write(/), 
	write(N), 
	write('}'),
	'TeX__write_braces'(Form), nl.

% tex.pl ends here

