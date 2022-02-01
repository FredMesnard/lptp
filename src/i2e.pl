/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 6/11/95, 9:15 PM */
/* Filename: i2e.pl */
/* Abstract: From the internal to the external representation. */

%%d i2e__arity_form(gr::in)

i2e__arity_form(n(_,_)).
i2e__arity_form(d(_,_)).
i2e__arity_form(f(_,_)).

%%d i2e__assoc_tag(gr::in)

i2e__assoc_tag(=).
i2e__assoc_tag(&).
i2e__assoc_tag(\/).

%%d i2e__expression(exp::in,gr::out)

i2e__expression($(X),? X).
i2e__expression([=|ExprL],X) :- i2e__eq(ExprL,X).
i2e__expression([&|ExprL],X) :- i2e__con(ExprL,X).
i2e__expression([\/|ExprL],X) :- i2e__dis(ExprL,X).
i2e__expression([n(Name,_)|ExprL],X) :-
	i2e__expressionL(ExprL,XL),
	X =.. [Name|XL].
i2e__expression([d(Name,_)|ExprL],X) :-
	i2e__expressionL(ExprL,XL),
	X =.. [Name|XL].
i2e__expression([f(Name,_)|ExprL],X) :-
	i2e__expressionL(ExprL,XL),
	X =.. [Name|XL].
i2e__expression([Tag|ExprL],X) :-		% ~, <>, =>, <=>, def, gr, 
	\+ i2e__arity_form(Tag),		% succeeds, fails, terminates
	\+ i2e__assoc_tag(Tag),
	i2e__expressionL(ExprL,XL),
	X =.. [Tag|XL].
i2e__expression(@(all,VarL,Expr),all X1: X2) :-
	i2e__flatten_singleton(VarL,X1),
	i2e__expression(Expr,X2).
i2e__expression(@(ex,VarL,Expr),ex X1: X2) :-
	i2e__flatten_singleton(VarL,X1),
	i2e__expression(Expr,X2).

%%d i2e__expressionL(expL::in,grL::out)

i2e__expressionL([],[]).
i2e__expressionL([Expr|ExprL],[X|XL]) :-
	i2e__expression(Expr,X),
	i2e__expressionL(ExprL,XL).

%%d i2e__eq(expL::in,gr::out)

% i2e__eq([$(1),$(2),$(3)], (?1 = ?2) = ?3).

i2e__eq([], tt).
i2e__eq([Expr|ExprL],X2) :-
	i2e__expression(Expr,X1),
	i2e__eqL(ExprL,X1,X2).

%%d i2e__eqL(expL::in,gr::in,gr::out)

i2e__eqL([],X,X).
i2e__eqL([Expr|ExprL],X1,X3) :-
	i2e__expression(Expr,X2),
	i2e__eqL(ExprL,X1 = X2,X3).

%%d i2e__con(expL::in,gr::out)

i2e__con([], tt).
i2e__con([Expr|ExprL],X2) :-
	i2e__expression(Expr,X1),
	i2e__conL(ExprL,X1,X2).

%%d i2e__conL(expL::in,gr::in,gr::out)

i2e__conL([],X,X).
i2e__conL([Expr|ExprL],X1,X3) :-
	i2e__expression(Expr,X2),
	i2e__conL(ExprL,X1 & X2,X3).

%%d i2e__dis(expL::in,gr::out)

i2e__dis([], ff).
i2e__dis([Expr|ExprL],X2) :-
	i2e__expression(Expr,X1),
	i2e__disL(ExprL,X1,X2).

%%d i2e__disL(expL::in,gr::in,gr::out)

i2e__disL([],X,X).
i2e__disL([Expr|ExprL],X1,X3) :-
	i2e__expression(Expr,X2),
	i2e__disL(ExprL,X1 \/ X2,X3).

%%d i2e__flatten_singleton(gr::in,gr::out)

i2e__flatten_singleton(X,Z) :-
	(	X = [Y] -> 
		Z = Y
	; 	Z = X
	).

%%d i2e__derivation(drv::in,gr::out)

i2e__derivation(Deriv,X) :-
	i2e__derivationL(Deriv,XL),
	i2e__flatten_singleton(XL,X).

%%d i2e__derivationL(drv::in,grL::out)

i2e__derivationL([],[]).
i2e__derivationL([Step|Deriv],[X|XL]) :-
	i2e__derivation_step(Step,X),
	i2e__derivationL(Deriv,XL).

%%d i2e__proof_form(gr::in)

i2e__proof_form(assume(_,_,_)).
i2e__proof_form(contra(_,_)).
i2e__proof_form(cases(_,_)).
i2e__proof_form(indirect(_,_)).
i2e__proof_form(exist(_,_,_,_)).
i2e__proof_form(by(_,_)).
i2e__proof_form(induction(_,_)).

%%d i2e__derivation_step(dstp::in,gr::out)

i2e__derivation_step(assume(Form1,Deriv,Form2),assume(X1,Y,X2)) :-
	i2e__expression(Form1,X1),
	i2e__expression(Form2,X2),
	i2e__derivation(Deriv,Y).
i2e__derivation_step(contra(Form,Deriv),contra(X,Y)) :-
	i2e__expression(Form,X),
	i2e__derivation(Deriv,Y).
i2e__derivation_step(indirect(Form,Deriv),indirect(X,Y)) :-
	i2e__expression(Form,X),
	i2e__derivation(Deriv,Y).
i2e__derivation_step(cases([case(Form1,Deriv1),case(Form2,Deriv2)],Form),
	cases(X1,Y1,X2,Y2,X)) :-
	i2e__expression(Form1,X1),
	i2e__expression(Form2,X2),
	i2e__expression(Form,X),
	i2e__derivation(Deriv1,Y1),
	i2e__derivation(Deriv2,Y2).
i2e__derivation_step(cases(CaseL,Form),cases(XL,X)) :-
	\+ lst__two_elements(CaseL),
	i2e__expression(Form,X),
	i2e__cases(CaseL,XL).
i2e__derivation_step(exist(VarL,Form1,Deriv,Form2),exist(X,X1,Y,X2)) :-
	i2e__flatten_singleton(VarL,X),
	i2e__expression(Form1,X1),
	i2e__expression(Form2,X2),
	i2e__derivation(Deriv,Y).
i2e__derivation_step(by(Form,Y),by(X,Y)) :-
	i2e__expression(Form,X).
i2e__derivation_step(induction(FormL,StepL),induction(XL,YL)) :-
	i2e__expressionL(FormL,XL),
	i2e__induction_steps(StepL,YL).
i2e__derivation_step(F,X) :-			% in the case of formulas
	\+ i2e__proof_form(F),
	i2e__expression(F,X).

%%d i2e__cases(casL::in,grL::out)

i2e__cases([],[]).
i2e__cases([case(Form,Deriv)|CaseL],[case(X,Y)|XL]) :-
	i2e__expression(Form,X),
	i2e__derivation(Deriv,Y),
	i2e__cases(CaseL,XL).

%%d i2e__induction_steps(istpL::in,grL::out)

i2e__induction_steps([],[]).
i2e__induction_steps([step(VarL,FormL,Deriv,Form)|StepL],
	[step(VarL,XL,X,Y)|YL]) :-
	i2e__expressionL(FormL,XL),
	i2e__derivation(Deriv,X),
	i2e__expression(Form,Y),
	i2e__induction_steps(StepL,YL).

%%d i2e__subL(sub::in,grL::out)

i2e__subL([],[]).
i2e__subL([X => Term|Sub],[X => Y|Z]) :-
	i2e__expression(Term,Y),
	i2e__subL(Sub,Z).

%%d i2e__class(cl::in,gr::out)

i2e__class(cl(Term,Part),cl(X,Y)) :-
	i2e__expression(Term,X),
	i2e__partition(Part,Y).

%%d i2e__partition(ptn::in,gr::out)

i2e__partition([],[]).
i2e__partition([Class|Part],[X|Y]) :-
	i2e__class(Class,X),
	i2e__partition(Part,Y).

%%d i2e__theorem(thm::in,gr::out)

i2e__theorem(theorem(Ref,Form,Deriv),theorem(Ref,EForm,EDeriv)) :-
	i2e__expression(Form,EForm),
	i2e__derivation(Deriv,EDeriv).
i2e__theorem(lemma(Ref,Form,Deriv),lemma(Ref,EForm,EDeriv)) :-
	i2e__expression(Form,EForm),
	i2e__derivation(Deriv,EDeriv).
i2e__theorem(corollary(Ref,Form,Deriv),corollary(Ref,EForm,EDeriv)) :-
	i2e__expression(Form,EForm),
	i2e__derivation(Deriv,EDeriv).

% i2e.el ends here

