%   Author: Robert F. Staerk <robert.staerk@unifr.ch> 
%  Created: Sun Mar 22 15:48:24 1998 
% Filename: sim.pl 
% Abstract: Simplifying proofs

sim__expression_size($(_),1).
sim__expression_size([_|ExprL],N2) :-
	sim__expression_sizeL(ExprL,N1),
	N2 is N1 + 1.
sim__expression_size(@(_,V,Expr),N3) :-
	sim__varL_size(V,N1),
	sim__expression_size(Expr,N2),
	N3 is N1 + N2 + 1.

sim__expression_sizeL([],0).
sim__expression_sizeL([Expr|ExprL],N3) :-
	sim__expression_size(Expr,N1),
	sim__expression_sizeL(ExprL,N2),
	N3 is N1 + N2.

sim__varL_size([],0).
sim__varL_size([_|L],N2) :-
	sim__varL_size(L,N1),
	N2 is N1 + 1.

sim__derivation_size([],0).
sim__derivation_size([Step|Deriv],N3) :-
	sim__step_size(Step,N1),
	sim__derivation_size(Deriv,N2),
	N3 is N1 + N2.

sim__step_size(by(Form,_),N2) :-
	sim__expression_size(Form,N1),
	N2 is N1 + 1.
sim__step_size([Tag|FormL],N) :-
	sim__expression_size([Tag|FormL],N).
sim__step_size(@(Tag,VL,Form),N) :-
	sim__expression_size(@(Tag,VL,Form),N).
sim__step_size(assume(Form1,Deriv,Form2),N4) :-
	sim__expression_size(Form1,N1),
	sim__derivation_size(Deriv,N2),
	sim__expression_size(Form2,N3),
	N4 is N1 + N2 + N3 + 1.
sim__step_size(cases(CaseL,Form),N3) :-
	sim__caseL_size(CaseL,N1),
	sim__expression_size(Form,N2),
	N3 is N1 + N2 + 1.
sim__step_size(exist(NameL,Form1,Deriv,Form2),N5) :-
	sim__varL_size(NameL,N1),
	sim__expression_size(Form1,N2),
	sim__derivation_size(Deriv,N3),
	sim__expression_size(Form2,N4),
	N5 is N1 + N2 + N3 + N4 + 1.
sim__step_size(induction(FormL,StepL),N3) :-
	sim__expression_sizeL(FormL,N1),
	sim__induction_step_sizeL(StepL,N2),
	N3 is N1 + N2 + 1.
sim__step_size(contra(Form,Deriv),N3) :-
	sim__expression_size(Form,N1),
	sim__derivation_size(Deriv,N2),
	N3 is N1 + N2 + 1.
sim__step_size(indirect([~,Form],Deriv),N3) :-
	sim__expression_size(Form,N1),
	sim__derivation_size(Deriv,N2),
	N3 is N1 + N2 + 1.

sim__caseL_size([],0).
sim__caseL_size([case(Form,Deriv)|CaseL],N4) :-
	sim__expression_size(Form,N1),
	sim__derivation_size(Deriv,N2),
	sim__caseL_size(CaseL,N3),
	N4 is N1 + N2 + N3 + 1.

sim__induction_step_size(step(NameL,FormL,Deriv,Form),N5) :-
	sim__varL_size(NameL,N1),
	sim__expression_sizeL(FormL,N2),
	sim__derivation_size(Deriv,N3),
	sim__expression_size(Form,N4),
	N5 is N1 + N1 + N2 + N3 + N4 + 1.
	
sim__induction_step_sizeL([],0).
sim__induction_step_sizeL([Step|StepL],N3) :-
	sim__induction_step_size(Step,N1),
	sim__induction_step_sizeL(StepL,N2),
	N3 is N1 + N2.




% sim.pl ends here
