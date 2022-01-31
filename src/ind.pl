/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: Fri Dec  2 15:52:53 1994 */
/* Updated: Mon Feb 15 14:40:52 1999 */
/* Filename: ind.pl */
/* Abstract: The induction scheme. */

% %%d ind__tactic_arg(gr::in)
% 
% ind__tactic_arg(arg(Tactic,Sub2,VarL,N)) :-
% 	(	Tactic = plain
% 	; 	Tactic = tactic(V,Gamma),
% 	 	obj__varL(V),
% 		obj__formulaL(Gamma)
% 	),
% 	obj__substitution2(Sub2),
% 	obj__varL(VarL),
% 	integer(N).

%%d ind__gen_err(gr::in,fmlL::in,istpL::out)

% Tactic in [plain,tactic(V,Gamma)]

ind__gen_err(Tactic,FormL,StepL) :-
	(	ind__make_sub(FormL,U,V,K) ->
		(	ind__steps(FormL,arg(Tactic,U,V,K),[],StepL) ->
			true
		;	ctl__error([cannot,create,induction,scheme]),
			StepL = []
		)
	;	i2e__expressionL(FormL,XL),
		ctl__error([XL,cannot,be,used,for,induction]),
		StepL = []
	).

%%d ind__make_sub(fmlL::in,sub2::out,varL::out,int::out)

% ind__make_sub(_,U,V,K) and sub(Name,N,BV,Form) is in U then
%   if $(X) is free in Form and X is not in BV then X is in V,
%   if $(I) is free in Form and I is not in BV then I < K.

ind__make_sub([],[],[],0).
ind__make_sub([@(all,BV,[=>,[succeeds,[n(Name,N)|TermL]],Form])|FormL],
		[sub(Name,N,BV,Form)|U],V2,K2) :-
	obj__make_varL(BV,TermL),
	ind__make_sub(FormL,U,V1,K1),
	\+ obj__domain2(Name,N,U),
	eq__add_max_free_bound(Form,BV,K1,V1,K2,V2).

%%d ind__steps(fmlL::in,itac::in,istpL::in,istpL::out)

ind__steps([@(all,_,[=>,[succeeds,[Tag|_]],_])|FormL],X,Step1L,Step3L) :-
	cmp__clauses_err(Tag,ClauseL),
	ind__clauses(ClauseL,X,Step2L,Step3L),
	ind__steps(FormL,X,Step1L,Step2L).
ind__steps([],_,StepL,StepL).

%%d ind__clauses(clsL::in,itac::in,istpL::in,istpL::out)

ind__clauses([Clause|ClauseL],X,Step1L,Step3L) :-
	ind__clause(Clause,X,Step2L,Step3L),
	ind__clauses(ClauseL,X,Step1L,Step2L).
ind__clauses([],_,StepL,StepL).

%%d ind__clause(cl::in,itac::in,istpL::in,istp::out)

ind__clause(clause(Atom,Goal,V/K),X,Step1L,Step2L) :-
	cmp__succeeds_goal(Goal,Form),
	(	ind__normal_body(Form) ->
		ind__formula_to_list(Form,FormL),
		ind__normal_clause(FormL,Atom,V,K,X,Step),
		Step2L = [Step|Step1L]
	;	X = arg(_,U,_,_),
		ind__dnf_formula(Form,U,FormLL),
		ind__normal_clauses(FormLL,Atom,V,K,X,Step1L,Step2L)
	).

%%d ind__normal_clauses(fmlLL::in,atm::in,varL::in,int::in,itac::in,istpL::in,istpL::out)

ind__normal_clauses([FormL|FormLL],Atom,V,K,X,Step1L,[Step|Step2L]) :-
	ind__normal_clause(FormL,Atom,V,K,X,Step),
	ind__normal_clauses(FormLL,Atom,V,K,X,Step1L,Step2L).
ind__normal_clauses([],_,_,_,_,StepL,StepL).

%%d ind__normal_clause(fmlL::in,atm::in,varL::in,int::in,itac::in,istp::out)

ind__normal_clause(Form1L,Atom1,V1,K1,arg(Tactic,U,V2,K2),Step) :-
	cmp__maximum(K1,K2,K3),
	(	Tactic = tactic(V3,_) ->
		lst__append_set(V3,V2,V4)
	;	V4 = V2
	),
	eq__apply_extend(V1,V4,[],K3,BV,_,Sub,K4),
	eq__apply_sub_qf(Atom1,Sub,Atom2),
	ind__apply([succeeds,Atom2],U,K4,Form),
	eq__apply_sub_qfL(Form1L,Sub,Form2L),
	ind__apply_add(Form2L,U,K4,Form2L,Form3L),
	ind__tactic(Tactic,Form3L,Form,Deriv),
	Step = step(BV,Form3L,Deriv,Form).

%%d ind__tactic(gr::in,fml::in,drv::out)

ind__tactic(plain,_,_,[by([\/],gap)]).
ind__tactic(tactic(V1,Gamma1),FormL,Form,Deriv) :-
	pr__add_assumptionL(FormL,V1,Gamma1,V2,Gamma2),
	tac__conclusion(Form,V2,Gamma2,d,Deriv).

%%d ind__apply(fml::in,sub2::in,int::in,fml::out)

ind__apply([succeeds,[n(Name,N)|TermL]],U,K,Form2) :-
	lst__member(sub(Name,N,V1,Form1),U),
	eq__make_sub(V1,TermL,V2,Sub),
	eq__apply(Form1,V2,Sub,K,Form2).
	
%%d ind__apply_add(fmlL::in,sub2::in,int::in,fmlL::in,fmlL::out)

ind__apply_add([],_,_,FormL,FormL).
ind__apply_add([Form|FormL],U,K,Form2L,Form4L) :-
	(	ind__apply(Form,U,K,Form2) ->
		Form4L = [Form2|Form3L]
	;	Form4L = Form3L
	),
	ind__apply_add(FormL,U,K,Form2L,Form3L).

%%d ind__normal_body(fml::in)

ind__normal_body([&|FormL]) :- 
	ind__normalL(FormL).
ind__normal_body(Form) :- 
	ind__literal_form(Form).

%%d ind__normalL(fmlL::in)

ind__normalL([]).
ind__normalL([Form|FormL]) :-
	ind__literal_form(Form),
	ind__normalL(FormL).

%%d ind__literal_form(fml::in)

ind__literal_form([succeeds,_]).
ind__literal_form([fails,_]).
ind__literal_form([=,_,_]).
ind__literal_form([<>,_,_]).

%%d ind__formula_to_list(fml::in,fmlL::out)
	
ind__formula_to_list(Form,FormL) :-
	(	obj__conjunction_form(Form) ->
		Form = [&|FormL]
	;	FormL = [Form]
	).

%%d ind__free(fml::in,sub2::in)

ind__free([=,_,_],_).
ind__free([<>,_,_],_).
ind__free([succeeds,[n(Name,N)|_]],U) :- 
	\+ obj__domain2(Name,N,U).
ind__free([fails,_],_).
ind__free([&|FormL],U) :-
	ind__freeL(FormL,U).
ind__free([\/|FormL],U) :-
	ind__freeL(FormL,U).

%%d ind__freeL(fmlL::in,sub2::in)

ind__freeL([],_).
ind__freeL([Form|FormL],U) :-
	ind__free(Form,U),
	ind__freeL(FormL,U).

%%d ind__dnf_formula(fml::in,sub2::in,fmlLL::out)

ind__dnf_formula(Form,U,FormLL) :-
	ind__dnf_add_formula(Form,U,[[]],FormLL).

%%d ind__dnf_add_formula(fml::in,sub2::in,fmlLL::in,fmlLL::out)

% ind__dnf_add_formula(F1,_,[[F2,...],...],[[F3,...],...]) =>
% 
% F1 & ((F2 & ... ) \/ ... ) <=> ((F3 & ... ) \/ ... )

ind__dnf_add_formula(Form1,U,Form1LL,Form2LL) :-
	(	(	ind__literal_form(Form1)
		; 	ind__free(Form1,U)
		) ->
		ind__dnf_add_atom(Form1,Form1LL,Form2LL)
	;	obj__conjunction_form(Form1) ->
		Form1 = [&|FormL],
		ind__dnf_add_con(FormL,U,Form1LL,Form2LL)
	;	obj__disjunction_form(Form1) ->
		Form1 = [\/|FormL],
		ind__dnf_add_dis(FormL,U,Form1LL,Form2LL)
	).

%%d ind__dnf_add_atom(fml::in,fmlLL::in,fmlL::out)

% ind__dnf_add_atom(F1,_,[[F2,...],...],[[F3,...],...]) =>
% 
% F1 & ((F2 & ... ) \/ ... ) <=> ((F3 & ... ) \/ ... )

ind__dnf_add_atom(_,[],[]).
ind__dnf_add_atom(Form,[Form1L|Form1LL],[Form3L|Form2LL]) :-
	(	obj__conjunction_form(Form) ->
		Form = [&|Form2L],
		lst__append(Form2L,Form1L,Form3L)
	;	Form3L = [Form|Form1L]
	),
	ind__dnf_add_atom(Form,Form1LL,Form2LL).

%%d ind__dnf_add_con(fmlL::in,sub2::in,fmlLL::in,fmlLL::out)

% ind__dnf_add_atom([F1,...],_,[[F2,...],...],[[F3,...],...]) =>
% 
% (F1 & ... ) & ((F2 & ... ) \/ ... ) <=> ((F3 & ... ) \/ ... )

ind__dnf_add_con([],_,FormLL,FormLL).
ind__dnf_add_con([Form|FormL],U,Form1LL,Form3LL) :-
	ind__dnf_add_con(FormL,U,Form1LL,Form2LL),
	ind__dnf_add_formula(Form,U,Form2LL,Form3LL).

%%d ind__dnf_add_dis(fmlL::in,sub2::in,fmlLL::in,fmlLL::out)

% ind__dnf_add_atom([F1,...],_,[[F2,...],...],[[F3,...],...]) =>
% 
% (F1 \/ ... ) & ((F2 & ... ) \/ ... ) <=> ((F3 & ... ) \/ ... )

ind__dnf_add_dis([],_,_,[]).
ind__dnf_add_dis([Form|FormL],U,FormLL,Form3LL) :-
	ind__dnf_add_formula(Form,U,FormLL,Form1LL),
	ind__dnf_add_dis(FormL,U,FormLL,Form2LL),
	lst__append(Form1LL,Form2LL,Form3LL).

%%d ind__pr_induction(varL::in,fmlL::in,fml::in,istpL::in)

ind__pr_induction(V,Gamma,FormL,DerivL) :-
	ind__gen_err(plain,FormL,StepL),
	ind__pr_induction_steps(DerivL,StepL,V,Gamma).

%%d ind__pr_induction_steps(istpL::in,istpL::in,varL::in,fmlL::in)

ind__pr_induction_steps([],[],_,_).
ind__pr_induction_steps([step(BV1,Form1L,Deriv,Form1)|DerivL],
	[step(BV2,Form2L,_,Form2)|StepL],V1,Gamma1) :-
	lst__disjoint(BV1,V1),
	(	eq__alpha(@(all,BV1,[&,Form1|Form1L]),
			  @(all,BV2,[&,Form2|Form2L])) ->
		true
	;	i2e__expressionL([Form1|Form1L],[X1|X1L]),
		i2e__expressionL([Form2|Form2L],[X2|X2L]),
		ctl__warning([mismatch,in,induction,step,
			p(X1),p(X2),p(X1L),p(X2L)])
	),
	pr__add_assumptionL(Form1L,V1,Gamma1,V2,Gamma2),
	pr__proof(Deriv,V2,Gamma2,Gamma3),
	pr__derivable_err(V2,Gamma3,Form1),
	ind__pr_induction_steps(DerivL,StepL,V1,Gamma1).

% ind.pl ends here

