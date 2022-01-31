/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: Fri Dec  2 15:54:48 1994 */
/* Updated: Mon Feb 22 12:53:28 1999 */
/* Filename: pr.pl (proofs) */
/* Abstract: The kernel of the system. What is a proof? */


%% Variable conventions in this file:
%%
%% Deriv	derivation
%% Form		formula
%% Gamma	list of formulas
%% V		list of variables
%% BV		list of bound variables
%% Step		step in a derivation or induction

%%c
%%c Derivations are Prolog terms of the following forms:
%%c
%%c [Step,...,Step] where each Step has of one of the following forms:
%%c 
%%c Form
%%c assume(Form,Deriv,Form)
%%c contra(Form,Deriv)
%%c cases([case(Form,Deriv),...],Form)
%%c indirect([~,Form],Deriv)
%%c exist(BV,Form,Deriv,Form)
%%c induction(FormL,[step(BV,FormL,Deriv,Form),...])
%%c by(Form,comment(_))
%%c by(Form,completion)
%%c by(Form,gap)
%%c by(Form,elimination(Name,N))
%%c by(Form,introduction(Name,N))
%%c by(Form,existence(Name,N))
%%c by(Form,uniqueness(Name,N))
%%c by(Form,theorem(_))
%%c by(Form,lemma(_))
%%c by(Form,corollary(_))
%%c by(Form,[l(N),r(N),ind,cmp,uni,thm,dis,ex])
%%c


%% The predicates in this file are correct with respect to the following
%% interpretation (Gamma1 |- Gamma2 means that every formula from the list
%% Gamma2 is derivable in classical logic from the formulas in Gamma1):
%%
%% pr__proof(Deriv,V,Gamma1,Gamma2) has to be understood as a function,
%% that given Deriv, V, Gamma1 checks Deriv and computes Gamma2.
%% 
%% pr__proof(Deriv,V,Gamma1,Gamma2) => for all Gamma3, if FV(Gamma3) is
%%   contained in V and Gamma3 |- Gamma1 then Gamma3 |- Gamma2.
%% 
%% pr__step(Deriv,V,Gamma1,Form) => for all Gamma2, if FV(Gamma2) is
%%   contained in V and Gamma2 |- Gamma1 then Gamma2 |- Form.
%% 
%% pr__derivable(V,Gamma1,Form,_) => for all Gamma2, if FV(Gamma2) is
%%   contained in V and Gamma2 |- Gamma1 then Gamma2 |- Form.
%% 
%% pr__by(_,V,Gamma1,Form1,Form2) => for all Gamma2, if FV(Gamma2) is
%%   contained in V and Gamma2 |- Gamma1 then
%%   Gamma2 |- Form1 and Gamma2 |- Form2.
%% 
%% pr__axiom(Form) => |- Form
%% 
%% pr__inconsistent(Gamma) => Gamma |- ff
%% 
%% pr__equivalent(Form1,Form2) => |- Form1 <=> Form2
%% 

%%d pr__proof(drv::in,varL::in,fmlL::in,fmlL::out)

pr__proof([],_,Gamma,Gamma).
pr__proof([Step|Deriv],V,Gamma1,Gamma2) :-
	pr__step_err(Step,V,Gamma1,Form),
	pr__proof(Deriv,V,[Form|Gamma1],Gamma2).

%%d pr__step(dstp::in,varL::in,fmlL::in,fml::out)

pr__step(Form1 by X,V,Gamma,Form2) :-			% step: by
	obj__formula(Form1),
	pr__by(X,V,Gamma,Form1,Form2),
	pr__statistics(step_by).
pr__step([Tag|FormL],V,Gamma,[Tag|FormL]) :-		% step: trivial 
	obj__formula([Tag|FormL]),
	pr__derivable_once(V,Gamma,[Tag|FormL]),
	pr__statistics(step_trivial).
pr__step(@(Tag,BV,Form),V,Gamma,@(Tag,BV,Form)) :-
	obj__formula(@(Tag,BV,Form)),
	pr__derivable_once(V,Gamma,@(Tag,BV,Form)),
	pr__statistics(step_trivial).
pr__step(assume(Form1,Deriv,Form2),V1,Gamma1,		% step: assume
	[=>,Form1,Form2]) :-
	obj__formula(Form1),
	obj__formula(Form2),
	eq__add_free(Form1,V1,V2),
	pr__proof(Deriv,V2,[Form1|Gamma1],Gamma2),
	pr__derivable_err(V2,Gamma2,Form2),
	pr__statistics(step_assume).
pr__step(cases(CaseL,Form),V,Gamma,Form) :-		% step: cases
	obj__formula(Form),
	pr__cases_formula(CaseL,FormL),
	pr__derivable_err(V,Gamma,[\/|FormL]),
	pr__cases(CaseL,V,Gamma,Form),
	pr__statistics(step_cases).
pr__step(exist(BV,Form1,Deriv,Form2),V1,Gamma,Form2) :-	% step: exist
	obj__formula(Form1),
	obj__formula(Form2),
	obj__varL(BV),
	lst__disjoint(V1,BV),
	eq__free(Form2,BV),
	pr__derivable_err(V1,Gamma,@(ex,BV,Form1)),
	eq__add_free(Form1,V1,V2),
	pr__proof(Deriv,V2,[Form1|Gamma],Gamma1),
	pr__derivable_err(V2,Gamma1,Form2),
	pr__statistics(step_exist).
pr__step(induction(FormL,StepL),V,Gamma,Form) :- 	% step: induction
	ind__pr_induction(V,Gamma,FormL,StepL),
	pr__conjunction(FormL,Form),
	pr__statistics(step_induction).
pr__step(contra(Form,Deriv),V1,Gamma1,[~,Form]) :-	% step: contra
	obj__formula(Form),
	eq__add_free(Form,V1,V2),
	pr__proof(Deriv,V2,[Form|Gamma1],Gamma2),
	pr__inconsistent(Gamma2),
	pr__statistics(step_contra).
pr__step(indirect([~,Form],Deriv),V1,Gamma1,Form) :-	% step: indirect
	obj__formula(Form),
	eq__add_free(Form,V1,V2),
	pr__proof(Deriv,V2,[[~,Form]|Gamma1],Gamma2),
	pr__inconsistent(Gamma2),
	pr__statistics(step_indirect).

%%d pr__cases_formula(casL::in,fmlL::out)

pr__cases_formula([],[]).
pr__cases_formula([case(Form,_)|CaseL],[Form|FormL]) :-
	obj__formula(Form),
	pr__cases_formula(CaseL,FormL).

%%d pr__cases(varL::in,fmlL::in,casL::in,fml::out)

pr__cases([],_,_,_).
pr__cases([case(Form1,Deriv)|CaseL],V1,Gamma,Form2) :-
	eq__add_free(Form1,V1,V2),
	pr__proof(Deriv,V2,[Form1|Gamma],Gamma1),
	pr__derivable_err(V2,Gamma1,Form2),
	pr__cases(CaseL,V1,Gamma,Form2).

%%d pr__add_assumptionL(fmlL::in,varL::in,fmlL::in,varL::out,fmlL::out)

pr__add_assumptionL(FormL,V1,Gamma1,V2,Gamma2) :-
	eq__add_free_boundL(FormL,[],V1,V2),
	lst__concat(FormL,Gamma1,Gamma2).

%%d pr__conjunction(fmlL::in,fml::out)

pr__conjunction(FormL,Form) :-
	(	lst__singleton(FormL) ->
		FormL = [Form]
	;	Form = [&|FormL]
	).

%%d pr__derivable_once(varL::in,fmlL::in,fml::in)

% DEPTH OF THINKING = 6

pr__derivable_once(V,Gamma,Form) :- 
	once(pr__derivable(V,Gamma,Form,s(s(s(s(s(s(0)))))))).


%%d pr__derivable_once(varL::in,fmlL::in,fml::in,nat::in)

pr__derivable_once(V,Gamma,Form,N) :-
	once(pr__derivable(V,Gamma,Form,N)).

%%d pr__derivable(varL::in,fmlL::in,fml::in,nat::in)

pr__derivable(V,Gamma,Form,N) :-
	db__flag(debug),
	once(pr__debug(V,Gamma,Form,N)),
	fail.

pr__derivable(_,Gamma,Form,_) :-			% identity axiom
	lst__member_con_check(Form,Gamma),
	pr__statistics(rule_identity_axiom).
pr__derivable(V,Gamma,[&|FormL],s(N)) :-		% and intro
	pr__derivableL(FormL,V,Gamma,N),
	pr__statistics(rule_and_intro).
pr__derivable(V,Gamma,@(all,BV,Form),s(N)) :-		% forall intro
	lst__disjoint(V,BV),
	pr__derivable_once(V,Gamma,Form,N),
	pr__statistics(rule_forall_intro).
pr__derivable(_,Gamma,Form1,_) :-			% modus ponens match
	lst__member_con(Form2,Gamma),
	(	obj__forall_form(Form2)
	;	obj__implication_form(Form2)
	),
	pr__match_kernel(Form2,Form1,[],[],Sub,FormL),
	once(pr__match_args(FormL,Gamma,Sub)),
	pr__statistics(rule_modus_ponens_match).
pr__derivable(V,Gamma,[\/|FormL],s(N)) :-		% or intro
	lst__member(Form,FormL),
	pr__derivable_once(V,Gamma,Form,N),
	pr__statistics(rule_or_intro).
pr__derivable(V,Gamma,Form2,s(N)) :-			% modus ponens
	lst__member_con([=>,Form1,Form2],Gamma),
	pr__derivable_once(V,Gamma,Form1,N),
	pr__statistics(rule_modus_ponens_plain).
pr__derivable(_,Gamma,_,_) :-				% inconsistent
	pr__inconsistent(Gamma),
	pr__statistics(rule_inconsistent).
pr__derivable(V,Gamma,Form1,s(N)) :-			% modus ponens deriv
	lst__member_con(@(all,BV,[=>,Form2,Form3]),Gamma),
	pr__match_conclusion(Form3,Form1,BV,Sub),
	eq__apply_plain(Form2,Sub,Form4),
	pr__derivable_once(V,Gamma,Form4,N),
	pr__statistics(rule_modus_ponens_deriv).
pr__derivable(_,Gamma,@(ex,BV,Form1),_) :-		% exists intro
	lst__member_con(Form2,Gamma),
	\+ obj__exists_form(Form2),
	eq__match_constrained(Form1,Form2,BV,[],_),
	pr__statistics(rule_exists_intro).
pr__derivable(_,Gamma,@(ex,BV,Form),_) :-		% exists intro match
	pr__match_assumption(Gamma,Form,BV,[],_),
	pr__statistics(rule_exists_intro_match).
pr__derivable(_,_,Form,_) :-				% logical axiom
	pr__axiom(Form),
	pr__statistics(rule_special_axiom).
pr__derivable(V,Gamma,[=>,_,Form],s(N)) :-		% implication intro r
	pr__derivable_once(V,Gamma,Form,N),
	pr__statistics(rule_implication_intro_right).
pr__derivable(_,Gamma,[gr,$(X)],_) :-			% gr intro variable
	lst__member_con([gr,[n(_,_)|TermL]],Gamma),
	lst__member(Term,TermL),
	eq__occurs_qf(Term,X),
	obj__pure_term(Term),
	pr__statistics(rule_gr_intro_variable).
pr__derivable(V,Gamma,[gr,[n(_,_)|TermL]],s(N)) :- 	% gr intro term
	obj__pure_termL(TermL),
	eq__add_free_boundL(TermL,[],[],XL),
	cmp__map_gr(XL,[],FormL),
	pr__derivableL(FormL,V,Gamma,N),
	pr__statistics(rule_gr_intro_term).
pr__derivable(V,Gamma,[terminates,[&,Goal|GoalL]],s(N)) :-
	cmp__terminates_goal(Goal,Form1),
	pr__derivable_once(V,Gamma,Form1,N),
	(	cmp__terminates_goal([&|GoalL],Form2), 	% t intro t
		pr__derivable_once(V,Gamma,Form2,N),
		pr__statistics(rule_t_intro_t)
	;	cmp__succeeds_goal(Goal,Form2),		% t intro s
		cmp__terminates_goal([&|GoalL],Form3),
		pr__derivable_once(V,Gamma,[=>,Form2,Form3],N),
		pr__statistics(rule_t_intro_s)
	;	cmp__fails_goal(Goal,Form2),		% t intro f
		pr__derivable_once(V,Gamma,Form2,N),
		pr__statistics(rule_t_intro_f)
	).
pr__derivable(_,Gamma,Form,_) :-			% cet unification
	mgu__unify_gamma(Gamma,Result),
	pr__derivable_cet(Gamma,Result,Form),
	pr__statistics(rule_cet_unification).
pr__derivable(_,Gamma,Form,_) :-			% equality trivial
	pr__extract_eqs(Gamma,[],TermLL),
	TermLL = [_|_],
	pr__derivable_eq(Gamma,TermLL,Form),
	pr__statistics(rule_equality_trivial).
pr__derivable(_,Gamma,[succeeds,[Tag|TermL]],_) :- 	% sld step
	cmp__match_clause(Tag,TermL,Gamma),
	pr__statistics(rule_sld_step).
pr__derivable(V,Gamma,[Op,Atom],s(N)) :-		% user defined intro
	obj__sft_op(Op),
	bi__user_defined_atom(Atom),
	cmp__sft_formula(Op,Atom,Form),
	pr__derivable_once(V,Gamma,Form,N),
	pr__statistics(rule_user_defined_intro).
pr__derivable(_,Gamma,[\/,[succeeds,Goal],[fails,Goal]],_) :-
	lst__member_con_check([terminates,Goal],Gamma),
	pr__statistics(rule_totality).			% totality
pr__derivable(_,Gamma,[\/,[fails,Goal],[succeeds,Goal]],_) :-
	lst__member_con_check([terminates,Goal],Gamma),
	pr__statistics(rule_totality).
pr__derivable(V,Gamma,[Op,Atom],s(N)) :-		% built-in intro
	obj__sft_op(Op),
	bi__builtin_atom(Atom),
	bi__typed(Atom),
	bi__eval(Atom,Goal),
	cmp__op_goal(Op,Goal,Form),
	pr__derivable_once(V,Gamma,Form,N),
	pr__statistics(rule_built_in_intro).
pr__derivable(_,Gamma,[<=>,Form1,Form2],_) :-		% equivalence intro
	lst__member_con_check([=>,Form1,Form2],Gamma),
	lst__member_con_check([=>,Form2,Form1],Gamma),
	pr__statistics(rule_equivalence_intro).
pr__derivable(V,Gamma,[=>,Form,_],s(N)) :-		% implication intro l
	pr__derivable_once(V,Gamma,[~,Form],N),
	pr__statistics(rule_implication_intro_left).
pr__derivable(_,Gamma,Form1,_) :-			% trivial equivalencies
	pr__equivalent(Form1,Form2),
	lst__member_con_check(Form2,Gamma),
	pr__statistics(rule_trivial_equivalencies).
pr__derivable(_,Gamma,[=,Term1,Term2],_) :-		% cet injective
	lst__member_con([=,[n(R,N)|Term1L],[n(R,N)|Term2L]],Gamma),
	pr__cet_injective(Term1L,Term2L,Term1,Term2),
	pr__statistics(rule_cet_injective).
pr__derivable(_,Gamma,[\/|Form1L],_) :-			% or intro subset
	lst__member_con([\/|Form2L],Gamma),
	lst__subset(Form2L,Form1L),
	pr__statistics(rule_or_intro_subset).
pr__derivable(V,Gamma,@(all,BV1,Form1),_) :-		% forall intro alpha
	lst__member_con(Form2,Gamma),
	\+ obj__forall_form(Form2),
	eq__match(Form2,Form1,Sub),
	eq__sub_forall(Sub,V,BV1,[]),
	pr__statistics(rule_forall_intro_alpha).
pr__derivable(_,Gamma,Form2,_) :-			% equivalence elim
	(	lst__member_con([<=>,Form1,Form2],Gamma)
	;	lst__member_con([<=>,Form2,Form1],Gamma)
	),
	lst__member_con_check(Form1,Gamma),
	pr__statistics(rule_equivalence_elim).
pr__derivable(V1,Gamma,[=>,Form1,Form2],s(N)) :- 	% implication intro
	eq__add_free(Form1,V1,V2),
	pr__derivable_once(V2,[Form1|Gamma],Form2,N),
	pr__statistics(rule_implication_intro).
pr__derivable(_,Gamma,Form1,_) :-			% alpha conversion
	lst__member_con(Form2,Gamma),
	eq__alpha(Form1,Form2),
	pr__statistics(rule_alpha_conversion).

%%d pr__derivableL(fmlL::in,varL::in,fmlL::in,nat::in)

pr__derivableL([],_,_,_).
pr__derivableL([Form|FormL],V,Gamma,N) :-
	pr__derivable_once(V,Gamma,Form,N),
	pr__derivableL(FormL,V,Gamma,N).

%%d pr__axiom(fml::in)

pr__axiom([=,Term,Term]) :-				% equal terms
	pr__statistics(axiom_equal_terms).
pr__axiom([gr,[n(_,0)]]) :-				
	pr__statistics(axiom_gr_constant).		% ground constants
pr__axiom([~,[=,Term1,Term2]]) :-			% not unifiable terms
	obj__pure_term(Term1),
	obj__pure_term(Term2),
	\+ mgu__unifiable_terms(Term1,Term2),
	pr__statistics(axiom_not_unifiable_terms).
pr__axiom([<>,[n(Name1,N1)|_],[n(Name2,N2)|_]]) :-	% function clash
	\+ (Name1 = Name2, N1 = N2),
	pr__statistics(axiom_function_clash).
pr__axiom([\/|FormL]) :-				% tertium non datur
	(	lst__member([~,Form],FormL),
		lst__member_check(Form,FormL)
	;	lst__member([<>,Term1,Term2],FormL),
		lst__member_check([=,Term1,Term2],FormL)
	),
	pr__statistics(axiom_tertium_non_datur).
pr__axiom([<>,Term1,Term2]) :-				% different terms
	obj__pure_term(Term1),
	obj__pure_term(Term2),
	\+ mgu__unifiable_terms(Term1,Term2),
	pr__statistics(axiom_different_terms).
pr__axiom([<=>,Form,Form]) :-				% equivalence
	pr__statistics(axiom_equivalence).

%%d pr__inconsistent(fmlL::in)

pr__inconsistent(Gamma) :-				% falsum
	lst__member_con_check([\/],Gamma),
	pr__statistics(inconsistent_falsum).
pr__inconsistent(Gamma) :-				% fails and succeeds
	lst__member_con([fails,Goal],Gamma),
	lst__member_con_check([succeeds,Goal],Gamma),
	pr__statistics(inconsistent_fails_and_succeeds).
pr__inconsistent(Gamma) :-				% pos and neg
	lst__member_con([~,Form],Gamma),
	lst__member_con_check(Form,Gamma),
	pr__statistics(inconsistent_pos_and_neg).
pr__inconsistent(Gamma) :-				% equal and different
	lst__member_con([<>,Term1,Term2],Gamma),
	lst__member_con_check([=,Term1,Term2],Gamma),
	pr__statistics(inconsistent_equal_and_different).
pr__inconsistent(Gamma) :-				% not self different
	lst__member_con([<>,Term,Term],Gamma),
	pr__statistics(inconsistent_not_self_different).

%%d pr__equivalent(fml::in,fml::out)
%%d pr__equivalent(fml::out,fml::in)

pr__equivalent([<>,Term1,Term2],[~,[=,Term1,Term2]]).
pr__equivalent([~,[=,Term1,Term2]],[<>,Term1,Term2]).
pr__equivalent([<>,Term1,Term2],[<>,Term2,Term1]).


%%d pr__by(gr::in,varL::in,fmlL::in,fml::in,fml::out)

pr__by(lemma(Ref),V,Gamma1,Form1,Form1) :-		% ref to lemma
	db__lemma(Ref,Form2),
	pr__derivable_once(V,[Form2|Gamma1],Form1),
	pr__statistics(by_reference).
pr__by(theorem(Ref),V,Gamma1,Form1,Form1) :-		% ref to theorem
	db__theorem(Ref,Form2),
	pr__derivable_once(V,[Form2|Gamma1],Form1),
	pr__statistics(by_reference).
pr__by(corollary(Ref),V,Gamma1,Form1,Form1) :-		% ref to corollary
	db__corollary(Ref,Form2),
	pr__derivable_once(V,[Form2|Gamma1],Form1),
	pr__statistics(by_reference).
pr__by(axiom(Ref),V,Gamma1,Form1,Form1) :-		% ref to axiom
	db__axiom(Ref,Form2),
	pr__derivable_once(V,[Form2|Gamma1],Form1),
	pr__statistics(by_reference).
pr__by(completion,V,Gamma,[def,[Op,Atom]],Form) :-	% fixed point
	pr__derivable_once(V,Gamma,[Op,Atom]),
	cmp__sft_formula(Op,Atom,Form),
	pr__statistics(by_fixed_point).
pr__by(sld,_,Gamma,Form,Form) :-			% sld step
	Form = [succeeds,[Tag|TermL]],
	cmp__match_clause(Tag,TermL,Gamma),
	pr__statistics(by_sld_step).
pr__by(completion,V,Gamma,[Op,Atom],[Op,Atom]) :-	% closure
	cmp__sft_formula(Op,Atom,Form),
	pr__derivable_once(V,Gamma,Form),
	pr__statistics(by_closure).
pr__by(introduction(Name,N),V,Gamma,Form1,Form1) :- 	% predicate intro
	Form1 = [d(Name,N)|_],
	def__pred_formula(Form1,Form2),
	pr__derivable_once(V,Gamma,Form2),
	pr__statistics(by_predicate_intro).
pr__by(elimination(Name,N),V,Gamma,Form1,Form1) :- 	% predicate elim
	def__pred_atom(Name,N,Form1,Form2),
	pr__derivable_once(V,Gamma,Form2),
	pr__statistics(by_predicate_elim).
pr__by(existence(Name,N),V,Gamma,Form1,Form1) :-	% function existence
	def__fun_existence(Name,N,Form1,Form2),
	pr__derivable_once(V,Gamma,Form2),
	pr__statistics(by_function_existence).
pr__by(uniqueness(Name,N),V,Gamma,Form1,Form1) :-	% function uniqueness
	def__fun_uniqueness(Name,N,Form1,Form2),
	pr__derivable_once(V,Gamma,Form2),
	pr__statistics(by_function_uniqueness).
pr__by(concatenation,V,Gamma,Form,Form) :-		% concatenation
	bi__concatenation(V,Gamma,Form),
	pr__statistics(by_concatenation).
pr__by(builtin,V,Gamma,[Op,Atom],[Op,Atom]) :-		% built-in closure
	obj__sft_op(Op),
	bi__typed(Atom),
	bi__eval(Atom,Goal),
	cmp__op_goal(Op,Goal,Form),
	pr__derivable_once(V,Gamma,Form),
	pr__statistics(by_built_in_closure).
pr__by(builtin,V,Gamma,[def,[Op,Atom]],Form) :-		% built-in fixed pt
	obj__sft_op(Op),
	bi__typed(Atom),
	pr__derivable_once(V,Gamma,[Op,Atom]),
	bi__eval(Atom,Goal),
	cmp__op_goal(Op,Goal,Form),
	pr__statistics(by_built_in_fixed_point).
pr__by(addition,V,Gamma,Form,Form) :-			% addition
	bi__addition(V,Gamma,Form),
	pr__statistics(by_addition).
pr__by(gap,_,_,Form,Form) :-				% gap with warning
	ctl__warning([there,is,a,gap,in,the,proof]).
pr__by(because,_,_,Form,Form) :-			% gap without warning
	(	db__flag(report_because) ->
		ctl__warning([there,is,a,gap,in,the,proof])
	;	true
	).
pr__by(new(Ref),V,Gamma,Form,Form) :-			% new theorem
	tac__new(Ref,V,Gamma,Form).
pr__by(Opt,V,Gamma,Form,Form) :-			% tactics, see tac.pl
	lst__list_form(Opt),
	tac__proof_prt(Opt,V,Gamma,Form).
pr__by(comment(_),V,Gamma,Form,Form) :-			% comment
	pr__derivable_once(V,Gamma,Form).
pr__by(X,_,_,Form,Form) :-				% unknown tactic
	\+ pr__by_tag(X),
	ctl__error([unknown,tactic,q(X)]).

%%d pr__by_tag(gr::in)

pr__by_tag(lemma(_)).
pr__by_tag(theorem(_)).
pr__by_tag(corollary(_)).
pr__by_tag(axiom(_)).
pr__by_tag(completion).
pr__by_tag(sld).
pr__by_tag(introduction(_,_)).
pr__by_tag(elimination(_,_)).
pr__by_tag(existence(_,_)).
pr__by_tag(uniqueness(_,_)).
pr__by_tag(concatenation).
pr__by_tag(builtin).
pr__by_tag(addition).
pr__by_tag(gap).
pr__by_tag(because).
pr__by_tag(comment(_)).
pr__by_tag(new(_)).
pr__by_tag([_|_]).
pr__by_tag([]).

%%d pr__match_conclusion(fml::in,fml::in,varL::in,sub::out)

pr__match_conclusion(Form1,Form2,XL,Sub) :-
	eq__match_constrained(Form1,Form2,XL,[],Sub).
pr__match_conclusion([&|FormL],Form2,XL,Sub) :-
	lst__member(Form1,FormL),
	eq__match_constrained(Form1,Form2,XL,[],Sub).

%%d pr__match_assumption(fmlL::in,fml::in,varL::in,sub::in,sub::out)

pr__match_assumption(Gamma,Form1,XL,Sub1,Sub2) :-
	(	obj__conjunction_form(Form1) ->
		Form1 = [&|FormL],
		pr__match_assumptionL(FormL,Gamma,XL,Sub1,Sub2)
	;	lst__member_con(Form2,Gamma),
		eq__match_constrained(Form1,Form2,XL,Sub1,Sub2)
	).

%%d pr__match_assumptionL(fmlL::in,fmlL::in,varL::in,sub::in)

pr__match_assumptionL([],_,_,Sub,Sub).
pr__match_assumptionL([Form1|FormL],Gamma,XL,Sub1,Sub3) :-
	lst__member_con(Form2,Gamma),
	eq__match_constrained(Form1,Form2,XL,Sub1,Sub2),
	pr__match_assumptionL(FormL,Gamma,XL,Sub2,Sub3). % once ??

%%d pr__match_kernel(fml::in,fml::in,varL::in,varL::insub::out,fmlL::out)

pr__match_kernel(Form1,Form2,BV,_,Sub,[]) :-
	eq__match_constrained(Form1,Form2,BV,[],Sub).
pr__match_kernel([&|FormL1],Form2,BV,V,Sub,FormL2) :-
	lst__member(Form1,FormL1),
	pr__match_kernel(Form1,Form2,BV,V,Sub,FormL2).
pr__match_kernel([=>,Form3,Form4],Form2,BV,V1,Sub,FormL1) :-
	eq__add_free_bound(Form3,BV,V1,V2),
	pr__match_kernel(Form4,Form2,BV,V2,Sub,FormL2),
	FormL1 = [@(all,BV,Form3)|FormL2].
pr__match_kernel(@(all,BV2,Form3),Form2,BV1,V,Sub,FormL1) :-
	lst__disjoint(BV2,V),
	lst__append_set(BV2,BV1,BV3),
	pr__match_kernel(Form3,Form2,BV3,V,Sub,FormL1).

%%d pr__match_args(fmlL::in,fmlL::in,Sub)

pr__match_args([],_,_).
pr__match_args([@(all,BV,Form)|FormL],Gamma,Sub1) :-
	pr__match_assumption(Gamma,Form,BV,Sub1,Sub2),
	pr__match_args(FormL,Gamma,Sub2).


%%d pr__cet_injective(tmL::in,tmL::in,tm::in,tm::in)

pr__cet_injective([Term1|_],[Term2|_],Term1,Term2).
pr__cet_injective([_|Term1L],[_|Term2L],Term1,Term2) :-
	pr__cet_injective(Term1L,Term2L,Term1,Term2).

%%d pr__derivable_cet(fmlL::in,ptn::in,fml::in)

pr__derivable_cet(_,no,_).
pr__derivable_cet(_,yes(Part),[=,Term1,Term2]) :-
	mgu__term_eq(Term1,Term2,Part).
pr__derivable_cet(Gamma,yes(Part),Form1) :-
	lst__member_con(Form2,Gamma),
	mgu__expr_eq(Form1,Form2,Part).

%%d pr__extract_eqs(fmlL::in,tmLL::in,tmLL::out)

pr__extract_eqs([],TermLL,TermLL).
pr__extract_eqs([Form|Gamma],Term1LL,Term3LL) :-
	(	obj__equation_form(Form) ->
		Form = [=|TermL],
		pr__extract_eqs(Gamma,[TermL|Term1LL],Term3LL)
	;	obj__conjunction_form(Form) ->
		Form = [&|FormL],
		pr__extract_eqs(FormL,Term1LL,Term2LL),
		pr__extract_eqs(Gamma,Term2LL,Term3LL)
	;	pr__extract_eqs(Gamma,Term1LL,Term3LL)
	).

%%d pr__derivable_eq(fmlL::in,tmLL::in,fml::in)

pr__derivable_eq(_,TermLL,[=|TermL]) :-
	eq__termL_eq(TermL,TermLL).
pr__derivable_eq(Gamma,TermLL,Form1) :-
	lst__member_con(Form2,Gamma),
	once(eq__expr_eq(Form1,Form2,TermLL)).

%%d pr__step_err(drv::in,varL::in,fmlL::in,fml::out)

pr__step_err(Step,V,Gamma,Form) :-
	(	pr__step(Step,V,Gamma,Form) -> 
		true
	;	i2e__derivation_step(Step,X),
		ctl__error([incorrect,derivation,step,p(X)])
	).

%%d pr__derivable_err(varL::in,fmlL::in,fml::in)

pr__derivable_err(V,Gamma,Form) :-
	(	pr__derivable_once(V,Gamma,Form) ->
		true
	;	i2e__expression(Form,X),
		ctl__error([underivable,formula,p(X)])
	).

%%d pr__debug(varL::in,fmlL::in,fml::in)

pr__debug(V,Gamma,Form,_) :-
	i2e__expressionL(Gamma,XL),
	i2e__expression(Form,X),
	io__tell_user, nl,
	write('Protected Variables: '),
	write(V), nl,
	write('Available Formulas: '), nl,
	prt__write(XL), nl,
	write('To show: '), nl,
	prt__write(X), nl.


%%d pr__statistics(in::gr)

pr__statistics(_).

% The following definition is used for statistics.

%pr__statistics(X) :- bb__inc(X).

% pr.pl ends here

