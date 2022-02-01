/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 7/19/95, 4:47 PM */
/* Updated: Mon Feb 15 10:29:11 1999 */
/* Filename: tac.pl */
/* Abstract: Some simple tactics. */


% tac__conclusion(Form,V,Gamma,m,Deriv) =>
%   exist Gamma1 such that pr__proof(Deriv,V,Gamma,Gamma1) and
%   lst__member(Form,Gamma1).
% 
% tac__conclusion(Form,V,Gamma,d,Deriv) =>
%   exist Gamma1 such that pr__proof(Deriv,V,Gamma,Gamma1) and
%   pr__derivable(V,Gamma1,Form).
% 
% tac__conclusion_acc(Form,V,Gamma,m,Deriv1,Deriv2) => 
%   Deriv2 = Deriv3 ** Deriv1 and 
%   there exist Gamma3 such that pr__proof(Deriv3,V,Gamma,Gamma3)
%   and lst__member(Form,Gamma3).
% 
% tac__conclusion_acc(Form,V,Gamma,d,Deriv1,Deriv2) =>
%   Deriv2 = Deriv3 ** Deriv1 and 
%   there exist Gamma3 such that pr__proof(Deriv3,V,Gamma,Gamma3)
%   and pr__derivable(V,Gamma1,Form).
% 
% tac__hypothesis(Form1,Form2,V,Gamma,m,Deriv) =>
%   if add_free(Form1,V,V1) then there exist a Gamma1 such that 
%   pr__proof(Deriv,V1,[Form1|Gamma],Gamma1)
%   and lst__member(Form2,Gamma1).
% 
% tac__hypothesis(Form1,Form2,V,Gamma,d,Deriv) =>
%   if add_free(Form1,V,V1) then there exist a Gamma1 such that 
%   pr__proof(Deriv,V1,[Form1|Gamma],Gamma1)
%   and pr__derivable(V1,Gamma1,Form2).


%%d tac__conclusion(fml::in,varL::in,fmlL::in,gr::in,drv::out)

tac__conclusion(Form,VL,Gamma,Opt,Deriv) :-
	tac__conclusion_acc(Form,VL,Gamma,Opt,[],Deriv).

%%d tac__conclusion_acc(fml::in,varL::in,fmlL::in,gr::in,drv::in,drv::out)

tac__conclusion_acc(Form,V,Gamma,Opt,Deriv1,Deriv5) :-
	(	pr__derivable_once(V,Gamma,Form,s(s(s(s(s(0)))))) ->
		tac__add(Opt,Form,Deriv1,Deriv5)
	;	Form = @(all,BV1,Form1) ->
		tac__add(Opt,@(all,BV1,Form1),Deriv1,Deriv2),
		(	lst__disjoint(BV1,V) ->
			tac__conclusion_acc(Form1,V,Gamma,m,Deriv2,Deriv5)
		;	tac__rename(BV1,Form1,V,BV2,Form2),
			tac__conclusion_acc(Form2,V,Gamma,m,
				[@(all,BV2,Form2)|Deriv2],Deriv5)
		)
	;	Form = [=>,Form1,Form2] ->
		tac__hypothesis(Form1,Form2,V,Gamma,d,Deriv2),
		Deriv5 = [assume(Form1,Deriv2,Form2)|Deriv1]
	;	Form = [<=>,Form1,Form2] ->
		tac__hypothesis(Form1,Form2,V,Gamma,d,Deriv2),
		tac__hypothesis(Form2,Form1,V,Gamma,d,Deriv3),
		tac__add(Opt,[<=>,Form1,Form2],Deriv1,Deriv4),
		Deriv5 = [assume(Form1,Deriv2,Form2),
		  	  assume(Form2,Deriv3,Form1)|Deriv4]
	;	Form = [~,Form1] ->
		tac__hypothesis(Form1,[\/],V,Gamma,d,Deriv2),
		Deriv5 = [contra(Form1,Deriv2)|Deriv1]
	;	Form = [&|FormL] ->
		tac__add(Opt,[&|FormL],Deriv1,Deriv2),
		tac__conclusion_accL(FormL,V,Gamma,Deriv2,Deriv5)
	;	Deriv5 = [Form by gap|Deriv1]
	).

%%d tac__conclusion_accL(fmlL::in,varL::in,fmlL::in,drv::in,drv::out)

tac__conclusion_accL([],_,_,Deriv,Deriv).
tac__conclusion_accL([Form|FormL],VL,Gamma,Deriv1,Deriv3) :-
	tac__conclusion_accL(FormL,VL,Gamma,Deriv1,Deriv2),
	tac__conclusion_acc(Form,VL,Gamma,d,Deriv2,Deriv3).

%%d tac__hypothesis(fml::in,fml::in,varL::in,fmlL::in,gr::in,drv::out)

tac__hypothesis(Form1,Form2,V1,Gamma,Opt,Deriv2) :-
	(	Form1 = @(ex,BV1,Form3) ->
		eq__add_free(Form2,V1,V2),
		(	lst__disjoint(V2,BV1) ->
			BV2 = BV1,
			Form4 = Form3
		;	tac__rename(BV1,Form3,V2,BV2,Form4)
		),
		eq__add_free(Form4,V1,V3),
		tac__hypothesis(Form4,Form2,V3,Gamma,d,Deriv1),
		Deriv2 = [exist(BV2,Form4,Deriv1,Form2)]
	;	Form1 = [\/|FormL],
		\+ (FormL = []) ->
		tac__caseL(FormL,Form2,V1,Gamma,CaseL),
		Deriv2 = [cases(CaseL,Form2)]
	;	Form1 = [=>,Form3,Form4],
		lst__member_con_check(Form3,Gamma) ->
		tac__hypothesis(Form4,Form2,V1,Gamma,Opt,Deriv1),
		Deriv2 = [Form4|Deriv1]
	;	eq__add_free(Form1,V1,V2),
		tac__conclusion(Form2,V2,[Form1|Gamma],Opt,Deriv2)
	).

%%d tac__caseL(fmlL::in,fml::in,varL::in,fmlL::in,casL::out)

tac__caseL([],_,_,_,[]).
tac__caseL([Form1|FormL],Form2,V,Gamma,[case(Form1,Deriv)|CaseL]) :-
	tac__hypothesis(Form1,Form2,V,Gamma,d,Deriv),
	tac__caseL(FormL,Form2,V,Gamma,CaseL).

%%d tac__add(gr::in,fml::in,drv::in,drv::out)

tac__add(m,Form,Deriv,[Form|Deriv]).
tac__add(d,_,Deriv,Deriv).

%%d tac__rename(varL::in,fml::in,varL::in,varL::out,fml::out)

tac__rename(BV1L,Form1,V1L,BV2L,Form2) :-
	eq__max(Form1,0,N1),
	eq__max_varL(V1L,N1,N2),
	eq__apply_extend(BV1L,V1L,[],N2,BV2L,V2L,Sub,N3),
	eq__apply(Form1,V2L,Sub,N3,Form2).

%%d tac__options(grL::in,fml::in,varL::in,fmlL::in,drv::out)

tac__options(Opt,Form,V,Gamma,Deriv) :-
	(	lst__member(debug,Opt) ->			% debug
		pr__debug(V,Gamma,Form,N)
	;	true
	),
		tac__derivable(Form,V,Gamma,Deriv)
	;	lst__member_check(fact,Opt),			% fact
		tac__fact(Form,V,Gamma,Deriv)
	;	lst__member_check(ind,Opt),			% ind
		tac__induction(Form,V,Gamma,Deriv)
	;	lst__member_check(indqf,Opt),			% indqf
		tac__qf_induction(Form,V,Gamma,Deriv)
	;	lst__member_check(unfold,Opt),			% unfold
		tac__unfold(Form,V,Gamma,Deriv)
	;	lst__member_check(case,Opt),			% case
		tac__case_split(Form,V,Gamma,Deriv)
	;	lst__member_check(ex,Opt),			% ex
		tac__existence_elim(Form,V,Gamma,Deriv)
	;	lst__member_check(elim,Opt),			% elim
		tac__definition_expand(Form,V,Gamma,Deriv)
	;	lst__member_check(tot,Opt),			% tot
		tac__totality(Form,V,Gamma,Deriv)
	;	lst__member_check(comp,Opt),			% comp
		tac__comp(Form,V,Gamma,Deriv)
	;	lst__member(auto(N),Opt),
		ai__automatic(N,Form,V,Gamma,Deriv)		% auto
	;	tac__conclusion(Form,V,Gamma,d,Deriv).

%%d tac__derivable(fml::in,varL::in,fmlL::in,drv::out)

tac__derivable(Form,V,Gamma,[Form]) :-
	pr__derivable_once(V,Gamma,Form).

%%d tac__fact(fml::in,varL::in,fmlL::in,drv::out)

tac__fact(Form1,V,Gamma,[Form2 by X]) :-
	tac__db_select(X,Form3),
	Form3 = @(all,BV,[=>,_,Form4]),
	(	Form2 = Form1
	;	Form1 = [=,Term1,Term2],
		Form2 = [=,Term2,Term1]
	),
	pr__match_kernel(Form4,Form2,BV,[],_,_),
	pr__derivable_once(V,[Form3|Gamma],Form2).
tac__fact(Form1,V,Gamma,[Form1 by X]) :-
	tac__db_select(X,Form2),
	pr__derivable_once(V,[Form2|Gamma],Form1).

%%d tac__db_select(gr::out,fml::out)

tac__db_select(X,Form) :-
		db__theorem(Ref,Form),
		X = theorem(Ref)
	;	db__lemma(Ref,Form),
		X = lemma(Ref)
	;	db__corollary(Ref,Form),
		X = corollary(Ref)
	;	db__axiom(Ref,Form),
		X = axiom(Ref).

%%d tac__induction(fml::in,varL::in,fmlL::in,drv::out)

tac__induction(Form,V,Gamma,[induction(Form2L,StepL)]) :-
	ind__formula_to_list(Form,Form1L),
	tac__induction_formulaL(Form1L,Form2L),
	ind__gen_err(tactic(V,Gamma),Form2L,StepL).

%%d tac__induction_formula(fml::in,fml::out)

tac__induction_formula(Form1,Form4) :-
	Form1 = @(all,ZL,[=>,Form2,Form3]),
	Form4 = @(all,XL,[=>,Form5,Form6]),
	(	Form2 = [succeeds,[n(_,_)|TermL]] ->
		Form5 = Form2,
		obj__make_varL(XL,TermL),
		lst__set_minus(ZL,XL,YL),
		cmp__abstraction(all,YL,Form3,Form6)
	;	Form2 = [&,Form5|FormL],	% FormL is not empty
		Form5 = [succeeds,[n(_,_)|TermL]],
		obj__make_varL(XL,TermL),
		lst__set_minus(ZL,XL,YL),
		cmp__conjunction(FormL,Form7),
		cmp__abstraction(all,YL,[=>,Form7,Form3],Form6)
	).

%%d tac__induction_formulaL(fmlL::in,fmlL::out)

tac__induction_formulaL([],[]).
tac__induction_formulaL([Form1|Form1L],[Form2|Form2L]) :-
	tac__induction_formula(Form1,Form2),
	tac__induction_formulaL(Form1L,Form2L).

%%d tac__qf_induction(fml::in,varL::in,fmlL::in,drv::out)

tac__qf_induction(@(all,_,[=>,Form1,Form2]),VL,Gamma,Deriv) :-
	Form1 = [succeeds,[n(_,_)|TermL]],
	obj__make_varL(XL,TermL),
	Form3 = @(all,XL,[=>,Form1,Form2]),
	ind__gen_err(tactic(VL,Gamma),[Form3],StepL),
	Deriv = [induction([Form3],StepL)].
tac__qf_induction(@(all,_,[=>,[&,Form1|Form1L],Form2]),VL,Gamma,Deriv) :-
	Form1 = [succeeds,[n(_,_)|TermL]],
	obj__make_varL(XL,TermL),
	cmp__conjunction(Form1L,Form3),
	Form4 = [=>,Form3,Form2],
	Form5 = @(all,XL,[=>,Form1,Form4]),
	ind__gen_err(tactic(VL,Gamma),[Form5],StepL),
	Deriv = [induction([Form5],StepL)].

%%d tac__unfold(fml::in,varL::in,fmlL::in,drv::out)

tac__unfold(Form1,VL,Gamma,Deriv) :-
	Form1 = [Op,Atom],
	obj__sft_op(Op), 
	obj__atomic_goal(Atom),
	cmp__sft_formula(Op,Atom,Form2),
	tac__conclusion_acc(Form2,VL,Gamma,m,
		[Form1 by completion],Deriv).
tac__unfold(Form1,VL,Gamma,Deriv) :-
	Form1 = [d(Name,N)|_],
	def__pred_formula(Form1,Form2),
	tac__conclusion_acc(Form2,VL,Gamma,d,
		[Form1 by introduction(Name,N)],Deriv).
tac__unfold(Form1,VL,Gamma,Deriv) :-
	Form1 = [=|_],
	def__fun_uniqueness(Name,N,Form1,Form2),
	tac__conclusion_acc(Form2,VL,Gamma,d,
		[Form1 by uniqueness(Name,N)],Deriv).
tac__unfold(Form1,VL,Gamma,Deriv) :-
	Form1 = [terminates,[&,Goal|GoalL]],
	cmp__terminates_goal(Goal,Form2),
	cmp__terminates_goal([&|GoalL],Form3),
	tac__conclusion_accL([Form2,Form3],VL,Gamma,[Form1],Deriv).
tac__unfold(Form1,VL,Gamma,Deriv) :-
	Form1 = [terminates,[&,Goal|GoalL]],
	cmp__terminates_goal(Goal,Form2),
	cmp__succeeds_goal(Goal,Form3),
	cmp__terminates_goal([&|GoalL],Form4),
	Form5 = [=>,Form3,Form4],
	tac__conclusion_accL([Form2,Form5],VL,Gamma,[Form1],Deriv).
tac__unfold(Form1,VL,Gamma,Deriv) :-
	def__fun_existence(Name,N,Form1,Form2),
	tac__conclusion_acc(Form2,VL,Gamma,d,
		[Form1 by existence(Name,N)],Deriv).

%%d tac__case_split(fml::in,varL::in,fmlL::in,drv::out)

tac__case_split(Form,V,Gamma,Deriv) :-
	tac__choose_assumption([\/|FormL],Gamma),
	tac__hypothesis([\/|FormL],Form,V,Gamma,d,Deriv).

%%d tac__existence_elim(fml::in,varL::in,fmlL::in,drv::out)

tac__existence_elim(Form1,V,Gamma,Deriv) :-
	tac__choose_assumption(@(ex,BV,Form2),Gamma),
	tac__hypothesis(@(ex,BV,Form2),Form1,V,Gamma,d,Deriv).

%%d tac__definition_expand(fml::in,varL::in,fmlL::in,drv::out)

tac__definition_expand(Form1,VL,Gamma,Deriv2) :-
	tac__choose_assumption([d(Name,N)|TermL],Gamma),
	def__pred_formula([d(Name,N)|TermL],Form2),
	tac__hypothesis(Form2,Form1,VL,Gamma,m,Deriv1),
	Deriv2 = [Form2 by elimination(Name,N)|Deriv1].

%%d tac__totality(fml::in,varL::in,fmlL::in,drv::out)

tac__totality(Form1,VL,Gamma,Deriv2) :-
	tac__choose_assumption([terminates,Atom],Gamma),
	Atom = [n(_,_)|_],
	Form2 = [\/,[succeeds,Atom],[fails,Atom]],
	tac__hypothesis(Form2,Form1,VL,Gamma,d,Deriv1),
	Deriv2 = [Form2|Deriv1].

%%d tac__comp(fml::in,varL::in,fmlL::in,drv::out)

tac__comp(Form1,VL,Gamma,Deriv2) :-
	tac__choose_assumption([Op,Atom],Gamma),
	obj__sft_op(Op),
	bi__user_defined_atom(Atom),
	cmp__sft_formula(Op,Atom,Form2),
	tac__hypothesis(Form2,Form1,VL,Gamma,m,Deriv1),
	Deriv2 = [[def,[Op,Atom]] by completion|Deriv1].

%%d tac__choose_assumption(fml::out,fmlL::in)

tac__choose_assumption(Form,Gamma) :-
	db__marked_assumption(Form),
	lst__member_con_check(Form,Gamma),
	retract(db__marked_assumption(Form)),
	assert(db__marked_assumption([&])).
tac__choose_assumption(Form,Gamma) :-
	lst__member_con(Form,Gamma).

%%d tac__proof_prt(grL::in,varL::in,fmlL::in,fml::in)

tac__proof_prt(Opt,VL,Gamma,Form) :-
	tac__options(Opt,Form,VL,Gamma,Deriv),
	once((
		i2e__derivation(Deriv,Y),
		(	lst__member(l(Left),Opt) -> 
			true 
		;	 Left = 0
		),
		(	lst__member(r(Right),Opt) -> 
			true 
		; 	prt__text_width(Right)
		),
		io__tell_user,
		nl, write('======'), nl,
		prt__write(Y,Left,Right), nl,
		write('======'), nl
	)),
	(	lst__member_check(more,Opt) ->
		write('more (y/n)? '),
		get(Char),
		(	Char = 110 ->		% answer: n
			true
		;	fail			% answer: y
		)
	; 	true).

%%d tac__by(gr::in,grL::in)

tac__by(X,Opt) :-
	e2i__formula(X,Form),
	tac__proof_prt(Opt,[],[],Form).

%%d tac__new(gr::in,varL::in,fmlL::in,fml::in)

tac__new(Ref,V1,Gamma1,Form1) :-
	lst__reverse(V1,V2),
	lst__reverse(Gamma1,Gamma2),
	cmp__conjunction(Gamma2,Form2),
	cmp__implication(Form2,Form1,Form3),
	cmp__abstraction(all,V2,Form3,Form4),
	tac__conclusion(Form4,[],[],d,Deriv),
	i2e__expression(Form4,X),
	i2e__derivation(Deriv,Y),
	prt__fact(lemma,Ref,X,Y).

% tac.pl ends here

