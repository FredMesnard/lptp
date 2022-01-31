%   Author: Robert Staerk <staerk@saul.cis.upenn.edu> 
%  Created: Mon Mar 11 14:46:08 1996 
% Updated: Thu Feb 11 10:39:07 1999
% Filename: ai.pl 
% Abstract: Artificial intelligence? --- Backward and forward search.

%%d ai__automatic(int::in,fml::in,varL::in,fmlL::in,drv::out)

ai__automatic(I,Form,V,Gamma,Deriv) :-
	ai__integer_numeral(I,K),
	ai__backward_acc(Form,V,Gamma,d,[],Deriv,K).

%%d ai__backward_acc(fml::in,varL::in,fmlL::in,gr::in,drv::in,drv::out,gr::in)

ai__backward_acc(Form,V,Gamma,Opt,Deriv1,Deriv2,_) :-
	pr__derivable_once(V,Gamma,Form),
	tac__add(Opt,Form,Deriv1,Deriv2).
ai__backward_acc(Form1,V,Gamma1,Opt,Deriv1,Deriv2,s(K)) :-
	lst__delete_con([=>,Form2,Form1],Gamma1,Gamma2),
	ai__backward_acc(Form2,V,Gamma2,Opt,Deriv1,Deriv2,K).
ai__backward_acc(Form1,_,Gamma,_,Deriv1,Deriv2,_) :-
	tac__db_select(X,@(all,BV,Form2)),
	pr__match_kernel(Form2,Form1,BV,[],Sub,FormL),
	pr__match_args(FormL,Gamma,Sub),
	Deriv2 = [Form1 by X|Deriv1].
ai__backward_acc(Form1,V,Gamma,Opt,Deriv1,Deriv3,s(K)) :-
	Form1 = @(all,BV1,Form2),
	tac__add(Opt,Form1,Deriv1,Deriv2),
	(	lst__disjoint(BV1,V) ->
		ai__backward_acc(Form2,V,Gamma,m,Deriv2,Deriv3,K)
	;	tac__rename(BV1,Form2,V,BV2,Form3),
		Form4 = @(all,BV2,Form3),
		ai__backward_acc(Form3,V,Gamma,m,[Form4|Deriv2],Deriv3,K)
	).
ai__backward_acc([=>,Form1,Form2],V,Gamma,_,Deriv1,Deriv3,s(K)) :-
	ai__backward_add(Form1,Form2,V,Gamma,d,Deriv2,K),
	Deriv3 = [assume(Form1,Deriv2,Form2)|Deriv1].
ai__backward_acc(Form1,V,Gamma,Opt,Deriv1,Deriv3,s(K)) :-
	Form1 = [<=>,Form2,Form3],
	tac__add(Opt,Form1,Deriv1,Deriv2),
	FormL = [[=>,Form2,Form3],[=>,Form3,Form2]],
	ai__backward_accL(FormL,V,Gamma,Opt,Deriv2,Deriv3,K).
ai__backward_acc([~,Form],V,Gamma,_,Deriv1,Deriv3,s(K)) :-
	ai__backward_add(Form,[\/],V,Gamma,d,Deriv2,K),
	Deriv3 = [contra(Form,Deriv2)|Deriv1].
ai__backward_acc([&|FormL],V,Gamma,Opt,Deriv1,Deriv3,s(K)) :-
	tac__add(Opt,[&|FormL],Deriv1,Deriv2),
	ai__backward_accL(FormL,V,Gamma,d,Deriv2,Deriv3,K).
ai__backward_acc(Form,_,Gamma,_,Deriv1,Deriv2,_) :-
	Form = [succeeds,[Tag|TermL]],
	cmp__match_clause(Tag,TermL,Gamma),
	Deriv2 = [Form by sld|Deriv1].
ai__backward_acc([Op,Atom],V,Gamma,_,Deriv1,Deriv3,s(K)) :-
	obj__sft_op(Op),
	bi__user_defined_atom(Atom),
	cmp__sft_formula(Op,Atom,Form),
	Deriv2 = [[Op,Atom] by completion|Deriv1],
	ai__backward_acc(Form,V,Gamma,d,Deriv2,Deriv3,K).
ai__backward_acc([Op,Atom],V,Gamma,_,Deriv1,Deriv3,s(K)) :-
	obj__sft_op(Op),
	bi__builtin_atom(Atom),
	bi__typed(Atom),
	bi__eval(Atom,Goal),
	cmp__op_goal(Op,Goal,Form),
	Deriv2 = [[Op,Atom] by builtin|Deriv1],
	ai__backward_acc(Form,V,Gamma,d,Deriv2,Deriv3,K).
ai__backward_acc(Form1,V,Gamma,_,Deriv1,Deriv3,s(K)) :-
	Form1 = [d(Name,N)|_],
	def__pred_formula(Form1,Form2),
	Deriv2 = [Form1 by introduction(Name,N)|Deriv1],
	ai__backward_acc(Form2,V,Gamma,d,Deriv2,Deriv3,K).
ai__backward_acc(Form1,V,Gamma,_,Deriv1,Deriv3,s(K)) :-
	Form1 = [=|_],
	def__fun_uniqueness(Name,N,Form1,Form2),
	Deriv2 = [Form1 by uniqueness(Name,N)|Deriv1],
	ai__backward_acc(Form2,V,Gamma,d,Deriv2,Deriv3,K).
ai__backward_acc(Form1,V,Gamma,Opt,Deriv1,Deriv3,s(K)) :-
	Form1 = [terminates,[&,Goal|GoalL]],
	cmp__terminates_goal(Goal,Form2),
	cmp__terminates_goal([&|GoalL],Form3),
	tac__add(Opt,Form1,Deriv1,Deriv2),
	FormL = [Form2,Form3],
	ai__backward_accL(FormL,V,Gamma,d,Deriv2,Deriv3,K).
ai__backward_acc(Form1,V,Gamma,Opt,Deriv1,Deriv3,s(K)) :-
	Form1 = [terminates,[&,Goal|GoalL]],
	cmp__terminates_goal(Goal,Form2),
	cmp__succeeds_goal(Goal,Form3),	
	cmp__terminates_goal([&|GoalL],Form4),
	tac__add(Opt,Form1,Deriv1,Deriv2),
	FormL = [Form2,[=>,Form3,Form4]],
	ai__backward_accL(FormL,V,Gamma,d,Deriv2,Deriv3,K).
ai__backward_acc(Form,V,Gamma,Opt,Deriv1,Deriv3,s(K)) :-
	Form = [gr,[n(_,_)|TermL]],
	obj__pure_termL(TermL),
	tac__add(Opt,Form,Deriv1,Deriv2),
	eq__add_free_boundL(TermL,[],[],XL),
	cmp__map_gr(XL,[],FormL),
	ai__backward_accL(FormL,V,Gamma,d,Deriv2,Deriv3,K).
ai__backward_acc(Form,V,Gamma,Opt,Deriv1,Deriv3,s(K)) :-
	Form = [gr,$(X)],
	tac__add(Opt,Form,Deriv1,Deriv2),
	(	lst__member_con([=,$(X),Term],Gamma)
	;	lst__member_con([=,Term,$(X)],Gamma)
	),
	ai__backward_acc([gr,Term],V,Gamma,m,Deriv2,Deriv3,K).
ai__backward_acc(Form,V,Gamma,Opt,Deriv1,Deriv3,s(K)) :-
	ai__choose_hypothesis(V,Gamma,Opt,Form,Deriv2,K),
	lst__append(Deriv2,Deriv1,Deriv3).
ai__backward_acc(Form1,V,Gamma,_,Deriv1,Deriv3,s(K)) :-
	ai__names_expressionL(Gamma,[],L1),
	tac__db_select(X,@(all,BV,[=>,Form4,Form3])),
	pr__match_conclusion(Form3,Form1,BV,Sub),
	ai__names_expression(Form4,[],L2),
	lst__subset(L2,L1),
	Deriv2 = [Form1 by X|Deriv1],
	eq__apply_plain(Form4,Sub,Form5),
	ai__backward_acc(Form5,V,Gamma,d,Deriv2,Deriv3,K).
ai__backward_acc(Form1,V1,Gamma,Opt,Deriv1,Deriv3,s(K)) :-
	tac__db_select(X,@(all,BV,[=>,Form2,Form3])),
	pr__match_assumption(Gamma,Form2,BV,[],Sub),
	eq__apply_plain(Form3,Sub,Form4),
	\+ lst__member_con(Form4,Gamma),
	eq__add_free(Form4,V1,V2),
	ai__backward_acc(Form1,V2,[Form4|Gamma],Opt,Deriv1,Deriv2,K),
	Deriv3 = [Form4 by X|Deriv2].

%%d ai__backward_accL(fmlL::in,varL::in,fmlL::in,gr::in,drv::in,drv::out,gr::in)

ai__backward_accL([],_,_,_,Deriv,Deriv,_).
ai__backward_accL([Form|FormL],V,Gamma,Opt,Deriv1,Deriv3,K) :-
	ai__backward_accL(FormL,V,Gamma,Opt,Deriv1,Deriv2,K),
	ai__backward_acc(Form,V,Gamma,Opt,Deriv2,Deriv3,K).


%%d ai__choose_hypothesis(varL::in,fmlL::in,gr::in,fml::in,drv::out,gr::in)

ai__choose_hypothesis(V,Gamma1,Opt,Form1,Deriv,K) :-
	lst__delete_con(Form2,Gamma1,Gamma2),
	ai__forward(Form2,Form1,V,Gamma2,Opt,Deriv,K).

%%d ai__forward(fml::in,varL::in,fmlL::in,gr::in,fml::in,drv::out,gr::in)

ai__forward(@(ex,BV1,Form1),Form2,V1,Gamma,_,Deriv2,s(K)) :-
	eq__add_free(Form2,V1,V2),
	(	lst__disjoint(V2,BV1) ->
		BV2 = BV1,
		Form3 = Form1
	;	tac__rename(BV1,Form1,V2,BV2,Form3)
	),
	eq__add_free(Form3,V1,V3),
	ai__backward_add(Form3,Form2,V3,Gamma,d,Deriv1,K),
	Deriv2 = [exist(BV2,Form3,Deriv1,Form2)].
ai__forward([\/|FormL],Form,V,Gamma,_,Deriv,s(K)) :-
	\+ (FormL = []),
	ai__cases(FormL,Form,V,Gamma,CaseL,K),
	Deriv = [cases(CaseL,Form)].
ai__forward([d(Name,N)|TermL],Form1,V,Gamma,Opt,Deriv2,s(K)) :-
	def__pred_formula([d(Name,N)|TermL],Form2),
	ai__backward_add(Form2,Form1,V,Gamma,Opt,Deriv1,K),
	Deriv2 = [Form2 by elimination(Name,N)|Deriv1].
ai__forward([succeeds,Atom],Form1,V,Gamma,Opt,Deriv2,s(K)) :-
	bi__user_defined_atom(Atom),
	cmp__sft_formula(succeeds,Atom,Form2),
	ai__backward_add(Form2,Form1,V,Gamma,Opt,Deriv1,K),
	Deriv2 = [[def,[succeeds,Atom]] by completion|Deriv1].
ai__forward([succeeds,Atom],Form1,V,Gamma,Opt,Deriv2,s(K)) :-
	bi__builtin_atom(Atom),
	bi__typed(Atom),
	bi__eval(Atom,Goal),
	cmp__op_goal(succeeds,Goal,Form2),
	ai__backward_add(Form2,Form1,V,Gamma,Opt,Deriv1,K),
	Deriv2 = [[def,[succeeds,Atom]] by builtin|Deriv1].
ai__forward([terminates,Atom],Form1,V,Gamma,_,Deriv,s(K)) :-
	obj__atomic_goal(Atom),
	FormL = [[succeeds,Atom],[fails,Atom]],
	ai__cases(FormL,Form1,V,Gamma,CaseL,K),
	Deriv = [cases(CaseL,Form1)].
ai__forward([=>,Form1,Form2],Form3,V,Gamma,Opt,Deriv2,s(K)) :-
	pr__derivable_once(V,Gamma,Form1),
	ai__backward_add(Form2,Form3,V,Gamma,Opt,Deriv1,K),
	Deriv2 = [Form2|Deriv1].
ai__forward(@(all,BV,[=>,Form1,Form2]),Form3,V,Gamma,Opt,Deriv2,s(K)) :-
	pr__match_assumption(Gamma,Form1,BV,[],Sub),
	eq__apply_plain(Form2,Sub,Form4),
	ai__backward_add(Form4,Form3,V,Gamma,Opt,Deriv1,K),
	Deriv2 = [Form4|Deriv1].

%%d ai__cases(fmlL::in,fml::in,varL::in,fmlL::in,casL::out,gr::int).

ai__cases([],_,_,_,[],_).
ai__cases([Form1|FormL],Form2,V,Gamma,[case(Form1,Deriv)|CaseL],K) :-
	ai__backward_add(Form1,Form2,V,Gamma,d,Deriv,K),
	ai__cases(FormL,Form2,V,Gamma,CaseL,K).

%%d ai__backward_add(fml::in,fml::in,varL::in,fmlL::in,drv::out,gr::in)

ai__backward_add(Form1,Form2,V1,Gamma,Opt,Deriv,K) :-
	\+ lst__member_con(Form1,Gamma),
	eq__add_free(Form1,V1,V2),
	ai__backward_acc(Form2,V2,[Form1|Gamma],Opt,[],Deriv,K).

%%d ai__integer_numeral(int::in,gr::out)

ai__integer_numeral(I1,K2) :-
	(	I1 > 0 ->
		I2 is I1 - 1,
		K2 = s(K1),
		ai__integer_numeral(I2,K1)
	;	K2 = 0
	).


%%d ai__names_expression(expr::in,grL::in,grL::out)

ai__names_expression($(_),L,L).
ai__names_expression([Tag|ExprL],L1,L3) :-
	(	ai__name(Tag) ->
		lst__add_element(Tag,L1,L2),
		ai__names_expressionL(ExprL,L2,L3)
	;	ai__names_expressionL(ExprL,L1,L3)
	).
ai__names_expression(@(_,_,Expr),L1,L2) :-
	ai__names_expression(Expr,L1,L2).

%%d ai__names_expressionL(exprL::in,grL::in,grL::out)

ai__names_expressionL([],L,L).
ai__names_expressionL([Expr|ExprL],L1,L3) :-
	ai__names_expression(Expr,L1,L2),
	ai__names_expression(ExprL,L2,L3).


%%d ai__name(gr::in)

ai__name(n(_,_)).
ai__name(f(_,_)).
ai__name(d(_,_)).

% ai.pl ends here

