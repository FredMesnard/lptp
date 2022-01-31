/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 6/11/95, 10:37 PM */
/* Updated: Mon Feb 15 14:25:53 1999 */
/* Filename: cmp.pl */
/* Abstract: Predicates for computing the success-, failure- and 
   termination formula with and without unification. */

% We assume that the bodies of clauses are quantifier-free goals.

%%d db__clauses(prd::in,clsL::out)

:- dynamic db__clauses/2.

db__clauses(n(fail,0),[]).

%%d assert_clauses(prd::in,clsL::in)

assert_clauses(n(Name,N),ClauseL) :-
	(	obj__clauseL(ClauseL) ->
		(	db__clauses(n(Name,N),_) ->
			ctl__warning([predicate,Name/N,is,already,defined]),
			retract(db__clauses(n(Name,N),_)),
			assert(db__clauses(n(Name,N),ClauseL))
		;	bi__predicate(Name,N) ->
			ctl__warning([builtin,predicate,Name/N,is,
				already,defined]),
			assert(db__clauses(n(Name,N),ClauseL))
		;	assert(db__clauses(n(Name,N),ClauseL))
		)
	;	ctl__error([clauses,for,Name/N,are,corrupted])
	).

%%d cmp__clauses_err(prd::in,clsL::out)

cmp__clauses_err(n(Name,N),ClauseL) :-
	(	db__clauses(n(Name,N),ClauseL) -> 
		true
	;	ctl__error([there,are,no,clauses,for,Name/N]),
		ClauseL = []
	).

%%d cmp__sft_formula(gr::in,atm::in,fml::out)

cmp__sft_formula(Op,[Tag|TermL],Form) :-
	(	obj__make_varL(V,TermL),
		obj__varL(V) ->
		cmp__plain_gen(Tag,TermL,ClauseL)
	;	cmp__uni_gen(Tag,TermL,ClauseL)
	),
	cmp__op_clauseL(ClauseL,Op,FormL),
	(	Op = (succeeds) ->
		cmp__disjunction(FormL,Form)
	;	cmp__conjunction(FormL,Form)
	).

%%d cmp__op_clauseL(gr::in,clsL::in,fml::out)

cmp__op_clauseL([],_,[]).
cmp__op_clauseL([Clause|ClauseL],Op,[Form|FormL]) :-
	cmp__op_clause(Op,Clause,Form),
	cmp__op_clauseL(ClauseL,Op,FormL).

%%d cmp__op_clause(gr::in,cls::in,fml::out)

cmp__op_clause(succeeds,clause(EqL,Goal,VL),Form3) :-
	cmp__succeeds_goal(Goal,Form1),
	lst__append(EqL,[Form1],Form1L),
	cmp__conjunction(Form1L,Form2),
	cmp__abstraction(ex,VL,Form2,Form3).
cmp__op_clause(fails,clause(EqL,Goal,VL),Form4) :-
	cmp__conjunction_equations(EqL,Form1),
	cmp__fails_goal(Goal,Form2),
	cmp__implication(Form1,Form2,Form3),
	cmp__abstraction(all,VL,Form3,Form4).
cmp__op_clause(terminates,clause(EqL,Goal,VL),Form4) :-
	cmp__conjunction_equations(EqL,Form1),
	cmp__terminates_goal(Goal,Form2),
	cmp__implication(Form1,Form2,Form3),
	cmp__abstraction(all,VL,Form3,Form4).

%%d cmp__gen(gr::in,atm::in,clsL::out)

cmp__gen(plain,[Tag|TermL],ClauseL) :-
	cmp__plain_gen(Tag,TermL,ClauseL).
cmp__gen(uni,[Tag|TermL],ClauseL) :-
	cmp__uni_gen(Tag,TermL,ClauseL).

%%d cmp__plain_gen(prd::in,tmL::in,clsL::out)

cmp__plain_gen(Tag,TermL,Clause2L) :-
	cmp__clauses_err(Tag,Clause1L),
	eq__add_max_free_qfL(TermL,0,[],K,VL),
	cmp__plain_genL(Clause1L,TermL,VL,K,Clause2L).

%%d cmp__plain_genL(clsL::in,tmL::in,varL::in,int::in,clsL::out)

cmp__plain_genL([],_,_,_,[]).
cmp__plain_genL([Clause1|Clause1L],TermL,VL,K,[Clause3|Clause2L]) :-
	cmp__rename(Clause1,VL,K,Clause2),
	cmp__plain_gen_clause(Clause2,TermL,Clause3),
	cmp__plain_genL(Clause1L,TermL,VL,K,Clause2L).

%%d cmp__plain_gen_clause(cls::in,tmL::in,cls::out)

cmp__plain_gen_clause(clause([_|Term1L],Goal1,V1L),Term2L,
	clause(Eq2L,Goal2,V2L)) :-
	cmp__equationL(Term2L,Term1L,V1L,V2L,Eq1L,Sub),
	% One has to apply the substitution also to the equations
	eq__apply_sub_qfL(Eq1L,Sub,Eq2L),
	eq__apply_sub_qf(Goal1,Sub,Goal2).

%%d cmp__equationL(tmL::in,tmL::in,varL::in,varL::out,fmlL::out,sub::out)

cmp__equationL([],[],VL,VL,[],[]).
cmp__equationL([Term|Term1L],[[Tag|TermL]|Term2L],V1L,V2L,
	[[=,Term,[Tag|TermL]]|EqL],Sub) :-
	cmp__equationL(Term1L,Term2L,V1L,V2L,EqL,Sub).
cmp__equationL([Term|Term1L],[$(X)|Term2L],V1L,V3L,Eq2L,Sub2) :-
	% $(X) does not occur in Term, since the clause is renamed.
	(	lst__delete(X,V1L,V2L) ->
		Sub2 = [X => Term|Sub1],
		cmp__equationL(Term1L,Term2L,V2L,V3L,Eq2L,Sub1)
	;	Eq2L = [[=,Term,$(X)]|Eq1L],
		cmp__equationL(Term1L,Term2L,V1L,V3L,Eq1L,Sub2)
	).

%%d cmp__rename(cls::in,varL::in,int::in,cls::out)

cmp__rename(clause(Atom1,Goal1,V1L/N1),V2L,N2,clause(Atom2,Goal2,V3L)) :-
	cmp__maximum(N1,N2,K1),
	eq__apply_extend(V1L,V2L,[],K1,V3L,_,Sub,_),
	eq__apply_sub_qf(Atom1,Sub,Atom2),
	eq__apply_sub_qf(Goal1,Sub,Goal2).

%%d cmp__maximum(int::in,int::in,int::out)

cmp__maximum(N1,N2,N3) :-
	(	N1 < N2 -> 
		N3 = N2
	;	N3 = N1
	).

%%d cmp__uni_gen(prd::in,tmL::in,clsL::out)

cmp__uni_gen(Tag,Term1L,Clause3L) :-
	cmp__clauses_err(Tag,Clause1L),
	eq__add_max_free_qfL(Term1L,0,[],K1,V1L),
	cmp__pure_partL(Term1L,K1,[],Term2L,K2,Sub),
	eq__add_free_qfL(Term2L,V1L,V2L),	% Why? Oh, yes.
	cmp__uni_genL(Clause1L,Term2L,V2L,K2,Clause2L),
	(	Sub = [] ->
		Clause3L = Clause2L
	;	cmp__apply_clauseL(Clause2L,Sub,Clause3L)
	).

%%d cmp__uni_genL(clsL::in,tmL::in,varL::in,int::in,clsL::out)

cmp__uni_genL([],_,_,_,[]).
cmp__uni_genL([Clause1|Clause1L],Term1L,V1L,K,Clause3L) :-
	cmp__rename(Clause1,V1L,K,clause([_|Term2L],Goal1,V2L)),
	(	mgu__unify_termL_sub(Term1L,Term2L,Sub1) ->
		cmp__uni_equationL(Sub1,V2L,V3L,Sub2,Sub3,Eq1L),
		eq__apply_sub_qf(Goal1,Sub2,Goal2),
		eq__apply_sub_qf(Goal2,Sub3,Goal3),
		eq__apply_sub_qfL(Eq1L,Sub3,Eq2L),
		Clause3L = [clause(Eq2L,Goal3,V3L)|Clause2L],
		cmp__uni_genL(Clause1L,Term1L,V1L,K,Clause2L)
	;	% otherwise the terms are not unifiable
		cmp__uni_genL(Clause1L,Term1L,V1L,K,Clause3L)
	).

%%d cmp__uni_equationL(sub::in,varL::in,varL::out,sub::out,sub::out,fmlL::out)

cmp__uni_equationL([],VL,VL,[],[],[]).
cmp__uni_equationL([X => Term|Sub1],V1L,V3L,Sub3,Sub5,Eq2L) :-
    (   Term = $(X) ->
        cmp__uni_equationL(Sub1,V1L,V3L,Sub3,Sub5,Eq2L)
    ;   (   lst__delete(X,V1L,V2L) ->
	    % $(X) does not occur in Term, since the mgu is idempotent
            Sub3 = [X => Term|Sub2],
            cmp__uni_equationL(Sub1,V2L,V3L,Sub2,Sub5,Eq2L)
        ;   (   Term = $(Y) ->
                (   lst__delete(Y,V1L,V2L) ->
                    Sub3 = [Y => $(X)|Sub2],
                    Sub5 = [Y => $(X)|Sub4],
                    cmp__uni_equationL(Sub1,V2L,V3L,Sub2,Sub4,Eq2L)
                ;   Eq2L = [[=,$(Y),$(X)]|Eq1L],
		    cmp__uni_equationL(Sub1,V1L,V3L,Sub3,Sub5,Eq1L)
                    
                )
            ;   Eq2L = [[=,$(X),Term]|Eq1L],
	        cmp__uni_equationL(Sub1,V1L,V3L,Sub3,Sub5,Eq1L)
                
            )
        )
    ).

%%d cmp__pure_part(tm::in,int::in,sub::in,tm::out,int::out,sub::out)

cmp__pure_part($(X),K,Sub,$(X),K,Sub).
cmp__pure_part([n(Name,N)|Term1L],K1,Sub1,[n(Name,N)|Term2L],K2,Sub2) :-
	cmp__pure_partL(Term1L,K1,Sub1,Term2L,K2,Sub2).
cmp__pure_part([f(Name,N)|Term1L],K1,Sub1,$(K2),K3,Sub2) :-
	% We want a special term and not a general one.
	(	lst__member(K2 => [f(Name,N)|Term1L],Sub1) ->
		K3 = K1,
		Sub2 = Sub1
	;	K2 = K1, 
		K3 is K1 + 1, 
		Sub2 = [K2 => [f(Name,N)|Term1L]|Sub1]).

%%d cmp__pure_partL(tmL::in,int::in,sub::in,tmL::out,int::out,sub::out)

cmp__pure_partL([],K,Sub,[],K,Sub).
cmp__pure_partL([Term1|Term1L],K1,Sub1,[Term2|Term2L],K3,Sub3) :-
	cmp__pure_part(Term1,K1,Sub1,Term2,K2,Sub2),
	cmp__pure_partL(Term1L,K2,Sub2,Term2L,K3,Sub3).

%%d cmp__apply_clauseL(clsL::in,sub::in,clsL::out)

cmp__apply_clauseL([],_,[]).
cmp__apply_clauseL([clause(Eq1L,Goal1,VL)|Clause1L],Sub,
	[clause(Eq2L,Goal2,VL)|Clause2L]) :-
	eq__apply_sub_qfL(Eq1L,Sub,Eq2L),
	eq__apply_sub_qf(Goal1,Sub,Goal2),
	cmp__apply_clauseL(Clause1L,Sub,Clause2L).

% In applying the operators 'succeeds', 'fails' and 'terminates' to goals
% the following simplifications are made:
%
% tt & Form ===> Form
% ff & Form ===> ff
% tt \/ Form ===> tt
% ff \/ Form ===> Form
% tt => Form ===> Form
% ff => Form ===> tt
% Form => tt ===> tt
% Form => ff ===> ~ Form
% fails (?x = ?y & Goal) ===> ?x = ?y => fails Goal
% terminates (?x = ?y & Goal) ===> ?x = ?y => terminates Goal

%%d cmp__op_goal(gr::in,goal::in,fml::out)

cmp__op_goal(succeeds,Goal,Form) :-			% succeeds
	cmp__succeeds_goal(Goal,Form).
cmp__op_goal(fails,Goal,Form) :-			% fails
	cmp__fails_goal(Goal,Form).
cmp__op_goal(terminates,Goal,Form) :-			% terminates
	cmp__terminates_goal(Goal,Form).

%%d cmp__succeeds_goal(goal::in,fml::out)

cmp__succeeds_goal([=,Term1,Term2],[=,Term1,Term2]).	% =
cmp__succeeds_goal([n(Name,N)|TermL],		% predicate
	[succeeds,[n(Name,N)|TermL]]).
cmp__succeeds_goal([~,Goal],Form) :-		% negation
	cmp__fails_goal(Goal,Form).
cmp__succeeds_goal([&|GoalL],Form) :-		% conjunction
	cmp__succeeds_goalL(GoalL,FormL),
	cmp__conjunction(FormL,Form).
cmp__succeeds_goal([\/|GoalL],Form) :-		% disjunction
	cmp__succeeds_goalL(GoalL,FormL),
	cmp__disjunction(FormL,Form).
cmp__succeeds_goal(@(ex,XL,Goal),	% existential
	@(ex,XL,Form)) :-
	cmp__succeeds_goal(Goal,Form).

%%d cmp__succeeds_goalL(goalL::in,fmlL::out)

cmp__succeeds_goalL([],[]).
cmp__succeeds_goalL([Goal|GoalL],[Form|FormL]) :-
	cmp__succeeds_goal(Goal,Form),
	cmp__succeeds_goalL(GoalL,FormL).

%%d cmp__fails_goal(goal::in,fml::out)

cmp__fails_goal([=,Term1,Term2],[<>,Term1,Term2]).	% =
cmp__fails_goal([n(Name,N)|TermL],		% predicate
	[fails,[n(Name,N)|TermL]]).
cmp__fails_goal([~,Goal],Form) :-		% negation
	cmp__succeeds_goal(Goal,Form).
cmp__fails_goal([&|GoalL],Form) :-		% conjunction
	cmp__fails_goalL(GoalL,FormL),
	cmp__disjunction(FormL,Form).
cmp__fails_goal([\/|GoalL],Form) :-		% disjunction
	cmp__fails_goalL(GoalL,FormL),
	cmp__conjunction(FormL,Form).
cmp__fails_goal(@(ex,XL,Goal),		% existential
	@(all,XL,Form)) :-
	cmp__fails_goal(Goal,Form).

%%d cmp__fails_goalL(goalL::in,fmlL::out)

cmp__fails_goalL([],[]).
cmp__fails_goalL([Goal|GoalL],[Form|FormL]) :-
	cmp__fails_goal(Goal,Form),
	cmp__fails_goalL(GoalL,FormL).

%%d cmp__terminates_goal(goal::in,fml::out)

cmp__terminates_goal([=,_,_],[&]).		% =
cmp__terminates_goal([n(Name,N)|TermL],		% predicate
	[terminates,[n(Name,N)|TermL]]).
cmp__terminates_goal([~,Goal],Form2) :-		% negation
	cmp__pure_goal(Goal),
	cmp__terminates_goal(Goal,Form1),
	cmp__gr_goal(Goal,FormL),
	cmp__conjunction([Form1|FormL],Form2).
cmp__terminates_goal([&|GoalL],Form) :-		% conjunction
	(	GoalL = [] ->
		Form = [&]
	;	lst__singleton(GoalL) ->
		GoalL = [Goal],
		cmp__terminates_goal(Goal,Form)
	;	Form = [terminates,[&|GoalL]]
	).
cmp__terminates_goal([\/|GoalL],Form) :-	% disjunction
	cmp__terminates_goalL(GoalL,FormL),
	cmp__conjunction(FormL,Form).
cmp__terminates_goal(@(ex,XL,Goal),	% existential
	@(all,XL,Form)) :-
	cmp__terminates_goal(Goal,Form).

%%d cmp__terminates_goalL(goalL::in,fmlL::out)

cmp__terminates_goalL([],[]).
cmp__terminates_goalL([Goal|GoalL],[Form|FormL]) :-
	cmp__terminates_goal(Goal,Form),
	cmp__terminates_goalL(GoalL,FormL).

%%d cmp__gr_goal(exp::in,fmlL::out)

cmp__gr_goal(Goal,FormL) :-
	eq__add_free(Goal,[],XL),
	cmp__map_gr(XL,[],FormL).

%%d cmp__map_gr(grL::in,fmlL::in,fmlL::out)

cmp__map_gr([],FormL,FormL).
cmp__map_gr([X|XL],Form1L,Form2L) :-
	cmp__map_gr(XL,[[gr,$(X)]|Form1L],Form2L).

%%d cmp__disjunction(fmlL::in,fml::out)

cmp__disjunction(Form1L,Form2) :-
	cmp__flatten_dis(Form1L,Form2L),
	(	lst__singleton(Form2L) ->
		Form2L = [Form2]
	;	lst__member_check([&],Form2L) ->
		Form2 = [&]
	;	Form2 = [\/|Form2L]
	).

%%d cmp__conjunction(fmlL::in,fml::out)

cmp__conjunction(Form1L,Form2) :-
	cmp__flatten_con(Form1L,Form2L),
	(	lst__singleton(Form2L) ->
		Form2L = [Form2]
	;	lst__member_check([\/],Form2L) ->
		Form2 = [\/]
	;	Form2 = [&|Form2L]
	).

%%d cmp__flatten_con(fmlL::in,fmlL::out)

cmp__flatten_con([],[]).
cmp__flatten_con([Form|Form1L],Form4L) :-
	cmp__flatten_con(Form1L,Form2L),
	(	obj__conjunction_form(Form) ->
		Form = [&|Form3L],
		lst__concat(Form3L,Form2L,Form4L)
	;	Form4L = [Form|Form2L]
	).
		
%%d cmp__flatten_dis(fmlL::in,fmlL::out)

cmp__flatten_dis([],[]).
cmp__flatten_dis([Form|Form1L],Form4L) :-
	cmp__flatten_dis(Form1L,Form2L),
	(	obj__disjunction_form(Form) ->
		Form = [\/|Form3L],
		lst__concat(Form3L,Form2L,Form4L)
	;	Form4L = [Form|Form2L]
	).

%%d cmp__implication(fml::in,fml::in,fml::out)

cmp__implication(Form1,Form2,Form3) :-
	(	Form1 = [&] ->
		Form3 = Form2
	;	Form1 = [\/] -> 
		Form3 = [&]
	;	Form2 = [\/] -> 
		Form3 = [~,Form1]
	;	Form2 = [&] -> 
		Form3 = [&]
	;	Form3 = [=>,Form1,Form2]
	).

%%d cmp__conjunction_equations(fmlL::in,fml::out)

cmp__conjunction_equations(FormL,Form) :-
	(	lst__singleton(FormL) ->
		FormL = [Form]
	;	Form = [&|FormL]
	).

%%d cmp__abstraction(gr::in,varL::in,fml::in,fml::out)


cmp__abstraction(Tag,VL,Form1,Form2) :-
	(	VL = [] ->
		Form2 = Form1
	;	eq__free(Form1,VL) ->
		Form2 = Form1
	;	Form2 = @(Tag,VL,Form1)
	).

% What happens if Form1 is already an abstraction???


%%d cmp__match_clause(prd::in,tmL::in,fmlL::in)

cmp__match_clause(Tag,Term1L,Gamma) :-
	db__clauses(Tag,ClauseL),
	lst__member(clause([Tag|Term2L],Goal,_),ClauseL),
	eq__match_qfL(Term2L,Term1L,[],Sub),
	cmp__succeeds_goal(Goal,Form),
	cmp__body_match(Form,Gamma,Sub,_).

%%d cmp__body_match(fml::in,fmlL::in,sub::in,sub::out)

cmp__body_match([=,Term1,Term2],Gamma,Sub1,Sub3) :-
	lst__member_con([=,Term3,Term4],Gamma),
	(	eq__match_qf(Term1,Term3,Sub1,Sub2),
		eq__match_qf(Term2,Term4,Sub2,Sub3) ->
		true
	;	eq__match_qf(Term1,Term4,Sub1,Sub2),
		eq__match_qf(Term2,Term3,Sub2,Sub3)
	).
cmp__body_match([<>,Term1,Term2],Gamma,Sub1,Sub3) :-
	lst__member_con([<>,Term3,Term4],Gamma),
	(	eq__match_qf(Term1,Term3,Sub1,Sub2),
		eq__match_qf(Term2,Term4,Sub2,Sub3) ->
		true
	;	eq__match_qf(Term1,Term4,Sub1,Sub2),
		eq__match_qf(Term2,Term3,Sub2,Sub3)
	).
cmp__body_match([succeeds,Atom1],Gamma,Sub1,Sub2) :-
	lst__member_con([succeeds,Atom2],Gamma),
	eq__match_qf(Atom1,Atom2,Sub1,Sub2).
cmp__body_match([fails,Atom1],Gamma,Sub1,Sub2) :-
	lst__member_con([fails,Atom2],Gamma),
	eq__match_qf(Atom1,Atom2,Sub1,Sub2).
cmp__body_match([&|FormL],Gamma,Sub1,Sub2) :-
	cmp__body_matchL(FormL,Gamma,Sub1,Sub2).
cmp__body_match([\/|FormL],Gamma,Sub1,Sub2) :-
	lst__member(Form,FormL),
	cmp__body_match(Form,Gamma,Sub1,Sub2).

%%d cmp__body_matchL(fmlL::in,fmlL::in,sub::in,sub::out)

cmp__body_matchL([],_,Sub,Sub).
cmp__body_matchL([Form|FormL],Gamma,Sub1,Sub3) :-
	cmp__body_match(Form,Gamma,Sub1,Sub2),
	cmp__body_matchL(FormL,Gamma,Sub2,Sub3).

%%d cmp__pure_goal(goal::in)

cmp__pure_goal([=,Term1,Term2]) :-
	obj__pure_term(Term1),
	obj__pure_term(Term2).
cmp__pure_goal([n(_,_)|TermL]) :-
	obj__pure_termL(TermL).
cmp__pure_goal([~,Goal]) :-
	cmp__pure_goal(Goal).
cmp__pure_goal([&|GoalL]) :-
	cmp__pure_goalL(GoalL).
cmp__pure_goal([\/|GoalL]) :-
	cmp__pure_goalL(GoalL).

%%d cmp__pure_goalL(goalL::in)

cmp__pure_goalL([]).
cmp__pure_goalL([Goal|GoalL]) :-
	cmp__pure_goal(Goal),
	cmp__pure_goalL(GoalL).

% cmp.pl ends here

