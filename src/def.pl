/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 7/19/95, 4:33 PM */
/* Updated: Mon Feb 15 14:39:02 1999 */
/* Filename: def.pl */
/* Abstract: Defined predicate and defined function symbols. */

%%d db__pred(gr::out,fml::out)

:- dynamic db__pred/2.

db__pred([d('DUMMY',0)],[&]).

%%d def__defined_pred(gr::in,int::in)

def__defined_pred(Name,N) :-
	db__pred([d(Name,N)|_],_).

%%d db__fun(tm::out,fml::out,fml::out)

:- dynamic db__fun/3.

db__fun([f('DUMMY',0)],[&],[&]).

%%d def__defined_fun(gr::in,int::in)

def__defined_fun(Name,N) :-
	db__fun([f(Name,N)|_],_,_).

%% add a predicate definition to the database

%%d assert_pred(atm::in,fml::in)

assert_pred(Atom,Form) :-
	Atom = [d(Name,N)|_],
	(	def__defined_pred(Name,N) ->
		ctl__warning([Name/N,is,already,a,defined,predicate,symbol])
	;	def__defined_fun(Name,N) ->
		ctl__warning([Name/N,is,already,a,defined,function,symbol])
	;	assert(db__pred(Atom,Form))
	).

%% process a predicate definition

%%d definition_pred(gr::in,gr::in)

definition_pred(Name,N,X) :-
	ctl__unset_flag(global_error),
	e2i__formula(X,Form1),
	(	def__pred_check(Name,N,Form1,Form2,Form3,Form4) ->
		assert_pred(Form2,Form3),
		(	db__is_open(thm), 
			db__flag(thm_output) -> 
			io__tell(thm),
			write(':- '),
			writeq(assert_pred(Form2,Form3)),
			write('.'), nl
		; 	true
		),
		(	db__is_open(tex), 
			db__flag(tex_output) ->
			io__tell(tex),
			'TeX__write_def'(Name,N,Form4)
		; 	true
		),
		(	db__is_open(prt) ->
			io__tell(prt),
			prt__pred_def(Name,N,X)
		;	true
		),
		dep__write_assert(definition_pred(Name,N),[])	
	;	ctl__error([incorrect,predicate,definition,p(X)])
	).

%%d def__pred_check(gr::in,int::in,fml::in,fml::out,fml::out)

def__pred_check(Name,N,Form1,Form5,Form4,Form6) :-
	eq__add_free(Form1,[],[]),
	Form1 = @(all,BV,Form2),
	(	Form2 = [<=>,Form3,Form4]
	;	Form2 = [<=>,Form4,Form3]
	),
	(	Form3 = [n(Name,N)|TermL]
	;	Form3 = [d(Name,N)|TermL]
	),
	obj__make_varL(BV,TermL),
	(	def__defined_pred(Name,N) ->
		ctl__error([Name/N,is,already,a,defined,predicate,symbol])
	;	def__defined_fun(Name,N) ->
		ctl__error([Name/N,is,already,a,defined,function,symbol])
	;	Form5 = [d(Name,N)|TermL],
		Form6 = @(all,BV,[<=>,Form5,Form4])
	).

%%d def__pred_formula(fml::in,fml::out)

def__pred_formula([d(Name,N)|Term1L],Form2) :-
	db__pred([d(Name,N)|Term2L],Form1),
	obj__make_varL(V1,Term2L),
	eq__make_sub(V1,Term1L,V2,Sub),
	eq__max_qfL(Term1L,0,K1),
	eq__max(Form1,K1,K2),
	eq__apply(Form1,V2,Sub,K2,Form2).

%%d def__pred_atom(gr::in,int::in,fml::in,atm::out)

def__pred_atom(Name,N,Form1,Atom) :-
	db__pred([d(Name,N)|TermL],Form2),
	eq__match(Form2,Form1,Sub),
	eq__apply_sub_qf([d(Name,N)|TermL],Sub,Atom).

%% add a function definition to the database

%%d assert_fun(tm::in,fml::in,fml::in)

assert_fun(Term,Form1,Form2) :-
	Term = [f(Name,N)|_],
	(	def__defined_fun(Name,N) ->
		ctl__warning([Name/N,is,already,a,defined,function,symbol])
	;	def__defined_pred(Name,N) ->
		ctl__warning([Name/N,is,already,a,defined,predicate,symbol])
	;	assert(db__fun(Term,Form1,Form2))
	).

%% process a function definition

%%d definition_fun(gr::in,int::in,gr::in,gr::in,gr::in,gr::in)

definition_fun(Name,N,X,
		existence by Refex,
		uniqueness by Refuni) :-
	ctl__unset_flag(global_error),
	e2i__formula(X,Form1),
	(	def__fun_check(Name,N,Form1,Term,BV,Y,Form2,Form3,Form4) ->
		(	def__fun_check_existence(Refex,BV,Y,Form2,Form3) ->
			true
		;	ctl__error([incorrect,existence,in,definition,
				of,Name/N])
		),
		(	def__fun_check_uniqueness(Refuni,BV,Y,Form2,Form3) ->
			true
		;	ctl__error([incorrect,uniqueness,in,definition,
				of,Name/N])
		),
		Form5 = @(ex,[Y],Form3),
		assert_fun(Term,Form2,Form5),
		(	db__is_open(thm), 
			db__flag(thm_output) -> 
			io__tell(thm),
			write(':- '),
			writeq(assert_fun(Term,Form2,Form5)),
			write('.'), nl
		; 	true
		),
		(	db__is_open(tex), 
			db__flag(tex_output) ->
			io__tell(tex),
			'TeX__write_def'(Name,N,Form4)
		; 	true
		),
		(	db__is_open(prt) ->
			io__tell(prt),
			prt__definition_fun(Name,N,X,Refex,Refuni)
		;	true
		),
		dep__write_assert(definition_fun(Name,N),[Refex,Refuni])
	;	ctl__error([incorrect,function,definition,p(X)])
	).

%%d def__fun_check(gr::in,int::in,fml::in,tm::out,grL::out,gr::out,fml::out,fml::out)

def__fun_check(Name,N,Form1,Term2,BV2,Y,Form2,Form4,Form5) :-
	Form1 = @(all,BV1,[=>,Form2,Form3]),
	(	Form3 = [<=>,[=,Term1,$(Y)],Form4]
	;	Form3 = [<=>,[=,$(Y),Term1],Form4]
	;	Form3 = [<=>,Form4,[=,Term1,$(Y)]]
	;	Form3 = [<=>,Form4,[=,$(Y),Term1]]
	),
	(	Term1 = [n(Name,N)|TermL]
	;	Term1 = [f(Name,N)|TermL]
	),
	Term2 = [f(Name,N)|TermL],
	obj__make_varL(BV2,TermL),
	lst__delete(Y,BV1,BV2),
	eq__add_free(Form1,[],[]),
	eq__free(Form2,[Y]),
	Form5 = @(all,BV1,[=>,Form2,[<=>,[=,Term2,$(Y)],Form4]]).

%%d def__fun_check_existence(gr::in,varL::in,var::in,fml::in,fml::in)

def__fun_check_existence(Ref,BV,Y,Form1,Form2) :-
	Form3 = @(all,BV,[=>,Form1,@(ex,[Y],Form2)]),
	def__implies_thm(Ref,Form3).

%%d def__fun_check_uniqueness(gr::in,varL::in,var::in,fml::in,fml::in)

def__fun_check_uniqueness(Ref,BV1,Y,Form1,Form2) :-
	eq__max(Form2,0,Z),
	N is Z + 1,
	eq__apply(Form2,[Z],[Y => $(Z)],N,Form3),
	cmp__conjunction([Form2,Form3,Form1],Form4),
	lst__concat(BV1,[Y,Z],BV2),
	Form5 = @(all,BV2,[=>,Form4,[=,$(Y),$(Z)]]),
	def__implies_thm(Ref,Form5).

%%d def__map_gr(varL::in,fmlL::out)

def__map_gr([],[]).
def__map_gr([X|XL],[[gr,$(X)]|FormL]) :-
	def__map_gr(XL,FormL).

%d def__implies_thm(gr::in,fml::in)

def__implies_thm(theorem(Ref),Form1) :-
	db__theorem(Ref,Form2),
	def__derivable(Form2,Form1).
def__implies_thm(lemma(Ref),Form1) :-
	db__lemma(Ref,Form2),
	def__derivable(Form2,Form1).
def__implies_thm(corollary(Ref),Form1) :-
	db__corollary(Ref,Form2),
	def__derivable(Form2,Form1).
def__implies_thm(axiom(Ref),Form1) :-
	db__axiom(Ref,Form2),
	def__derivable(Form2,Form1).

%%d def__derivable(fml::in,fml::in)

def__derivable(Form1,Form2) :-
	eq__alpha(Form1,Form2).
def__derivable(Form1,@(all,BV,[=>,Form2,Form3])) :-
	pr__derivable_once(BV,[Form1,Form2],Form3).

%%d def__fun_existence(gr::in,int::in,fml::in,fml::out)

def__fun_existence(Name,N,Form1,Form4) :-
	db__fun([f(Name,N)|TermL],Form2,@(ex,[Y],Form3)),
	eq__match(Form3,Form1,Sub),
	eq__apply_sub_qf([f(Name,N)|TermL],Sub,Term),
	lst__member_check(Y => Term,Sub),
	eq__apply_plain(Form2,Sub,Form4).

%%d def__fun_uniqueness(gr::in,int::in,fml::in,fml::out)

def__fun_uniqueness(Name,N,Form1,Form6) :-
	db__fun([f(Name,N)|TermL],Form2,@(ex,[Y],Form3)),
	(	Form1 = [=,[f(Name,N)|Term2L],Term]
	;	Form1 = [=,Term,[f(Name,N)|Term2L]]
	),
	obj__make_varL(V1,TermL),
	eq__make_sub(V1,Term2L,V2,Sub),
	eq__max_qfL(Term2L,0,N1),
	eq__max(Form2,N1,N2),
	eq__apply(Form2,V2,Sub,N2,Form4),
	eq__max(Form3,N1,N3),
	eq__max_qf(Term,N3,N4),
	eq__add_free_qf(Term,V2,V3),
	eq__apply(Form3,V3,[Y => Term|Sub],N4,Form5),
	cmp__conjunction([Form4,Form5],Form6).

% def.pl ends here

