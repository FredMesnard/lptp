/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 7/26/95, 11:50 AM */
/* Updated: Wed Jul 21 11:51:53 1999 */
/* Filename: test.pl */
/* Abstract: Test file. 
   Main predicates: test(1), test(2), ... and test. */

test_max(8).

test_max(0,2).
test_max(1,11).
test_max(2,10).
test_max(3,14).
test_max(4,18).
test_max(5,32).
test_max(6,3).
test_max(7,8).
test_max(8,19).

%%% test predicates %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

test(0,1) :-
	concat_atom([ib,ex,' ',and,' ',marmot],X),
	X = 'ibex and marmot'.
test(0,2) :-
	atomic_length(ibex,N),
	N = 4.

test(1,1) :-
	e2i__test_formula(tt,[&]),
	e2i__test_formula(ff,[\/]).
test(1,2) :-
	e2i__test_formula(r(f(?x)), [n(r,1),[n(f,1),$(x)]]).
test(1,3) :-
	e2i__test_formula(?x = ?y = c = 0,[=,$(x),$(y),[n(c,0)],[n(0,0)]]).
test(1,4) :-
	e2i__test_formula((a & b) & (c & d),
	[&,[n(a,0)],[n(b,0)],[n(c,0)],[n(d,0)]]).
test(1,5) :-
	e2i__test_formula(a \/ b & c \/ d,
	[\/,[n(a,0)],[&,[n(b,0)],[n(c,0)]],[n(d,0)]]).
test(1,6) :-
	e2i__test_formula(all x: (all[y,z]: ?x <> ?y),
	@(all,[x,y,z],[<>,$(x),$(y)])).
test(1,7) :-
	e2i__test_formula(ex[x,y]:(ex z:r(?x,?y,?z)),
	@(ex,[x,y,z],[n(r,3),$(x),$(y),$(z)])).
test(1,8) :-
	e2i__test_formula(~ ?x <> ?x => ~ r(?y),
	[=>,[~,[<>,$(x),$(x)]],[~,[n(r,1),$(y)]]]).
test(1,9) :-
	e2i__test_formula(def(succeeds r(?x)) <=> fails q(?x),
	[<=>,[def,[succeeds,[n(r,1),$(x)]]],[fails,[n(q,1),$(x)]]]).
test(1,10) :-
	e2i__test_formula(succeeds a,[succeeds,[n(a,0)]]).
test(1,11) :-
	e2i__test_formula(gr(c),[gr,[n(c,0)]]).

test(2,1) :-
	i2e__test_formula(tt,tt),
	i2e__test_formula(ff,ff).
test(2,2) :-
	i2e__test_formula(r(f(?x,?y,0,[])),r(f(?x,?y,0,[]))).
test(2,3) :-
	i2e__test_formula([?x|?y] = ?z = f(f(0)),[?x|?y] = ?z = f(f(0))).
test(2,4) :-
	i2e__test_formula((a & b) & (c & d),a & b & c & d).
test(2,5) :-
	i2e__test_formula(a \/ (b \/ c),(a \/ b) \/ c).
test(2,6) :-
	i2e__test_formula(all x: (all[y,z]: ?x <> ?y),all[x,y,z]: ?x <> ?y).
test(2,7) :-
	i2e__test_formula(ex[x,y]:(ex z:r(?x,?y,?z)),ex[x,y,z]: r(?x,?y,?z)).
test(2,8) :-
	i2e__test_formula(~ ?x <> ?x => ~ r(?y),~ ?x <> ?x => ~ r(?y)).
test(2,9) :-
	i2e__test_formula(def(succeeds r(?x)) <=> fails q(?x),
	def(succeeds r(?x)) <=> fails q(?x)).
test(2,10) :-
	i2e__test_formula(succeeds[a,b] & fails[c,d] & terminates[e,f],
	succeeds[a,b] & fails[c,d] & terminates[e,f]).

test(3,1) :-
	e2i__test_derivation(a & b,a & b).
test(3,2) :-
	e2i__test_derivation([a & b],a & b).
test(3,3) :-
	e2i__test_derivation(ff by gap,ff by gap).
test(3,4) :-
	e2i__test_derivation(assume(a,[b],c),assume(a,b,c)).
test(3,5) :-
	e2i__test_derivation(contra(a,[]),contra(a,[])).
test(3,6) :-
	e2i__test_derivation(indirect(~ a,[]),indirect(~ a,[])).
test(3,7) :-
	e2i__test_derivation(cases(a,[aa],b,[bb],c),cases(a,aa,b,bb,c)).
test(3,8) :-
	e2i__test_derivation(cases([case(a,[]),case(b,[]),case(c,[])],d),
	cases([case(a,[]),case(b,[]),case(c,[])],d)).
test(3,9) :-
	e2i__test_derivation(cases([],a),cases([],a)).
test(3,10) :-
	e2i__test_derivation(cases([case(a,b)],c),cases([case(a,b)],c)).
test(3,11) :-
	e2i__test_derivation(exist(x,r(?x),[],ff),exist(x,r(?x),[],ff)).
test(3,12) :-
	e2i__test_derivation(exist([x],r(?x),[],ff),exist(x,r(?x),[],ff)).
test(3,13) :-
	e2i__test_derivation(exist([x,y],r(?x,?y),[],ff),
	exist([x,y],r(?x,?y),[],ff)).
test(3,14) :-
	e2i__test_derivation(induction([a,b],[step([x,y],[c,d],[],e)]),
	induction([a,b],[step([x,y],[c,d],[],e)])).

test(4,1) :-
	cmp__test_sft(succeeds a,tt).
test(4,2) :-
	cmp__test_sft(fails a,ff).
test(4,3) :-
	cmp__test_sft(terminates a,
	terminates (b1&b2&b3)&terminates c1&terminates (d1&d2)).

test(4,4) :-
	cmp__test_sft(succeeds append(?l1,?l2,?l3),
	?l1 = [] & ?l3 = ?l2 \/
	(ex [0,1,3] : ?l1 = [?0|?1] & ?l3 = [?0|?3] & 
	succeeds append(?1,?l2,?3))).
test(4,5) :-
	cmp__test_sft(fails append(?l1,?l2,?l3),
	~ (?l1 = [] & ?l3 = ?l2) & 
	(all [0,1,3] : ?l1 = [?0|?1] & ?l3 = [?0|?3] => 
	fails append(?1,?l2,?3))).
test(4,6) :-
	cmp__test_sft(terminates append(?l1,?l2,?l3),
	all [0,1,3] : ?l1 = [?0|?1] & ?l3 = [?0|?3] => 
	terminates append(?1,?l2,?3)).

test(4,7) :-
	cmp__test_sft(succeeds member(?l1,?l2),
	(ex 1 : ?l2 = [?l1|?1]) \/ 
	(ex [1,2] : ?l2 = [?1|?2] & succeeds member(?l1,?2))).
test(4,8) :-
	cmp__test_sft(fails member(?l1,?l2),
	(all 1 : ~ ?l2 = [?l1|?1]) & 
	(all [1,2] : ?l2 = [?1|?2] => fails member(?l1,?2))).
test(4,9) :-
	cmp__test_sft(terminates member(?l1,?l2),
	all [1,2] : ?l2 = [?1|?2] => terminates member(?l1,?2)).

test(4,10) :-
	cmp__test_sft(succeeds list(?l1),
	?l1 = [] \/ (ex [0,1] : ?l1 = [?0|?1] & succeeds list(?1))).
test(4,11) :-
	cmp__test_sft(fails list(?l1),
	~ ?l1 = [] & (all [0,1] : ?l1 = [?0|?1] => fails list(?1))).
test(4,12) :-
	cmp__test_sft(terminates list(?l1),
	all [0,1] : ?l1 = [?0|?1] => terminates list(?1)).

test(4,13) :-
	cmp__test_sft(succeeds notsubset(?l1,?l2),
	ex x : succeeds member(?x,?l1) & fails member(?x,?l2)).
test(4,14) :-
	cmp__test_sft(fails notsubset(?l1,?l2),
	all x : fails member(?x,?l1) \/ succeeds member(?x,?l2)).
test(4,15) :-
	cmp__test_sft(terminates notsubset(?l1,?l2),
	all 2 : terminates (member(?2,?l1) & ~ member(?2,?l2))).

test(4,16) :-
	cmp__test_sft(succeeds subset(?l1,?l2),
	fails notsubset(?l1,?l2)).
test(4,17) :-
	cmp__test_sft(fails subset(?l1,?l2),
	succeeds notsubset(?l1,?l2)).
test(4,18) :-
	cmp__test_sft(terminates subset(?l1,?l2),
	terminates notsubset(?l1,?l2) & gr(?l1) & gr(?l2)).

test(5,1) :-
	eq__free_qf([n(f,2),$(x),[n(g,1),$(y)]],[u,v,w]).
test(5,2) :-
	\+ eq__free_qf([n(f,2),$(x),[n(g,1),$(w)]],[u,v,w]).
test(5,3) :-
	eq__free(@(all,[x,y],[=,$(x),$(u)]),[x,v]).
test(5,4) :-
	\+ eq__free(@(all,[x,y],[=,$(x),$(v)]),[x,v]).
test(5,5) :-
	eq__free(@(all,[x,y],@(ex,[x,z],[=,$(x),$(u)])),
	[x,v]).
test(5,6) :-
	\+ eq__free(@(all,[x,y],@(ex,[x,z],[=,$(x),$(v)])),
	[x,v]).
test(5,7) :-
	lst__append_set([a,b,c,a,b,c],[u,v,c],X), X=[a,b,u,v,c].
test(5,8) :-
	eq__add_free(@(all,[x,y],[=,$(x),$(u),$(v)]),[v,w],X),
	X = [u,v,w].
test(5,9) :-
	eq__match([+,$(u),$(v),$(w)],[+,[f,$(a)],[c],$(w)],Sub),
	Sub=[w => $(w),v => [c],u => [f,$(a)]].
test(5,10) :-
	\+ eq__match([+,$(u),$(v)],[*,[f,$(a)],[c]],_).
test(5,11) :-
	\+ eq__match([+,$(u),$(v),$(u)],[+,[f,$(a)],[c],[d]],_).
test(5,12) :-
	eq__match(@(all,[x],[r,$(x),$(v),$(u)]),
	  @(all,[y],[r,$(y),[c],[d]]),Sub),
	Sub=[u => [d],v => [c]].
test(5,13) :-
	\+ eq__match(@(all,[x],[r,$(x),$(y),$(u)]),
	  @(all,[y],[r,$(y),$(y),[d]]),_).
test(5,14) :-
	eq__test_instance(all x:r(?x,?a,?b),all y:r(?y,c,d),Sub),
	Sub=[b => [n(d,0)],a => [n(c,0)]].
test(5,15) :-
	eq__test_instance(ex x:r(?x,?a,?a),ex y:r(?y,con,con),Sub),
	Sub=[a => [n(con,0)]].
test(5,16) :-
	eq__test_instance(ex x:r(?x,?a,?a),ex y:r(?y,?a,?a),Sub),
	Sub=[a => $(a)].
test(5,17) :-
	\+ eq__test_instance(ex x:r(?x,?a,?a),ex y:r(?y,?a,f(?y)),_).
test(5,18) :-
	true.
test(5,19) :-
	true.
test(5,20) :-
	eq__apply_test(all[x,y,z]:r(?x,?y,?z,?a,?b),[a,b],[c0,c1],X3),
	X3=(all[x,y,z]:r(?x,?y,?z,c0,c1)).
test(5,21) :-
	eq__apply_test(all[x,y,z]:r(?x,?y,?z,?a,?b),[a,b],[c0,f(?x,?y,?2)],X4),
	X4=(all[3,4,z]:r(?3,?4,?z,c0,f(?x,?y,?2))).
test(5,22) :-
	eq__apply_test(all x:f(?x,?y),[x],[f(?z)],Y),
	Y=(all x:f(?x,?y)).
test(5,23) :-
	eq__apply_test(all y:f(?x,?y),[x],[f(?z)],Y),
	Y=(all y:f(f(?z),?y)).
test(5,24) :-
	eq__apply_test(all y:f(?x,?y),[x],[f(?y)],Y),
	Y=(all 0:f(f(?y),?0)).
test(5,25) :-
	eq__apply_test(all 7:f(?x,?7),[x],[f(?7)],Y),
	Y=(all 8:f(f(?7),?8)).
test(5,26) :-
	eq__apply_test(all 3:f(?x,?3),[x],[f(?7)],Y),
	Y=(all 3:f(f(?7),?3)).
test(5,27) :-
	eq__test_match(all x: r(?x,?y,?z),all y:r(?y,0,1),[x,y,z],Sub),
	Sub = [z => [n(1,0)],y => [n(0,0)]].
test(5,28) :-
	\+ eq__test_match(all x: r(?x,?y,?z),all y:r(?y,0,1),[x,y],_).
test(5,29) :-
	\+ eq__test_match(all x: r(?x,?y,?z),all y:r(?y,?y,1),[x,y,z],_).
test(5,30) :-
	eq__test_match(all x: r(?x,?y,?z),all y:r(?y,?z,1),[x,y,z],Sub),
	Sub = [z => [n(1,0)],y => $(z)].
test(5,31) :-
	\+ eq__test_match(all x: r(?x,?y,?y),all y:r(?y,?x,0),[x,y,z],_).
test(5,32) :-
	\+ eq__test_match(all x: r(?x,?y,?z),all y:r(?y,0,f(?y)),[x,y,z],_).


test(6,1) :-
	e2i__formulaL([all x:succeeds list(?x)=>r(?x)],FormL),
	ind__gen_err(plain,FormL,Deriv),
	ind__step_alphaL(Deriv,
		[step([],[],[[\/]by gap],[n(r,1),[n([],0)]]),
	     step([0,1],[[n(r,1),$(1)],[succeeds,[n(list,1),$(1)]]],
	     [[\/]by gap],[n(r,1),[n(.,2),$(0),$(1)]])]).
test(6,2) :-
	e2i__formulaL([all[l1,l2,l3]: succeeds append(?l1,?l2,?l3)=> 
         (all l4:succeeds append(?l1,?l2,?l4)=> ?l3= ?l4)],FormL),
        ind__gen_err(plain,FormL,Deriv),
	ind__step_alphaL(Deriv,
    	[step([0],[],[[\/]by gap],
         @(all,[l4],
	 [=>,[succeeds,[n(append,3),[n([],0)],$(0),$(l4)]],
         [=,$(0),$(l4)]])),
         step([0,1,2,3],[@(all,[l4],[=>,
         [succeeds,[n(append,3),$(1),$(2),$(l4)]],
         [=,$(3),$(l4)]]),[succeeds,[n(append,3),$(1),$(2),$(3)]]],
         [[\/]by gap],@(all,[l4],[=>,
         [succeeds,[n(append,3),[n(.,2),$(0),$(1)],$(2),$(l4)]],
         [=,[n(.,2),$(0),$(3)],$(l4)]]))]).
test(6,3) :-
	e2i__formulaL([all 5:succeeds list(?5) => r(?5,?1)],FormL),
	ind__gen_err(plain,FormL,Deriv),
	ind__step_alphaL(Deriv,
	[step([],[],[[\/]by gap],[n(r,2),[n([],0)],$(1)]),
	 step([0,2],[[n(r,2),$(2),$(1)],[succeeds,[n(list,1),$(2)]]],
	  [[\/]by gap],[n(r,2),[n(.,2),$(0),$(2)],$(1)])]).

test(7,1) :-
	eq__apply_var([1 => $(x),2 => $(y),1 => $(z)],1,X),
	X = $(x).
test(7,2) :-
	eq__apply_var([1 => $(x),2 => $(y),1 => $(z)],2,X),
	X = $(y).
test(7,3) :-
	eq__apply_var([1 => $(x),2 => $(y),1 => $(z)],3,X),
	X = $(3).
test(7,4) :-
	eq__exp_test(r(?x),r(?y),[?u = ?w, ?y = 0 = ?x]).
test(7,5) :-
	eq__exp_test(r(?x,?y),r(?u,?w),[?x = 1 = ?u, ?w = 2 = ?y]).
test(7,6) :-
	\+ eq__exp_test(r(?x,?y),r(?u,?w),[?x = 1 = ?u, ?w = 2]).
test(7,7) :-
	eq__exp_test(all x:r(?x,f(f(?y)),?w),all u: r(?u,f(?w),f(?y)),
	[?w = f(?y)]).
test(7,8) :-
	\+ eq__exp_test(all y:r(?y,f(f(?y)),?w),all u: r(?u,f(?w),f(?y)),
	[?w = f(?y)]).

test(8,1) :-
	mgu__cycle_free(
	   [cl([n(f,2),$(x1),$(x1)],[cl($(x0),[])]),
	    cl([n(f,2),$(x2),$(x2)],[cl($(x1),[])]),
	    cl([n(f,2),$(x3),$(x3)],[cl($(x2),[])]),
	    cl([n(f,2),$(x4),$(x4)],[cl($(x3),[])]),
	    cl([n(f,2),$(x5),$(x5)],[cl($(x4),[])]),
	    cl([n(f,2),$(x6),$(x6)],[cl($(x5),[])]),
	    cl([n(f,2),$(x7),$(x7)],[cl($(x6),[])]),
	    cl([n(f,2),$(x8),$(x8)],[cl($(x7),[])]),
	    cl([n(f,2),$(x9),$(x9)],[cl($(x8),[])]),
	    cl([n(f,2),$(x10),$(x10)],[cl($(x9),[])]),
	    cl([n(f,2),$(x11),$(x11)],[cl($(x10),[])]),
	    cl([n(f,2),$(x12),$(x12)],[cl($(x11),[])]),
	    cl([n(f,2),$(x13),$(x13)],[cl($(x12),[])]),
	    cl([n(f,2),$(x14),$(x14)],[cl($(x13),[])]),
	    cl([n(f,2),$(x15),$(x15)],[cl($(x14),[])]),
	    cl([n(f,2),$(x16),$(x16)],[cl($(x15),[])]),
	    cl([n(f,2),$(x17),$(x17)],[cl($(x16),[])]),
	    cl([n(f,2),$(x18),$(x18)],[cl($(x17),[])]),
	    cl([n(f,2),$(x19),$(x19)],[cl($(x18),[])]),
	    cl([n(f,2),$(x20),$(x20)],[cl($(x19),[])])]).
test(8,2) :-
	\+ mgu__cycle_free(
	   [cl([n(f,2),$(x1),$(x1)],[cl($(x0),[])]),
	    cl([n(f,2),$(x2),$(x2)],[cl($(x1),[])]),
	    cl([n(f,2),$(x3),$(x0)],[cl($(x2),[])])]).
test(8,3) :-
	mgu__test(?x,f(0,0,?y,?y,?x),Sub), Sub = no.
test(8,4) :-
	mgu__test(?x,f(?y),Sub),
	Sub = [x => f(?y)].
test(8,5) :-
	mgu__test(f(g(?x),?y),f(?z,?z),Sub),
	Sub = [z => g(?x),y => g(?x)].
test(8,6) :-
	mgu__test(f(?x,?y),f(?y,?x),Sub),
	Sub = [x => ?y,y => ?y].
test(8,7) :-
	mgu__test(f(f(f(a,?x1),?x2),?x3),f(?x3,f(?x2,f(?x1,a))),Sub),
	Sub = [x3 => f(f(a,a),f(a,a)),x2 => f(a,a),x1 => a].
test(8,8) :-
	mgu__test(f(?z,g(g(g(g(?x))))),f(g(?z),g(g(g(g(?y))))),Sub), Sub = no.
test(8,9) :-
	mgu__test(f(?x,g(?x,g(?x,g(?x,g(?x,?x)))),?x),
		f(g(?y,g(?y,g(?y,g(?y,?y)))),?y,?y),Sub), Sub = no.
test(8,10) :-
	mgu__test(f(f(f(f(a,?x1),?x2),?x3),?x4),f(?x4,f(?x3,f(?x2,f(?x1,b)))),
	Sub), Sub = no.
test(8,11) :-
	mgu__test(f(?x,g(g(g(g(?x)))),?x),f(g(g(g(g(?y)))),?y,?y),Sub),
	Sub = no.
test(8,12) :-
	mgu__test(f(g(g(g(g(?x))))),f(g(g(g(g(?y))))),Sub),
	Sub = [x => ?y,y => ?y].
test(8,13) :-
	mgu__test(f(f(f(f(f(a,?x1),?x2),?x3),?x4),?z),
		f(f(?x4,f(?x3,f(?x2,f(?x1,a)))),g(?z)),Sub), Sub = no.
test(8,14) :-
	e2i__formulaL([f(?x,?y)= ?z=f((g(c)),g(?x)),p & q,
	  f(?x,?y)=f(g(?a),?b)],G),
	mgu__unify_gamma(G,yes(P)),
	mgu__partition_sub(P,P,[],Sub),
	i2e__subL(Sub,X),
	X = [z => f(g(c),g(g(c))),x => g(c),a => c,
		b => g(g(c)),y => g(g(c))].
test(8,15) :-
	mgu__test(f(?x,?y,?x),f(h(?x,?x),h(?y,?y),?y),Sub), Sub = no.
test(8,16) :-
	mgu__eq_test(all x: r(?x,?u),all y: r(?y,?w),f(?u),f(?w)).
test(8,17) :-
	\+ mgu__eq_test(all x: r(?x,?u),all y: r(?y,?w),0,0).
test(8,18) :-
	\+ mgu__eq_test(all x: r(?x),all y: r(0),f(?x),f(0)).
test(8,19) :-
	\+ mgu__eq_test(all x: r(?x,?u),all y: r(?y,?y),f(?u),f(?y)).
   
%%% test auxiliary predicates %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

e2i__test_formula(X,Form1) :-
	e2i__formula(X,Form2),
	obj__formula(Form2),
	Form1 = Form2.

i2e__test_formula(X,Y) :-
	e2i__formula(X,Form),
	obj__formula(Form),
	i2e__expression(Form,Z),
	Y = Z.

e2i__test_derivation(X1,X2) :-
	e2i__derivation(X1,Deriv),
	i2e__derivation(Deriv,X3),
	X3 = X2.

cmp__test_sft(X,Y) :-
	e2i__formula(X,Form1),
	Form1 = [Op,Atom],
	cmp__sft_formula(Op,Atom,Form2),
	e2i__formula(Y,Form3),
	eq__alpha(Form2,Form3).

eq__test_instance(X1,X2,Sub) :-
	e2i__formula(X1,Expr1),
	e2i__formula(X2,Expr2),
	eq__match(Expr1,Expr2,Sub).

eq__apply_test(X,VL,XL,Y) :-
	e2i__formula(X,Form1),
	e2i__formulaL(XL,TermL),
	eq__make_sub(VL,TermL,_,Sub),
	eq__apply_plain(Form1,Sub,Form2),
	i2e__expression(Form2,Y).

mgu__test(X1,X2,Y) :-
	e2i__expression(X1,Term1),
	e2i__expression(X2,Term2),
	(	mgu__unify_terms_sub(Term1,Term2,Sub) -> 
		i2e__subL(Sub,Y)
	; 	Y = no
	).

mgu__eq_test(X1,X2,X3,X4) :-
	e2i__formula(X1,Form1),
	e2i__formula(X2,Form2),
	e2i__formula(X3,Term1),
	e2i__formula(X4,Term2),
	mgu__unify_terms_part(Term1,Term2,Part),
	mgu__expr_eq(Form1,Form2,Part).

eq__exp_test(X1,X2,X3) :-
	e2i__formula(X1,Form1),
	e2i__formula(X2,Form2),
	e2i__formulaL(X3,FormL),
	pr__extract_eqs(FormL,[],TermLL),
	eq__expr_eq(Form1,Form2,TermLL).

eq__test_match(X1,X2,XL,Sub) :-
	e2i__formula(X1,Expr1),
	e2i__formula(X2,Expr2),
	eq__match_constrained(Expr1,Expr2,XL,[],Sub).

ind__step_alphaL([],[]).
ind__step_alphaL([step(V1L,Form1L,Deriv,Form1)|Step1L],
	[step(V2L,Form2L,Deriv,Form2)|Step2L]) :-
	eq__alpha_extend(V1L,V2L,[],AL),
	eq__alpha_bound(Form1,Form2,AL),
	eq__alpha_boundL(Form1L,Form2L,AL),
	ind__step_alphaL(Step1L,Step2L).

%%% test control predicates %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

test(N) :- 
	test_max(M),
	N =< M,
	\+ test_not(N).

test_not(N) :-	
	test_max(N,K), test_gen(K,1,J), \+ test_ok(N,J).


test_gen(_,M,M).
test_gen(K,M1,J) :-
	M1 < K,
	M2 is M1 + 1,
	test_gen(K,M2,J).

test_ok(N,J) :-
	write(test(N,J)),
	test(N,J),
	write(' O.K.'), nl.

test :-
	initialize,
	needs_gr($(test)/boot/lists),
	\+ test_not,
	write('*** test o.k.'), nl.

test_not :-
	test_max(M),
	test_gen(M,0,N),
	\+ test_ok(N).

test_ok(N) :-
	write(test(N)),
	\+ test_ok_not(N),
	write(' O.K.'), nl.

test_ok_not(N) :-
	test_max(N,K),
	test_gen(K,1,J),
	\+ test(N,J).

:- initialization(test).

% End of test.pl
