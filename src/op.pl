/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: Fri Dec  2 15:49:17 1994 */
/* Updated: Mon May 29 15:02:48 2000 */ 
/* Filename: op.pl */
/* Abstract: Operator declarations. Comments on built-in predicates. */

%% Special characters (ISO Prolog): # $ & * + - . / : < = > ? @ ^ ~ \

%% Since the backslash \ behaves differently in quoted names in different
%% implementations we take ! as escape character for creating TeX
%% output. For instance, the Prolog atom '!neq' stands for the TeX control
%% sequence \neq (cf. proofmacros.tex).

:- op(980,xfy,by).		% ... by ...
:- op(970,xfy,:).		% two Peano dots, right associative
:- op(960,yfx,<=>).		% equivalence
:- op(950,xfy,=>).		% implication (-> is an operator of Prolog)
:- op(940,yfx,\/).		% disjunction (v can be used as name)
:- op(930,yfx,&).		% conjunction
:- op(900,fy,~).		% negation (cf. not, \+)  
:- op(900,fy,not).		% negation
:- op(900,xfy,'!,').		% empty operator (TeX)
:- op(900,fy,def).		% def
:- op(900,fy,succeeds).		% succeeds
:- op(900,fy,fails).		% fails
:- op(900,fy,terminates).	% terminates
:- op(800,fy,all).		% universal quantifier
:- op(800,fy,ex).		% existential quantifier
:- op(700,yfx,=).		% equality
:- op(700,yfx,:=).		% assignment
:- op(700,yfx,'!eq').		% equality (TeX)
:- op(700,xfy,<>).		% different
:- op(700,xfy,'!neq').		% different (TeX)
:- op(700,xfy,<).		% less (built-in)
:- op(700,xfy,=<).		% less than or equal (built-in)
:- op(700,xfy,@<).		% less (nat)
:- op(700,xfy,@=<).		% less than or equal (nat)
:- op(700,xfy,#<).		% less (int)
:- op(700,xfy,#=<).		% less than or equal (int)
:- op(700,xfy,'!leq').		% less than or equal (TeX)
:- op(700,xfy,'!prec').         % less than (TeX)
:- op(700,xfy,'!preceq').       % less than or equal (TeX)
:- op(700,xfy,'!sub').		% subset (TeX)
:- op(700,xfx,'!is').		% is (TeX)
:- op(600,yfx,//).		% application of substitutions
:- op(600,yfx,'!apply').	% application of substitutions (TeX)
:- op(600,yfx,**).		% concatenation
:- op(600,yfx,'!app').		% concatenation (TeX)
:- op(550,xfy,imp).
:- op(500,yfx,@+).		% sum (nat)
:- op(500,yfx,#+).		% sum (int)
:- op(500,yfx,or).
:- op(500,yfx,#-).		% subtraction (int)
:- op(400,yfx,@*).		% product (nat)
:- op(400,yfx,and).
:- op(400,yfx,#*).		% product (int)
:- op(300,fy,#-).		% minus (int)
:- op(300,fy,neg).
:- op(100,fy,?).		% variables: ?x, ?y, ?z, ?v, ?0, ?1, ?2

%%
%% We use fhe following built-in predicates:
%%
%% In the pure, declarative kernel only the negation as failure operator is 
%% used. We use (almost) no cuts. We use (G1 -> G2; G3). Note, that
%% (G1 -> G2 ; G3 -> G4 ; G5) is parsed as (G1 -> G2 ; (G3 -> G4 ; G5)).
%%
%% Negation:
%%
%%   \+ G: Negation as failure.
%%
%% If-then-else:
%%
%%   (G1 -> G2 ; G3): Tries to execute goal G1, and, if successful, proceeds
%%   to goal G2; otherwise proceeds to goal G3.
%%
%% Arithmetic:
%%
%%   N1 is N2 + N3: N1 is the sum of N2 and N3.
%%   N1 is N2 - N3: N1 is the difference of N2 and N3.
%%   N1 is N2 mod N3: N1 is the rest of dividing N2 by N3.
%%   N1 < N2: N1 is less than N2.
%%   N1 =< N2: N1 is less than or equal to N2.
%%
%% Unification:
%%
%%   T1 = T2: Equality is defined by the fact =(X,X).
%%
%% Type tests:
%%
%%   atom(X): X is an atom.
%%   atomic(X): X is an atom or an integer.
%%   integer(X): X is an integer.
%% 
%% Creating and decomposing terms:
%%
%%   T =.. L: L is the list consisting of the function symbol and the
%%     arguments of T in order, e.g. f(c,d) =.. [f,c,d].
%%   functor(T,F,N): F is the function sumbol of T and N is its arity,
%%     e.g. functor(f(c,d),f,2).
%%
%% Character operations:
%%
%%   concat_atom(L,A): A is the concatenation of the atoms in L,
%%     e.g. concat_atom([pro,log],prolog).
%%   name(A,L): L ist the list of ASCII codes of the atom A,
%%     e.g. name(prolog,[112,114,111,108,111,103]).
%%   atomic_length(A,N): N is the number of characters of the atom A.
%%     e.g. atomic_length(prolog,6).
%%
%% List Predicates:
%%
%%   length(L,N): N is the lenght of the list L.
%%
%% Input and Output:
%%
%%   write(T): Write T to the current output stream.
%%   writeq(T): Write T to the current output stream in a form readable
%%     by the parser.
%%   nl: Write a newline character to the current output stream.
%%   read(T): Read a term from the current input stream.
%%   close(S): Close stream S.
%%
%% The following I/O predicates are defined in the files
%% {cprolog,eclipse,open,quintus,sicstus}.pl
%%
%%   io__get_stream(F,write,S): Open file F to write and return a stream S.
%%   io__get_stream(F,read,S): Open file F to read and return a stream S.
%%   io__set_output(S): Set the current output stream to S.
%%   io__set_input(S): Set the current input stream to S.
%%   io__original_user(S): S is the original input stream (user).
%%
%% Manipulating the knowledge base:
%%
%%   dynamic(P/N): Predicate P with arity N is dynamic. Facts can be added to
%%     the knowledge base and removed.
%%   abolish(P/N): Remove the definition of predicate P with arity N.
%%   assert(F): Add the fact F to the knwoledge base.
%%   retract(F): Remove the fact F from the knowledge base.
%%
%% Finding all solutions (only used for creating the ground representation of
%% a Prolog program, in gnd.pl):
%%
%%   setof(Term,Goal,List)
%%   bagof(Term,Goal,List)
%%
%% Non-logical properties of terms (only used for creating the ground
%% representation of a Prolog program, in gnd.pl):
%%
%%   var(X): X is an unbound variable.
%%

% op.pl ends here

