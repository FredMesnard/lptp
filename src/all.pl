%   Author: Robert F. Staerk <staerk@inf.ethz.ch>
%  Created: Wed Jul 21 09:23:16 1999
%  Updated: Wed Jul 21 12:31:05 1999
% Filename: all.pl
% Abstract: This file tests the whole system.
% Usage (traditional): ?- [all].
% Usage (GNU Prolog): sed "s/:-//g" all.pl | lptp

%:- set(tmp,'/tmp').

% Simple tests
:- ['../test/io/test_io.pl'].
:- ['../test/if_then_else/test_if.pl'].
:- ['../test/boot/test.pl'].
% Simple proofs
:- check($(test)/proof/proof1).
:- check($(test)/proof/proof2).
:- check($(test)/proof/proof3).
:- check($(test)/proof/proof4).
:- check($(test)/proof/proof5).
:- check($(test)/proof/proof6).
% The library (Robert Staerk)
:- check($(lib)/nat/nat).
:- check($(lib)/nat/ackermann).
:- check($(lib)/nat/gcd).
:- check($(lib)/nat/int).
:- check($(lib)/list/list).
:- check($(lib)/list/permutation).
:- check($(lib)/list/suffix).
:- check($(lib)/list/reverse).
:- check($(lib)/sort/sort).
:- check($(lib)/sort/mergesort).
:- check($(lib)/graph/transitiveclosure).
:- check($(lib)/builtin/callsort).
:- check($(lib)/builtin/integeraxioms).
:- check($(lib)/builtin/callsortexample).
:- check($(lib)/builtin/bubble).
% A Tautology checker (Robert Staerk)
:- check($(examples)/taut/taut).
% A parser for ISO Prolog (Robert Staerk)
:- check($(examples)/parser/pr/axioms).
:- check($(examples)/parser/pr/precedence).
:- check($(examples)/parser/pr/grammar).
:- check($(examples)/parser/pr/soundness).
:- check($(examples)/parser/pr/completeness).
:- check($(examples)/parser/pr/uniqueness).
:- check($(examples)/parser/pr/termination).
:- check($(examples)/parser/pr/write).
:- check($(examples)/parser/pr/parser).
% AVL-trees (Rene Lehmann & Patrik Fuhrer)
:- check($(examples)/avl/axioms).
:- check($(examples)/avl/ordered).
:- check($(examples)/avl/set).
:- check($(examples)/avl/termination).
:- check($(examples)/avl/balanced).
:- check($(examples)/avl/existence).
:- check($(examples)/avl/avl).
% Min-max and alpha-beta (Dritan Berzati)
:- check($(examples)/alpha/valueaxioms).
:- check($(examples)/alpha/alpha).
% Union-find-based unification algorithm (Guido Vogt & Robert Staerk)
:- check($(examples)/mgu/mgu).
%:- check($(examples)/while/while).

% all.pl ends here

