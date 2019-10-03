:- module(predExists_predForall2,_).

:- use_module(appendListOfDisjs).
:- use_module(canonical).
:- use_module(setops).
:- use_module(input_ppl).
:- use_module(library(terms_vars)).
:- use_module(library(ppl)).


%:- dynamic my_clause/2.

negHandleCon(H1,H2) :-
	h2c(H1,C1),
	negCon(C1,C2),
	c2h(C2,H2).
	
h2c((H1;Hs),(C2;Cs2)) :-
	!,
	getConstraint(H1,C1),
	list2conj(C1,C2),
	h2c(Hs,Cs2).
h2c(H1,C2) :-
	getConstraint(H1,C1),
	list2conj(C1,C2).
	
list2conj([C],C) :-
	!.
list2conj([C|Cs],(C,Ds)) :-
	!,
	list2conj(Cs,Ds).

c2h((C1;Cs),(H1;Hs)) :-
	!,
	tuple2list(C1,L1),
	makePolyhedron(L1,H1),
	c2h(Cs,Hs).
c2h(C1,H1) :-
	tuple2list(C1,L1),
	makePolyhedron(L1,H1).
	
% negCon(Constraint,NegConstraintAsDisjunctionListOrConjunctionList).

negCon(X = Y,(X > Y; X < Y)).
negCon(X > Y,(X =< Y)).
negCon(X >= Y, (X < Y)).
negCon(X < Y,(X >= Y)).
negCon(X =< Y, (X > Y)).
negCon(false, (0>=0)).

negCon((C1,C2), NegC1C2) :-
	negCon(C1,NegC1),
	negCon(C2,NegC2),
	appendListsOfDisjoints(NegC1,NegC2,NegC1C2).

negCon((0<1;_), 0>1) :-
	!.
negCon((_;0<1), 0>1) :-
	!.
negCon((0>1;C2), NegC2) :-
	!,
	negCon(C2,NegC2).
negCon((C1;0>1), NegC1) :-
	!,
	negCon(C1,NegC1).
negCon((C1;C2), NegC1C2) :-
	negCon(C1,NegC1),
	negCon(C2,NegC2),
	conjunctDNF(NegC1,NegC2,NegC1C2).
	
constraint2Handles((C1;C2),(H1;H2)) :-
	!,
	makePolyhedron([C1],H1),
	makePolyhedron([C2],H2).
constraint2Handles(C1,H1) :-
	makePolyhedron([C1],H1).

conjunctDNF((0<1;_),Ds2,Ds3) :-
	!,
	distribute(Ds2,0<1,Ds3).
conjunctDNF((0>1;Ds1),Ds2,Ds3) :-
	!,
	conjunctDNF(Ds1,Ds2,Ds3).
conjunctDNF((D;Ds1),Ds2,Ds3) :-
	!,
	distribute(Ds2,D,Ds4),
	conjunctDNF(Ds1,Ds2,Ds5),
	appendListsOfDisjoints(Ds4,Ds5,Ds3).
conjunctDNF(D,Ds2,Ds3) :-
	distribute(Ds2,D,Ds3).
	
distribute(Ds2,0<1,Ds2) :-
	!.
distribute((D2;Ds2),D1,(D3;Ds3)) :-
	!,
	appendConj(D1,D2,D3),
	distribute(Ds2,D1,Ds3).
distribute(D2,D1,D3) :-
	appendConj(D1,D2,D3).
	
appendConj((C,Cs1),Cs2,(C,Cs3)) :-
	!,
	appendConj(Cs1,Cs2,Cs3).
appendConj(C,Cs2,(C,Cs2)).

tuple2list((X,Xs),[X|TList]) :- 
	!,
	tuple2list(Xs,TList).
tuple2list(X,[X]).


%/*
%
%conjunctDNF(C1,C2,DnfAppOfC1C2) :-
%	isDisjunction(C1),
%	isDisjunction(C2),!,
%	dnf_bothDisjunctions(C1,C2,DnfAppOfC1C2).
%
%conjunctDNF(C1,C2,DnfAppOfC1C2) :-
%	isDisjunction(C1),
%	notDisjunction(C2),!,
%	dnf_FirstOnlyDisjunction(C1,C2,DnfAppOfC1C2).
%
%conjunctDNF(C1,C2,DnfAppOfC1C2) :-
%	notDisjunction(C1),
%	isDisjunction(C2),!,
%	dnf_SecondOnlyDisjunction(C1,C2,DnfAppOfC1C2).
%
%conjunctDNF(C1,C2,DnfAppOfC1C2) :-
%	notDisjunction(C1),
%	notDisjunction(C2),!,
%	dnf_bothNotDisjunctions(C1,C2,DnfAppOfC1C2).
%	
%*/

%/* Replaced by GNB on 20 June 2009 Label: 20June2009_1626
%
%dnf_bothNotDisjunctions(C1,C2,(C1,C2)).
%
%*/

%/*Replacement Begins Label 20June2009_1626*/
%dnf_bothNotDisjunctions(C1,C2,C1C2) :-
%	tuple2list(C1,C1L),
%	tuple2list(C2,C2L),
%	append(C1L,C2L,C1C2List),
%	list2tuple(C1C2List,C1C2).
%
%list2tuple([H],(H)).
%list2tuple([H|T],(H,Hs)) :-
%	list2tuple(T,Hs).
%
%
%tuple2list((X,Xs),[X|TList]) :- 
%	!,
%	tuple2list(Xs,TList).
%tuple2list(X,[X]).
%
%/*Replacement Ends Label 20June2009_1626*/


%/*Replaced by GNB 20June2009 Label:20June09:1908
%dnf_FirstOnlyDisjunction(C1,C2,(C1,C2)) :-
%	notDisjunction(C1),!.
%*/	
%
%/*Begins Label:20June09:1908*/
%dnf_FirstOnlyDisjunction(C1,C2,C1C2) :-
%	notDisjunction(C1),!,
%	tuple2list(C1,C1L),
%	tuple2list(C2,C2L),
%	append(C1L,C2L,C1LC2L),
%	list2tuple(C1LC2L,C1C2).
%/*Ends Label:20June09:1908*/
%
%
%/*Replaced by GNB 20June2009 Label:20June09:1912
%
%dnf_FirstOnlyDisjunction((C1;C1s),C2,((C1,C2);DnfAppOfC1C2)) :-
%	dnf_FirstOnlyDisjunction(C1s,C2,DnfAppOfC1C2).
%*/
%
%/*Replacement Begins Label:20June09:1912*/
%dnf_FirstOnlyDisjunction((C1;C1s),C2,(C1C2;DnfAppOfC1C2)) :-
%	tuple2list(C1,C1L),
%	tuple2list(C2,C2L),
%	append(C1L,C2L,C1LC2L),
%	list2tuple(C1LC2L,C1C2),
%	dnf_FirstOnlyDisjunction(C1s,C2,DnfAppOfC1C2).
%/*Replacement Ends Label:20June09:1912*/
%
%dnf_SecondOnlyDisjunction(C1,C2,DnfAppOfC1C2) :-
%	dnf_FirstOnlyDisjunction(C2,C1,DnfAppOfC1C2).
%
%dnf_bothDisjunctions(C1,C2,DnfAppOfC1C2) :-
%	dnf_bothDisjunctions1(C1,C2,empty_constraint,DnfAppOfC1C2).
%
%dnf_bothDisjunctions1(C1,(C2;C2s),empty_constraint,DnfAppOfC1C2) :-
%	dnf_FirstOnlyDisjunction(C1,C2,TempDnfAppOfC1C2),!,
%	dnf_bothDisjunctions1(C1,C2s,TempDnfAppOfC1C2,DnfAppOfC1C2).
%
%dnf_bothDisjunctions1(C1,(C2;C2s),TempConstraintConjunct,DnfAppOfC1C2) :-
%	TempConstraintConjunct \= empty_constraint,
%	dnf_FirstOnlyDisjunction(C1,C2,TempDnfAppOfC1SingleC2),!,
%	appendListsOfDisjoints(TempConstraintConjunct,TempDnfAppOfC1SingleC2,TempAppDisjs),
%	dnf_bothDisjunctions1(C1,C2s,TempAppDisjs,DnfAppOfC1C2).
%
%dnf_bothDisjunctions1(C1,C2,TempConstraintConjunct,FinalDnfAppOfC1C2) :-
%	dnf_FirstOnlyDisjunction(C1,C2,TempDnfAppOfC1C2),
%	appendListsOfDisjoints(TempConstraintConjunct,TempDnfAppOfC1C2,FinalDnfAppOfC1C2).
%
%
%isDisjunction(C) :-
%	C=(_;_).
%
%notDisjunction(C) :-
%	C\=(_;_).

buildDisj([A],C1) :-
	!,
	getConstraint(A,C),
	list2conj(C,C1).
buildDisj([A|As],(C1;B)) :-
	!,
	getConstraint(A,C),
	list2conj(C,C1),
	buildDisj(As,B).
buildDisj([],1=0).


pred(H1,X,H2) :-
	getConstraint(H1,C),
	my_clause(H, B), 	% reading the reachable state program to find the possible predecessors
	H =.. [_|W], 		% W is the VarList over which constraint-set H1 holds
	varset((H,B), Xs), 	% Xs is the set of all variables in the clause
	getConstraintPart(B,Cs,Y), % Y are variables of the predecessor state
	setdiff(Xs,Y,Zs),	% Zs are the variables to be eliminated
	melt((X,C),(W,C1)),
	append(C1,Cs,Cs2),
	numbervars((Y,Cs2,Zs),0,_),
	satisfiable(Cs2,HB),
	project(HB,Zs,H2).  % eliminate variables Zs

predExists((H1;H2),X,Gs) :-
	!,
	predExists(H1,X,G1),
	predExists(H2,X,G2),
	appendListsOfDisjoints(G1,G2,Gs).
predExists(H1,X,G1) :-
	findall(H2,pred(H1,X,H2),G),
	(G=[] -> G1=(0<0); buildDisj(G,G1)).

/*Replaced by GNB 20Jun2009 Label: 20June09:1906
predExists(false,_,false).
*/

/* Begins 20June09:1906*/
predExists(false,_,(0<0)).
/* Ends 20June09:1906*/

predForall(Hs,X,Gs) :-
	predExists(Hs,X,Ds),
	%open('expr.txt',write,St),
	%yices_term(St,Ds),nl(St),
	%close(St),
	negHandleCon(Hs,Ns),
	predExists(Ns,X,Es),
	negCon(Es,Fs),
	conjunctDNF(Ds,Fs,Gs).
	
getConstraintPart(B,Cs,Y) :-
	separate_constraints(B,Cs,[R]),
	R =.. [_|Y].
	
separate_constraints([],[],[]).
separate_constraints([B|Bs],[C|Cs],Ds):-
	constraint(B,C),
	!,
	separate_constraints(Bs,Cs,Ds).
separate_constraints([B|Bs],Cs,[B|Ds]):-
	separate_constraints(Bs,Cs,Ds).

constraint(false, 0<0).
constraint(true, 0 >= 0).
constraint(X=Y, X=Y).
constraint(X=:=Y, X=Y).
constraint(X is Y, X = Y).
constraint(X>Y, X>Y).
constraint(X>=Y, X>=Y).
constraint(X=<Y, X=<Y).
constraint(X<Y, X<Y).

constraint(_\==_,0=0).
constraint(_=\=_,0=0).
constraint(true,0=0).
constraint(fail,1=0).

% PPL predicates	
getConstraint(H,Cs0) :-
	ppl_Polyhedron_get_minimized_constraints(H,Cs0).
	
makePolyhedron(Cs,H1)  :-
	ppl_new_NNC_Polyhedron_from_constraints(Cs,H1).
	
satisfiable(Cs,H1) :-
	ppl_new_NNC_Polyhedron_from_constraints(Cs,H1),
	\+ ppl_Polyhedron_is_empty(H1).
	          
project(H,Zs,H) :-
	ppl_Polyhedron_remove_space_dimensions(H,Zs).
	
	
go(File) :-
	ppl_initialize,
	ppl_version(_),
	load_file(File,pl),
	C1 = [X0 >= 0, X1 < 10],
	canonical(C1),
	makePolyhedron(C1,H1),
	predExists(H1,[X0,X1],Gs1),
	%showConstraints(Gs1),
	write(Gs1),nl,
	predForall(H1,[X0,X1],Gs2),
	write(Gs2),nl,
	%showConstraints(Gs2),
	ppl_finalize.
	
showConstraints(true) :-
	!.
showConstraints((H;Cs)) :-
	!,
	getConstraint(H,C),
	write(C),nl,
	showConstraints(Cs).
showConstraints(H) :-
	getConstraint(H,C),
	write(C),nl.
	
