:- module(predExists_predForall2,_).

:- use_module(appendListOfDisjs).
:- use_module(canonical).
:- use_module(library(ppl)).

:- use_module(input_ppl).

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
	makePolyhedron([C1],H1),
	c2h(Cs,Hs).
c2h(C1,H1) :-
	makePolyhedron([C1],H1).
	
% negCon(Constraint,NegConstraintAsDisjunctionListOrConjunctionList).

negCon(X = Y,(X > Y; X < Y)).
negCon(X > Y,(X =< Y)).
negCon(X >= Y, (X < Y)).
negCon(X < Y,(X >= Y)).
negCon(X =< Y, (X > Y)).
negCon(false, (0=0)).
negCon(true,(0>1)).

negCon((C1,C2), NegC1C2) :-
	negCon(C1,NegC1),
	negCon(C2,NegC2),
	appendListsOfDisjoints(NegC1,NegC2,NegC1C2).

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


conjunctDNF(C1,C2,DnfAppOfC1C2) :-
	isDisjunction(C1),
	isDisjunction(C2),!,
	dnf_bothDisjunctions(C1,C2,DnfAppOfC1C2).

conjunctDNF(C1,C2,DnfAppOfC1C2) :-
	isDisjunction(C1),
	notDisjunction(C2),!,
	dnf_FirstOnlyDisjunction(C1,C2,DnfAppOfC1C2).

conjunctDNF(C1,C2,DnfAppOfC1C2) :-
	notDisjunction(C1),
	isDisjunction(C2),!,
	dnf_SecondOnlyDisjunction(C1,C2,DnfAppOfC1C2).

conjunctDNF(C1,C2,DnfAppOfC1C2) :-
	notDisjunction(C1),
	notDisjunction(C2),!,
	dnf_bothNotDisjunctions(C1,C2,DnfAppOfC1C2).

dnf_bothNotDisjunctions(C1,C2,(C1,C2)).

dnf_FirstOnlyDisjunction(C1,C2,(C1,C2)) :-
	notDisjunction(C1),!.

dnf_FirstOnlyDisjunction((C1;C1s),C2,((C1,C2);DnfAppOfC1C2)) :-
	dnf_FirstOnlyDisjunction(C1s,C2,DnfAppOfC1C2).

dnf_SecondOnlyDisjunction(C1,C2,DnfAppOfC1C2) :-
	dnf_FirstOnlyDisjunction(C2,C1,DnfAppOfC1C2).

dnf_bothDisjunctions(C1,C2,DnfAppOfC1C2) :-
	dnf_bothDisjunctions1(C1,C2,empty_constraint,DnfAppOfC1C2).

dnf_bothDisjunctions1(C1,(C2;C2s),empty_constraint,DnfAppOfC1C2) :-
	dnf_FirstOnlyDisjunction(C1,C2,TempDnfAppOfC1C2),!,
	dnf_bothDisjunctions1(C1,C2s,TempDnfAppOfC1C2,DnfAppOfC1C2).

dnf_bothDisjunctions1(C1,(C2;C2s),TempConstraintConjunct,DnfAppOfC1C2) :-
	TempConstraintConjunct \= empty_constraint,
	dnf_FirstOnlyDisjunction(C1,C2,TempDnfAppOfC1SingleC2),!,
	appendListsOfDisjoints(TempConstraintConjunct,TempDnfAppOfC1SingleC2,TempAppDisjs),
	dnf_bothDisjunctions1(C1,C2s,TempAppDisjs,DnfAppOfC1C2).

dnf_bothDisjunctions1(C1,C2,TempConstraintConjunct,FinalDnfAppOfC1C2) :-
	dnf_FirstOnlyDisjunction(C1,C2,TempDnfAppOfC1C2),
	appendListsOfDisjoints(TempConstraintConjunct,TempDnfAppOfC1C2,FinalDnfAppOfC1C2).


isDisjunction(C) :-
	C=(_;_).

notDisjunction(C) :-
	C\=(_;_).

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
	my_clause(H, B), % reading the reachable state program to find the possible predecessors
	H =.. [_|W], % W is the VarList over which constraint-set H1 holds
	getConstraintPart(B,Cs,Y), % Y are variables over which constraints Cs holds
	melt((X,C),(W,C1)),
	append(C1,Cs,Cs2),
	numbervars((Cs2,Y),0,_),
	satisfiable(Cs2,HB),
	project(HB,X,H2).  % project out all variables not in B

predExists((H1;H2),X,Gs) :-
	!,
	predExists(H1,X,G1),
	predExists(H2,X,G2),
	appendListsOfDisjoints(G1,G2,Gs).

/*Replaced by GNB on 19 June 2009 Label j1909.346*/
/*
predExists(H1,X,G1) :-
	findall(H2,pred(H1,X,H2),G),
	(G=[] -> G1=false; buildDisj(G,G1)).
predExists(false,_,false).
*/

/*Begins j1909.346*/
predExists(H1,X,G1) :-
	findall(H2,pred(H1,X,H2),G),
	(G=[] -> G1=(1>0); buildDisj(G,G1)).
predExists(false,_,(1>0)).
/*Ends j1909.346*/


predForall(Hs,X,Gs) :-
	predExists(Hs,X,Ds),
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
	
/* Replaced by GNB 19 June 2009 3:22PM Label j1909*/
/*
satisfiable(Cs,H1) :-
	ppl_new_NNC_Polyhedron_from_constraints(Cs,H1),
	\+ ppl_Polyhedron_is_empty(H1).
*/

/* j1909:Replacement Begins*/
satisfiable(Cs,H1) :-
	sweep4TruesAndFalses(Cs,Cs1),
	ppl_new_NNC_Polyhedron_from_constraints(Cs1,H1),
	\+ ppl_Polyhedron_is_empty(H1).

sweep4TruesAndFalses([],[]).
sweep4TruesAndFalses([C|Cs],[C|Cs1]) :-
	(C \= true ; C \= false),!,
	sweep4TruesAndFalses(Cs,Cs1).
	     
sweep4TruesAndFalses([C|Cs],[(1=1)|Cs1]) :-
	C = true,
	sweep4TruesAndFalses(Cs,Cs1).

sweep4TruesAndFalses([C|Cs],[(1=0)|Cs1]) :-
	C = false,
	sweep4TruesAndFalses(Cs,Cs1).
/* j1909:Replacement Ends*/

	
		     
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