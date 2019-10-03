:- module(amc_all,_).

% Abstract semantics for CTL
% Program requires Yices SMT solver and the following modules (available from jpg@ruc.dk)

:- use_module(input_ppl).
:- use_module(chclibs(yices2_sat)).  

:- use_module(ciao_yices(ciao_yices_2)).


:- dynamic(version/3).
:- dynamic(predExistsVersion/3).

% go(+File,+VersionsFile,+PredFile, +Phi,-S)
%   File - CLP representation of transition system
%   VersionsFile - File containing regions (abstraction of reachable states)
%   PredFile -File containing predecessor table
%   Phi - CTL formula to be checked
%   S - set of regions where Phi holds


go(File,VersionsFile,PredFile, Phi,S) :-
	load_file(File,pl),
	readVersions(VersionsFile),
	readPredTable(PredFile),
	yices_init,
	states(Phi,S),
	yices_exit.
	
testId(Id,File,Versions,Preds,Phi) :-
	S = user_output,
	write(S,'Test ID: '), write(S,Id),nl(S),
	write(S,'System: '), write(S, File),nl(S),
	write(S,'Versions: '), write(S, Versions), nl(S),
	write(S,'CTL Formula: '), write(S,Phi),nl(S),
	go(File,Versions,Preds,Phi,Ss),
	write(S,'States: '), write(Ss), nl(S),
	write(S,'========================'),nl(S).



%---------------


states(Formula,StatesWhereFormulaHolds) :-
	nnf(Formula, NNF_Formula),
	sat(NNF_Formula, StatesWhereFormulaHolds).

sat(true,S) :-
	allStates(S).
sat(false,[]).

sat(prop(P),States) :- 
	prop(P,States). /* elementary proposition */
sat(neg(prop(P)),States) :- 
	prop(neg(P),States). /* elementary proposition */
sat(and(F1,F2),States) :-
	sat(F1,F1States),
	sat(F2,F2States),
	setintersect(F1States,F2States,States).
sat(or(F1,F2),States) :-
	sat(F1,F1States),
	sat(F2,F2States),
	setunion(F1States,F2States,States).
sat(ex(F),States) :- /* Exists neXt */
	sat(F,States_1),
	predExists(States_1,States).
sat(ax(F),States) :- /* Always neXt */
	sat(F,States_1),
	predForall(States_1,States).
sat(af(F),States) :- /* Always in Future */
	sat(F,FStates),
	lfp_af(FStates,States).
sat(ef(F),States) :- /* Exists in Future */
	sat(F,FStates),
	lfp_ef(FStates,States).
sat(ag(F),States) :- /* Always Globally */
	sat(F,FStates),
	gfp_ag(FStates,States).
sat(eg(F),States) :- /* Exists Globally */
	sat(F,FStates),
	gfp_eg(FStates,States).
sat(ar(F1,F2),States) :- /* Always Release */
	sat(F1,F1States),
	sat(F2,F2States),
	gfp_ar(F1States,F2States,States).
sat(er(F1,F2),States) :- /* Always Release */
	sat(F1,F1States),
	sat(F2,F2States),
	gfp_er(F1States,F2States,States).
sat(au(F1,F2),States) :- /* Always Until */
	sat(F1,F1States),
	sat(F2,F2States),
	lfp_au(F1States,F2States,States).
sat(eu(F1,F2),States) :- /* Always Until */
	sat(F1,F1States),
	sat(F2,F2States),
	lfp_eu(F1States,F2States,States).
	


lfp(Z,E, S1) :-
	lfp_iteration([], Z, E, S1).

lfp_iteration(Prev, Z, E, Fix) :-
	apply_arg(Z,Prev,E,E1),	
	allStates(Rs),
	evalExpr(E1,Rs,Next),
	lfp_check_fix(Next,Prev,Z,E,Fix).

lfp_check_fix(E1,Prev,_,_,Fix) :-
	subset(E1,Prev),
	!,
	return_fixpoint(E1,Fix).
lfp_check_fix(E1,_,Z,E,Fix) :-
	lfp_iteration(E1, Z, E, Fix).


gfp(Z,E, S1) :-
	allStates(S),
	gfp_iteration(S, Z, E, S1).

gfp_iteration(Prev, Z, E, Fix) :-
	apply_arg(Z,Prev,E,E1),	
	evalExpr(E1,Prev,Next),
	gfp_check_fix(Next,Prev,Z,E,Fix).

gfp_check_fix(E1,Prev,_,_,Fix) :-
	subset(Prev,E1),
	!,
	return_fixpoint(E1,Fix).
gfp_check_fix(E1,_,Z,E,Fix) :-
	gfp_iteration(E1, Z, E, Fix).
	
return_fixpoint(X,X).


apply_arg(V,X,T,X) :-
        T == V,
        !.
apply_arg(_,_,T,T) :-
        var(T),
        !.
apply_arg(V,X,T,T1) :-
        nonvar(T),
        T =.. [F|Us],
        apply_all(Us,V,X,Vs),
        T1 =.. [F|Vs].

apply_all([U|Us],V,X,[W|Ws]) :-
        apply_arg(V,X,U,W),
        apply_all(Us,V,X,Ws).
apply_all([],_,_,[]).


%---------------------------------
	
evalExpr(union(E1,E2),Rs,S3) :-
	evalExpr(E1,Rs,S1),
	evalExpr(E2,Rs,S2),
	setunion(S1,S2,S3).
evalExpr(intersect(E1,E2),Rs,S3) :-
	evalExpr(E1,Rs,S1),
	evalExpr(E2,Rs,S2),
	setintersect(S1,S2,S3).
evalExpr(predExists(S1),Rs,S2) :-
	predExists3(S1,Rs,S2).
evalExpr(predForall(S1),Rs,S2) :-
	predForall3(S1,Rs,S2).
evalExpr([],_,[]).
evalExpr([S|Ss],Rs,RSs) :-
	setintersect([S|Ss],Rs,RSs).
	
lfp_af(F,S) :-
	lfp('$VAR'('Z'), union(F,predForall('$VAR'('Z'))), S).
lfp_ef(F,S) :-
	lfp('$VAR'('Z'), union(F,predExists('$VAR'('Z'))), S).
lfp_au(F1,F2,S) :-
	lfp('$VAR'('Z'), union(F2,intersect(F1,predForall('$VAR'('Z')))), S).
lfp_eu(F1,F2,S) :-
	lfp('$VAR'('Z'), union(F2,intersect(F1,predExists('$VAR'('Z')))), S).
	
gfp_ag(F,S) :-
	gfp('$VAR'('Z'), intersect(F,predForall('$VAR'('Z'))), S).
gfp_eg(F,S) :-
	gfp('$VAR'('Z'), intersect(F,predExists('$VAR'('Z'))), S).
gfp_ar(F1,F2,S) :-
	gfp('$VAR'('Z'), intersect(F2,union(F1,predForall('$VAR'('Z')))), S).
gfp_er(F1,F2,S) :-
	gfp('$VAR'('Z'), intersect(F2,union(F1,predExists('$VAR'('Z')))), S).
	
prop(P,States) :-
	allStates(Rs),
	smt_alpha(P,Rs,States).
	
predExists(S1,S2) :-
	allStates(Rs),
	predExists3(S1,Rs,S2).
	
predExists3(S1,Rs,S2) :-
	predExistsLookup(S1,Ds),
	smt_alpha(Ds,Rs,S2).
	
predExistsLookup([S],C) :-
	!,
	predExistsVersion(S,T,C),
	numbervars((T,C),0,_).
predExistsLookup([S|Ss],(C;Cs)) :-
	predExistsVersion(S,T,C),
	numbervars((T,C),0,_),
	predExistsLookup(Ss,Cs).
predExistsLookup([],0<0).
	
predForall(S1,S2) :-
	allStates(Rs),
	predForall3(S1,Rs,S2).
	
predForall3(S1,Rs,S2) :-
	predExistsLookup(S1,Ds),
	allStates(Ss),
	setdiff(Ss,S1,SC),
	predExistsLookup(SC,DsC),
	smt_alpha((Ds,neg(DsC)),Rs,S2).   % uses SMT solver yices.

getVars(Xs) :-
	version(_,F,_),
	numbervars(F,0,_),
	!,
	F =.. [_|Xs].
	
smt_alpha(false,_,[]) :-
	!.
smt_alpha(E,Rs,Ss) :-
	setof(S,smt_consistentRegion(E,Rs,S),Ss),
	!.
smt_alpha(_,_,[]).

smt_consistentRegion(E,Rs,S) :-
	version(S,F,Cs),
	member(S,Rs),	% ignore regions that are not in the restricted set Rs
	numbervars((F,Cs),0,_),
	disjList2Conj(Cs,Cs1),
	getVars(Vs),	
	%insterted 30 Sep 2019
	yices_vars(Vs,real,Ws),
	%instert ends 30 Sep 2019
	yices_sat((Cs1,E),Ws).

disjList2Conj((C1;C2),(D1;D2)) :-
	!,
	disjList2Conj(C1,D1),
	disjList2Conj(C2,D2).
disjList2Conj(C,D) :-
	list2conj(C,D).
	
list2conj([C],C) :-
	!.
list2conj([C|Cs],(C,Ds)) :-
	!,
	list2conj(Cs,Ds).


conj2list((C,Cs),Cs1,[C|Cs2]) :-
	!,
	conj2list(Cs,Cs1,Cs2).
conj2list(C,Cs1,[C|Cs1]).
	
allStates(Ss) :-
	setof(S,[C,F]^predExistsVersion(S,F,C),Ss).


readVersions(File) :-
	retractall(version(_,_,_)),
	open(File,read,S),
	readFacts(S),
	close(S).
	
readFacts(S) :-
	read(S,C),
	(
	    C == end_of_file -> true
	;
	    assert(C),
	    readFacts(S)
	).
	
readPredTable(File) :-
	retractall(predExistsVersion(_,_,_)),
	open(File,read,S),
	readFacts(S),
	close(S).
	
appendListsOfDisjoints((D;Ds),Es,(D;Fs)) :-
	!,
	appendListsOfDisjoints(Ds,Es,Fs).
appendListsOfDisjoints(D,Ds,(D;Ds)).

appendListsOfDisjoints((D;Ds),Es,(D;Fs)) :-
	!,
	appendListsOfDisjoints(Ds,Es,Fs).
appendListsOfDisjoints(D,Ds,(D;Ds)).

%-----------------

% negated normal form

nnf(true, true).
nnf(false, false).
nnf(neg(true),false).
nnf(neg(false),true).
nnf(prop(P),prop(P)).
nnf(neg(prop(P)),neg(prop(P))).
nnf(ax(F),ax(F_nnf)) :-
	nnf(F,F_nnf).
nnf(neg(ax(F)),ex(NegF_nnf)) :-
	nnf(neg(F),NegF_nnf).	
nnf(ex(F),ex(F_nnf)) :-
	nnf(F,F_nnf).
nnf(neg(ex(F)),ax(NegF_nnf)) :-
	nnf(neg(F),NegF_nnf).
nnf(af(F), af(F_nnf)) :-
	nnf(F,F_nnf).	
nnf(neg(af(F)), eg(NegF_nnf)) :-
	nnf(neg(F),NegF_nnf).
nnf(ag(F), ag(F_nnf)) :-
	nnf(F,F_nnf).	
nnf(neg(ag(F)), ef(NegF_nnf)) :-
	nnf(neg(F),NegF_nnf).
nnf(ar(F1,F2), ar(F1_nnf,F2_nnf)) :-
	nnf(F1,F1_nnf),
	nnf(F2,F2_nnf).	
nnf(neg(ar(F1,F2)), eu(NegF1_nnf,NegF2_nnf)) :-
	nnf(neg(F1),NegF1_nnf),
	nnf(neg(F2),NegF2_nnf).
nnf(au(F1,F2), au(F1_nnf,F2_nnf)) :-
	nnf(F1,F1_nnf),
	nnf(F2,F2_nnf).	
nnf(neg(au(F1,F2)), er(NegF1_nnf,NegF2_nnf)) :-
	nnf(neg(F1),NegF1_nnf),
	nnf(neg(F2),NegF2_nnf).
nnf(ef(F), ef(F_nnf)) :-
	nnf(F,F_nnf).	
nnf(neg(ef(F)), ag(NegF_nnf)) :-
	nnf(neg(F),NegF_nnf).
nnf(eg(F), eg(F_nnf)) :-
	nnf(F,F_nnf).	
nnf(neg(eg(F)), af(NegF_nnf)) :-
	nnf(neg(F),NegF_nnf).
nnf(er(F1,F2), er(F1_nnf,F2_nnf)) :-
	nnf(F1,F1_nnf),
	nnf(F2,F2_nnf).	
nnf(neg(er(F1,F2)), au(NegF1_nnf,NegF2_nnf)) :-
	nnf(neg(F1),NegF1_nnf),
	nnf(neg(F2),NegF2_nnf).
nnf(eu(F1,F2), eu(F1_nnf,F2_nnf)) :-
	nnf(F1,F1_nnf),
	nnf(F2,F2_nnf).	
nnf(neg(eu(F1,F2)), ar(NegF1_nnf,NegF2_nnf)) :-
	nnf(neg(F1),NegF1_nnf),
	nnf(neg(F2),NegF2_nnf).
nnf(and(F,G), and(F_nnf,G_nnf)) :-
	nnf(F,F_nnf),
	nnf(G,G_nnf).	
nnf(neg(and(F,G)), or(NegF_nnf,NegG_nnf)) :-
	nnf(neg(F),NegF_nnf),
	nnf(neg(G),NegG_nnf).
nnf(or(F,G), or(F_nnf,G_nnf)) :-
	nnf(F,F_nnf),
	nnf(G,G_nnf).
nnf(neg(or(F,G)), and(NegF_nnf,NegG_nnf)) :-
	nnf(neg(F),NegF_nnf),
	nnf(neg(G),NegG_nnf).
nnf(implies(F,G), or(NegF_nnf,G_nnf)) :-
	nnf(neg(F),NegF_nnf),
	nnf(G,G_nnf).
nnf(neg(implies(F,G)), NegImplies_F_G) :-
	nnf(implies(F,G),Implies_F_G_nnf),
	nnf(neg(Implies_F_G_nnf),NegImplies_F_G).	
nnf(neg(neg(F)),F_nnf) :-
	nnf(F,F_nnf),!.

setintersect([],_,[]).
setintersect([X|Xs],Vs,[X|Ws]) :-
	memb3(X,Vs),
	!,
	setintersect(Xs,Vs,Ws).
setintersect([_|Xs],Vs,Ws) :-
	setintersect(Xs,Vs,Ws).
	
setunion([],X,X).
setunion([X|Xs],Vs,Ws) :-
	memb3(X,Vs),
	!,
	setunion(Xs,Vs,Ws).
setunion([X|Xs],Vs,[X|Ws]) :-
	setunion(Xs,Vs,Ws).
	
setdiff([],_,[]).
setdiff([X|Xs],Ys,Zs) :-
	memb3(X,Ys),
	!,
	setdiff(Xs,Ys,Zs).
setdiff([X|Xs],Ys,[X|Zs]) :-
	setdiff(Xs,Ys,Zs).
	
subset(X,Y) :-
        \+ (member(Z,X), \+ memb3(Z,Y)).
	
memb3(X,[X1|_]) :-
	X == X1,
	!.
memb3(X,[_|Xs]) :-
	memb3(X,Xs).
