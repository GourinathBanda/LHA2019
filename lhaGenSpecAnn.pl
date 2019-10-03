:- module(lhaGenSpecAnn,_).

%:- use_module(library(atom2term)).
:- use_module(library(lists)).

:- op(600, xfx, ':=').


genSpec(Tree,S1) :-
	specComponents(Tree, VarDecls, Locs, Inits, Transitions),
	%% write('Specification Components Identified'),nl,
	systemVars(VarDecls,0,VarTable),
	%% write('call to systemVars succeeded'),nl,
	%% standardPart(S1,S2),
	standardPart(VarTable,S1,S2),
	%% write('Standard Part Generated'),nl,
	variablePart(VarTable,S2,S3),
	%% write('Variable Part Generated'),nl,
	locationPart(Locs,S3,S4),
	write('Inits evaluates to:'),write(Inits),nl,
	initPart(Inits,VarTable,S4,S5),
	write('Inits evaluates to:'),write(Inits),nl,
	write('Locs component evaluates to:'),write(Locs),nl,
	invariantPart(Locs,VarTable,S5,S6),
	write('call to invariantPart/4 succeeded '),write(Locs),nl,
	ratePart(Locs,VarTable,S6,S7),
	gammaPart(Transitions,0,VarTable,S7,S8),
	alphaPart(Transitions,0,VarTable,S8,[]).
	%probePart(VarTable,0,S9,[]).
	
specComponents(lha(VarDecls,Locs,Ts),VarDecls, Locs, Inits, Transitions) :-
	write('Ts valuates to:'),nl,
	write(Ts),nl,
	splitTrans(Ts,Inits,Transitions),
	write('Split Trans Succeeded'),nl.
	

%% systemVars takes vardecl and initial counter, thus producing a variable table as explained later.
%% varTable = [var(actualVarID, allocatedID, type),...,var(time,allocatedTimeID,rational)].

systemVars([],J,[var(time,'$VAR'(J),rational)]).
systemVars([vardecl(Type,V)|Vs],J,[var(V,'$VAR'(J),Type)|VarTable]) :-
	J1 is J+1,
	systemVars(Vs,J1,VarTable).

timeVar(State,T) :-
	last(State,T).

%% takes VarTable and generates the StateArg (a list of state vars not including the location)	
copyVars2(Vs,Vs1) :-
	length(Vs,N),
	X is 2*N,
	copyState(Vs,Vs1,X).

copyVars(Vs,Vs1) :-
	length(Vs,N),
	copyState(Vs,Vs1,N).
	
copyState([],[],_).
copyState([var(_,'$VAR'(J),_)|Vs],['$VAR'(J1)|Vs1],N) :-
	J1 is J+N,
	copyState(Vs,Vs1,N).
	
stateArg([],[]).
stateArg([var(_,'$VAR'(J),_)|Vs],['$VAR'(J)|Vs1]) :-
	stateArg(Vs,Vs1).

%% standardPart([locationOf(['$VAR'('Loc')|'$VAR'('_')],'$VAR'('Loc'))|S0],S0).

standardPart(VarTable,[(logen(P/N,C))|S0],S0) :-
	C = (locationOf(['$VAR'('Loc')|UList],'$VAR'('Loc'))),
	generateUList(VarTable,UList),
	functor(C,P,N).	


variablePart(VarTable,[C1,C2|S0],S0) :-
	stateArg(VarTable,State),
	copyVars(VarTable,State1),
	timeVar(State,T),
	timeVar(State1,T1),
	L = '$VAR'('Loc'),
	U = '$VAR'('_'),
	length(VarTable,N),
	NumberOfSysVars is N-1,
	generateList(U,NumberOfSysVars,Un2List),
	append(Un2List,[T],StateNow),
	append(Un2List,[T1],StateLater),
	HC1 = (before([U|StateNow],[U|StateLater]) :- T =< T1),
	HC1 = (HCH1 :- HCB1),
	functor(HCH1,HCH1P,HCH1PN),
	logenize(HCB1,LogenizedHCB1),
	C1 = ( logen(HCH1P/HCH1PN,HCH1) :- LogenizedHCB1),
	generateList(U,N,UnList),
	HC2 = (stateSpace([L|UnList]) :- location(L)),
	HC2 = (HCH2 :- _HCB2),
	functor(HCH2,HCH2P,HCH2PN),
	%% logenize(HCB2,LogenizedHCB2),
	C2 = ( logen(HCH2P/HCH2PN,HCH2) :- logen(unfold,location(L))).


locationPart([],S0,S0).
locationPart([locdecl(LocId,_,_)|LocDecls],[(logen(P/N,C))|S0],S1) :-
	C = location('$VAR'(LocId)),
	functor(C,P,N),
	locationPart(LocDecls,S0,S1).


/*

invariantPart([],_,S0,S0).
invariantPart([LocDecl|LocDecls],VarTable,[(H :- B)|S0],S1) :-
	invariantHead(LocDecl,VarTable,H),
	invariantBody(LocDecl,VarTable,B),
	invariantPart(LocDecls,VarTable,S0,S1).

*/
	


translateExpr(ident(V),X,Vars) :-
	member(var(V,X,_),Vars).

translateExpr(num(N),N,_).

translateExpr(E1+E2,F1+F2,Vars) :-
	translateExpr(E1,F1,Vars),
	translateExpr(E2,F2,Vars).
translateExpr(E1-E2,F1-F2,Vars) :-
	translateExpr(E1,F1,Vars),
	translateExpr(E2,F2,Vars).
translateExpr(E1*E2,F1*F2,Vars) :-
	translateExpr(E1,F1,Vars),
	translateExpr(E2,F2,Vars).
translateExpr(E1/E2,F1/F2,Vars) :-
	translateExpr(E1,F1,Vars),
	translateExpr(E2,F2,Vars).
translateExpr(E1 mod E2,F1 mod F2,Vars) :-
	translateExpr(E1,F1,Vars),
	translateExpr(E2,F2,Vars).
translateExpr(E1 := E2,F1 := F2,Vars) :-
	translateExpr(E1,F1,Vars),
	translateExpr(E2,F2,Vars).
translateExpr(E1 == E2,F1 = F2,Vars) :-
	translateExpr(E1,F1,Vars),
	translateExpr(E2,F2,Vars).
translateExpr(E1 = E2,F1 = F2,Vars) :-
	translateExpr(E1,F1,Vars),
	translateExpr(E2,F2,Vars).
translateExpr(E1 > E2,F1 > F2,Vars) :-
	translateExpr(E1,F1,Vars),
	translateExpr(E2,F2,Vars).
translateExpr(E1 >= E2,F1 >= F2,Vars) :-
	translateExpr(E1,F1,Vars),
	translateExpr(E2,F2,Vars).
translateExpr(E1 < E2,F1 < F2,Vars) :-
	translateExpr(E1,F1,Vars),
	translateExpr(E2,F2,Vars).
translateExpr(E1 =< E2,F1 =< F2,Vars) :-
	translateExpr(E1,F1,Vars),
	translateExpr(E2,F2,Vars).
translateExpr(or(E1,E2),(F1;F2),Vars) :-
	translateExpr(E1,F1,Vars),
	translateExpr(E2,F2,Vars).
translateExpr(and(E1,E2),(F1,F2),Vars) :-
	translateExpr(E1,F1,Vars),
	translateExpr(E2,F2,Vars).

translateExpr(invariant(E),F,VarTable) :-
	translateExpr(E,F,VarTable).


%%[locdecl(loc_0,[derivative(rate(ident(x))=num(+1)),derivative(rate(ident(y))=num(+1))], invariant(num(1)==num(+1))),
%%	locdecl(loc_1,[derivative(rate(ident(x))=num(+1)),derivative(rate(ident(y))=num(+1))]


translateDerivativeExpr(derivative(RateRelation),VarTable,F) :-
	RateRelation =.. [BinaryRelation,Op1,Op2],
	Op1 = (rate(ident(Var))),
	member(var(Var,'$VAR'(J),_),VarTable),
	Op2 = (num(_Val)),
	length(VarTable,L),
	RateVar is J+3*L,
	ReturnExpr =.. [BinaryRelation,'$VAR'(RateVar),Op2],
	translateRateExpr(ReturnExpr,F,VarTable).


translateRateExpr('$VAR'(R),'$VAR'(R),Vars) :-
	length(Vars,L),
	J is R - 3*L,
	member(var(_V,'$VAR'(J),_),Vars).

translateRateExpr(num(N),N,_).

translateRateExpr(E1+E2,F1+F2,Vars) :-
	translateRateExpr(E1,F1,Vars),
	translateRateExpr(E2,F2,Vars).
translateRateExpr(E1-E2,F1-F2,Vars) :-
	translateRateExpr(E1,F1,Vars),
	translateRateExpr(E2,F2,Vars).
translateRateExpr(E1*E2,F1*F2,Vars) :-
	translateRateExpr(E1,F1,Vars),
	translateRateExpr(E2,F2,Vars).
translateRateExpr(E1/E2,F1/F2,Vars) :-
	translateRateExpr(E1,F1,Vars),
	translateExpr(E2,F2,Vars).
translateRateExpr(E1 mod E2,F1 mod F2,Vars) :-
	translateRateExpr(E1,F1,Vars),
	translateRateExpr(E2,F2,Vars).
translateRateExpr(E1 := E2,F1 := F2,Vars) :-
	translateRateExpr(E1,F1,Vars),
	translateRateExpr(E2,F2,Vars).
translateRateExpr(E1 == E2,F1 = F2,Vars) :-
	translateRateExpr(E1,F1,Vars),
	translateRateExpr(E2,F2,Vars).
translateRateExpr(E1 = E2,F1 = F2,Vars) :-
	translateRateExpr(E1,F1,Vars),
	translateRateExpr(E2,F2,Vars).
translateRateExpr(E1 > E2,F1 > F2,Vars) :-
	translateRateExpr(E1,F1,Vars),
	translateRateExpr(E2,F2,Vars).
translateRateExpr(E1 >= E2,F1 >= F2,Vars) :-
	translateRateExpr(E1,F1,Vars),
	translateRateExpr(E2,F2,Vars).
translateRateExpr(E1 < E2,F1 < F2,Vars) :-
	translateRateExpr(E1,F1,Vars),
	translateRateExpr(E2,F2,Vars).
translateRateExpr(E1 =< E2,F1 =< F2,Vars) :-
	translateRateExpr(E1,F1,Vars),
	translateRateExpr(E2,F2,Vars).
translateRateExpr(or(E1,E2),(F1;F2),Vars) :-
	translateRateExpr(E1,F1,Vars),
	translateRateExpr(E2,F2,Vars).
translateRateExpr(and(E1,E2),(F1,F2),Vars) :-
	translateRateExpr(E1,F1,Vars),
	translateRateExpr(E2,F2,Vars).









translateExpr2Vars(ident(V),VarTable,X) :-
	member(var(V,X,_),VarTable).

translateExpr2Vars(num(_),_,true).

translateExpr2Vars(E1+E2,VarTable,(F1,F2)) :-
	translateExpr2Vars(E1,VarTable,F1),
	translateExpr2Vars(E2,VarTable,F2).
translateExpr2Vars(E1-E2,VarTable,(F1,F2)) :-
	translateExpr2Vars(E1,VarTable,F1),
	translateExpr2Vars(E2,VarTable,F2).
translateExpr2Vars(E1*E2,VarTable,(F1,F2)) :-
	translateExpr2Vars(E1,VarTable,F1),
	translateExpr2Vars(E2,VarTable,F2).
translateExpr2Vars(E1/E2,VarTable,(F1,F2)) :-
	translateExpr2Vars(E1,VarTable,F1),
	translateExpr2Vars(E2,VarTable,F2).
translateExpr2Vars(E1 mod E2,VarTable,(F1,F2)) :-
	translateExpr2Vars(E1,VarTable,F1),
	translateExpr2Vars(E2,VarTable,F2).
translateExpr2Vars(E1 := E2,VarTable,(F1,F2)) :-
	translateExpr2Vars(E1,VarTable,F1),
	translateExpr2Vars(E2,VarTable,F2).
translateExpr2Vars(E1 == E2,VarTable,(F1,F2)) :-
	translateExpr2Vars(E1,VarTable,F1),
	translateExpr2Vars(E2,VarTable,F2).
translateExpr2Vars(E1 > E2,VarTable,(F1,F2)) :-
	translateExpr2Vars(E1,VarTable,F1),
	translateExpr2Vars(E2,VarTable,F2).
translateExpr2Vars(E1 >= E2,VarTable,(F1,F2)) :-
	translateExpr2Vars(E1,VarTable,F1),
	translateExpr2Vars(E2,VarTable,F2).
translateExpr2Vars(E1 < E2,VarTable,(F1,F2)) :-
	translateExpr2Vars(E1,VarTable,F1),
	translateExpr2Vars(E2,VarTable,F2).
translateExpr2Vars(E1 =< E2,VarTable,(F1,F2)) :-
	translateExpr2Vars(E1,VarTable,F1),
	translateExpr2Vars(E2,VarTable,F2).
translateExpr2Vars(or(E1,E2),VarTable,(F1;F2)) :-
	translateExpr2Vars(E1,VarTable,F1),
	translateExpr2Vars(E2,VarTable,F2).
translateExpr2Vars(and(E1,E2),VarTable,(F1,F2)) :-
	translateExpr2Vars(E1,VarTable,F1),
	translateExpr2Vars(E2,VarTable,F2).

translateExpr2Vars(invariant(E),VarTable,F) :-
	translateExpr2Vars(E,VarTable,F).


translateExpr2Vars(E1+num(_),VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).
translateExpr2Vars(E1-num(_),VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).
translateExpr2Vars(E1*num(_),VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).
translateExpr2Vars(E1/num(_),VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).
translateExpr2Vars(E1 mod num(_),VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).
translateExpr2Vars(E1 := num(_),VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).
translateExpr2Vars(E1 == num(_),VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).
translateExpr2Vars(E1 > num(_),VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).
translateExpr2Vars(E1 >= num(_),VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).
translateExpr2Vars(E1 < num(_),VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).
translateExpr2Vars(E1 =< num(_),VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).


translateExpr2Vars(num(_)+E1,VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).
translateExpr2Vars(num(_)-E1,VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).
translateExpr2Vars(num(_)*E1,VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).
translateExpr2Vars(num(_)/E1,VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).
translateExpr2Vars(num(_) mod E1,VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).
%% translateExpr2Vars(num(_) := E1,VarTable,(F1)) :-
%%	translateExpr2Vars(E1,VarTable,F1).
translateExpr2Vars(num(_) == E1,VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).
translateExpr2Vars(num(_) > E1,VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).
translateExpr2Vars(num(_) >= E1,VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).
translateExpr2Vars(num(_) < E1,VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).
translateExpr2Vars(num(_) =< E1,VarTable,(F1)) :-
	translateExpr2Vars(E1,VarTable,F1).


flatten(X,X) :-
	atom(X).

flatten(X,X) :-
	X = '$VAR'(_).


flatten((X,T),(X,Y)):-
	vatom(X),
	flatten(T,Y).

flatten(((X,Y),Z),W) :-
	flatten((X,(Y,Z)),W).

vatom('$VAR'(_)).

vatom(X) :-
	atom(X).





%% takes the transitions list and splits them to init list and ordinary transition list

splitTrans([],[],[]).

splitTrans([T|Ts],[T|Inits],Transitions) :-
	write('Split Trans Called'),nl,
	isInit(T),
	splitTrans(Ts,Inits,Transitions).
splitTrans([T|Ts],Inits,[T|Transitions]) :-
	isTransition(T),
	splitTrans(Ts,Inits,Transitions).

isInit(init(_,_)).
isTransition(transition(_,_,_)).

%% init(loc_0,[action(ident(t):=num(+0))]
%% init([loc_0,0,0,0]).

initPart([],_,S0,S0):-
	write('initPart base case reached'),nl.
initPart([init(Loc,Alpha)|Inits],VarTable,[LC|S0],S1) :-
	write('initPart called'),nl,
	C = (init([Loc|StateArg2])),
	write('initPart first fact written'),nl,
	assignments(Alpha,VarTable,AssignedVarsIndexList,AssignedValsList),
	write('assignments call succeeded'),nl,
	stateArg(VarTable,StateArg),
	write('stateArg/2 called'),nl,
	generateInitAlpha(AssignedVarsIndexList,AssignedValsList,StateArg,StateArg1),
	timeVar(StateArg1,TimeVar),
	append(StateArg1Head,[TimeVar],StateArg1),
	append(StateArg1Head,[0],StateArg2),
	functor(C,CP,CN),
	LC= (logen(CP/CN,C)),
	initPart(Inits,VarTable,S0,S1).

generateInitAlpha(AssignedVarsIndexList,AssignedValsList,StateArg,StateArg1) :-
	listRaider12(AssignedVarsIndexList,AssignedValsList,StateArg,StateArg1).

assignments([],_,[],[]):-
	write('assignments call base case reached'),nl.

/*
assignments([action(ident(V):=num(Val))],VarTable,[J],[Val]) :-
	write('assignments called'),nl,
	member(var(V,'$VAR'(J),_),VarTable),
	write('member call succeeded'),nl.
*/


assignments([action(ident(V):=num(Val))|Actions],VarTable,[J|AssignedVarsIndexs],[Val|AssignedVals]) :-
	write('assignments called'),nl,
	member(var(V,'$VAR'(J),_),VarTable),
	write('member call succeeded'),nl,
	write('Actions evaluates to:'),nl,
	write(Actions),nl,
	assignments(Actions,VarTable,AssignedVarsIndexs,AssignedVals).

listRaider12([],[],InList,InList).

listRaider12([ActionVar|ActionVars],[AssignedVal|AssignedVals],InList,OutList) :-
	replaceListElements12(ActionVar,AssignedVal,0,InList,NewStateArgVals),
	listRaider12(ActionVars,AssignedVals,NewStateArgVals,OutList).

%% replaceListElements1 accepts element's index. elementlist, and replacing element and gives out the resultant list of this replacement

replaceListElements12(_,_,_,[],[]).
replaceListElements12(RepIndex,AssignedVal,Index,[_|StateArgs],[AssignedVal|NewStateArgVals]) :-
	RepIndex == Index,
	X is Index+1,
	replaceListElements12(RepIndex,AssignedVal,X,StateArgs,NewStateArgVals).

replaceListElements12(RepIndex,AssignedVal,Index,[E|StateArgs],[E|NewStateArgVals]) :-
	RepIndex \== Index,
	X is Index+1,
	replaceListElements12(RepIndex,AssignedVal,X,StateArgs,NewStateArgVals).



%% locdecl(loc_0,[derivative(rate(ident(t),num(+1)))],and(invariant(ident(t)+num(1)<num(-(10))),invariant(ident(t)>num(+8))))]
%% varTable = [var(actualVarID, allocatedID, type),...,var(time,allocatedTimeID,rational)].

%% invariant(loc_0,[loc_0,_,_,_]) :-   true.

/****** changed Jan-9-2008 17:45 ***begin***
invariantPart([],_,S0,S0).
invariantPart([LocDecl|LocDecls],VarTable,[(H :- B)|S0],S1) :-
	invariantHead(LocDecl,VarTable,H),
	invariantBody(LocDecl,VarTable,B),
	invariantPart(LocDecls,VarTable,S0,S1).
******* changed Jan-9-2007 17:45 ***ends***/

/****replacement *** done on Jan-9-2008 17:45*** for generating NEGATIVE invariants BEGINS**********/

invariantPart([],_,S0,S0).
invariantPart([LocDecl|LocDecls],VarTable,[(logen(P/N,H) :- LogenizedB),(logen(NegP/NegN,NegH) :- LogenizedNegB)|S0],S1) :-
	invariantHead(LocDecl,VarTable,H),
	negInvariantHead(LocDecl,VarTable,NegH),
	invariantBody(LocDecl,VarTable,B),
	negInvariantBody(LocDecl,VarTable,NegB),
	invariantPart(LocDecls,VarTable,S0,S1),
	functor(H,P,N),
	functor(NegH,NegP,NegN),
	logenize(B,LogenizedB),
	logenize(NegB,LogenizedNegB).

negInvariantHead(locdecl(Loc,_,Invariants),VarTable,NegH) :-
	translateExpr2Vars(Invariants,VarTable,SignificantVarsIncludingTrues),
	atomTuple21List(SignificantVarsIncludingTrues,SignificantVarsTrues1),
	removeTrues(SignificantVarsTrues1,SignificantVars1),
	removeDuplicates(SignificantVars1,SignificantVars2),
	%% removeNumbers(SignificantVars1,SignificantVars2),
	generateUList(VarTable,UList),
	generateInvarHeadStateArg(SignificantVars2,UList,InvarHeadStateArg),
	NegH = (negInvariant(Loc,[Loc|InvarHeadStateArg])).

negInvariantBody(locdecl(_,_,Invariants),VarTable,NegB) :-
	translateExprNeg(Invariants,NegB,VarTable).

translateExprNeg(ident(V),X,Vars) :-
	member(var(V,X,_),Vars).

translateExprNeg(num(N),N,_).

translateExprNeg(E1+E2,F1+F2,Vars) :-
	translateExprNeg(E1,F1,Vars),
	translateExprNeg(E2,F2,Vars).
translateExprNeg(E1-E2,F1-F2,Vars) :-
	translateExprNeg(E1,F1,Vars),
	translateExprNeg(E2,F2,Vars).
translateExprNeg(E1*E2,F1*F2,Vars) :-
	translateExprNeg(E1,F1,Vars),
	translateExprNeg(E2,F2,Vars).
translateExprNeg(E1/E2,F1/F2,Vars) :-
	translateExprNeg(E1,F1,Vars),
	translateExprNeg(E2,F2,Vars).
translateExprNeg(E1 mod E2,F1 mod F2,Vars) :-
	translateExprNeg(E1,F1,Vars),
	translateExprNeg(E2,F2,Vars).
translateExprNeg(E1 := E2,F1 := F2,Vars) :-
	translateExprNeg(E1,F1,Vars),
	translateExprNeg(E2,F2,Vars).
translateExprNeg(E1 == E2,(IE1;IE2),Vars) :-
	translateExprNeg(E1,F1,Vars),
	translateExprNeg(E2,F2,Vars),
	IE1 =.. [<,F1,F2],
	IE2 =.. [>,F1,F2].
translateExprNeg(E1 = E2,(IE1;IE2),Vars) :-
	translateExprNeg(E1,F1,Vars),
	translateExprNeg(E2,F2,Vars),
	IE1 =.. [<,F1,F2],
	IE2 =.. [>,F1,F2].
translateExprNeg(E1 > E2,F1 =< F2,Vars) :-
	translateExprNeg(E1,F1,Vars),
	translateExprNeg(E2,F2,Vars).
translateExprNeg(E1 >= E2,F1 < F2,Vars) :-
	translateExprNeg(E1,F1,Vars),
	translateExprNeg(E2,F2,Vars).
translateExprNeg(E1 < E2,F1 >= F2,Vars) :-
	translateExprNeg(E1,F1,Vars),
	translateExprNeg(E2,F2,Vars).
translateExprNeg(E1 =< E2,F1 > F2,Vars) :-
	translateExprNeg(E1,F1,Vars),
	translateExprNeg(E2,F2,Vars).
translateExprNeg(or(E1,E2),(F1,F2),Vars) :-
	translateExprNeg(E1,F1,Vars),
	translateExprNeg(E2,F2,Vars).
translateExprNeg(and(E1,E2),(F1;F2),Vars) :-
	translateExprNeg(E1,F1,Vars),
	translateExprNeg(E2,F2,Vars).

translateExprNeg(invariant(E),F,VarTable) :-
	translateExprNeg(E,F,VarTable).



/*****changed Jan-9-2007 17:45*** for generating NEGATIVE invariants ***ENDS*********/



invariantHead(locdecl(Loc,_,Invariants),VarTable,H) :-
	translateExpr2Vars(Invariants,VarTable,SignificantVarsIncludingTrues),
	atomTuple21List(SignificantVarsIncludingTrues,SignificantVarsTrues1),
	removeTrues(SignificantVarsTrues1,SignificantVars1),
	removeDuplicates(SignificantVars1,SignificantVars2),
	%% removeNumbers(SignificantVars1,SignificantVars2),
	generateUList(VarTable,UList),
	generateInvarHeadStateArg(SignificantVars2,UList,InvarHeadStateArg),
	H = (invariant(Loc,[Loc|InvarHeadStateArg])).

removeTrues(SignificantVarsTrues1,SignificantVars) :-
	ripOffElementE(true,SignificantVarsTrues1,SignificantVars).

generateUList(VarTable,UList) :-
	stateArg(VarTable,StateArg),
	E = '$VAR'('_'),
	generateEList(E,StateArg,UList).

generateEList(E,StateArg,UList):-
	length(StateArg,N),
	generateList(E,N,UList).

generateList(_,0,[]).
generateList(Element,Length,[Element|GList]):-
	X is Length-1,
	X >= 0,
	generateList(Element,X,GList).



generateInvarHeadStateArg(SignificantVars2,UList,StateArg1) :-
	dollarVar2Indices(SignificantVars2,RepVarList),
	arrayRaider(RepVarList,UList,StateArg1).

dollarVar2Indices([],[]).
dollarVar2Indices(['$VAR'(J)|AllocVarIds],[J|RepvarList]) :-
	dollarVar2Indices(AllocVarIds,RepvarList).



%%[locdecl(loc_0,[derivative(rate(ident(x))=num(+1)),derivative(rate(ident(y))=num(+1))],
%%			invariant(num(1)==num(+1))),
%%	locdecl(loc_1,[derivative(rate(ident(x))=num(+1)),derivative(rate(ident(y))=num(+1))]

%% invariant(loc_0,[loc_0,X,_]) :- X < 10.

invariantBody(locdecl(_,_,Invariants),VarTable,B):-
	translateExpr(Invariants,B,VarTable).
	

	

ratePart([],_,S0,S0).
ratePart([LocDecl|Locs],VarTable,[(logen(P/N,H) :- LogenizedB)|S0],S1):-
	generateRatePartHead(LocDecl,VarTable,H),
	functor(H,P,N),
	generateRatePartBody(LocDecl,VarTable,B),
	logenize(B,LogenizedB),
	ratePart(Locs,VarTable,S0,S1).


%% [locdecl(loc_0,[derivative(rate(ident(t),num(+1)))],and(invariant(ident(t)+num(1)<num(-(10))),invariant(ident(t)>num(+8))))]

%%[locdecl(loc_0,[derivative(rate(ident(x))=num(+1)),derivative(rate(ident(y))=num(+1))], invariant(num(1)==num(+1))),
%%	locdecl(loc_1,[derivative(rate(ident(x))=num(+1)),derivative(rate(ident(y))=num(+1))]


%% d([l0,A,B,T],[_,A1,B1,T1]) :-     A1 is A+1*(T1-T), B1 is B+1*(T1-T).



generateRatePartHead(locdecl(Loc,_,_),VarTable,d([Loc|StateArg],[U|StateArg1])) :-
	U = '$VAR'('_'),
	copyVars(VarTable,StateArg1),
	stateArg(VarTable,StateArg).
	
/*************

generateRatePartBody(locdecl(_,Derivatives,_),VarTable,C2) :-
	generateRateBody(Derivatives,VarTable,C2). 

***************/




/******* Linearized Rate Body Begins LBRBB****************/

generateRatePartBody(locdecl(_,Derivatives,_),VarTable,B) :-
	generateRateBodysLists(Derivatives,VarTable,OldVarsList,NewVarsList,LinearRelationList,DerivativeValList),
	stateArg(VarTable,StateArg),
	copyVars(VarTable,StateArg1),
	timeLapsed(StateArg1,StateArg,LapsedTime),
	generateRateBody(NewVarsList,LinearRelationList,OldVarsList,DerivativeValList,LapsedTime,VarTable,B).


generateRateBodysLists([],_,[],[],[],[]).
generateRateBodysLists([derivative(D)|Derivatives],VarTable,['$VAR'(J)|OldVars],['$VAR'(NewVarIndex)|NewVars],[LinRel|LinearRelations], [DerivRhsVal|DerivativeRhsVals]) :-
	D =.. [LinRel,rate(ident(Var)),num(DerivRhsVal)],
	member(var(Var,'$VAR'(J),_),VarTable),
	length(VarTable,N),
	NewVarIndex is J + N,
	generateRateBodysLists(Derivatives,VarTable,OldVars,NewVars,LinearRelations,DerivativeRhsVals).


/**** augmentation done on 22 Jan 2007 @ 4:08 PM ***BEGIN***/
generateRateBodysLists([derivative(D)|Derivatives],VarTable,['$VAR'(J)|OldVars],['$VAR'(NewVarIndex)|NewVars],[LinRel|LinearRelations], ['$VAR'(RhsValPar)|DerivativeRhsVals]) :-
	D =.. [LinRel,rate(ident(Var)),ident(ParameterAsDerivRhsVal)],
	member(var(Var,'$VAR'(J),_),VarTable),
	member(var(ParameterAsDerivRhsVal,'$VAR'(RhsValPar),_),VarTable),
	length(VarTable,N),
	NewVarIndex is J + N,
	generateRateBodysLists(Derivatives,VarTable,OldVars,NewVars,LinearRelations,DerivativeRhsVals).
/**** augmentation done on 22 Jan 2007 @ 4:08 PM ***END***/




/***** replacement begins 23 Nov 2007 **** 15:53 ******/


generateRateBody([Nv],[Lr],[Ov],[DrVal],LapsedTime,VarTable,B1) :-
	member(var(_,DrVal,_),VarTable),
%%	decimalNumber(DrVal,1,Numerator, Denominator),
	DeltaVarVal =.. [*,DrVal,LapsedTime],
	NewVarval =.. [+,Ov,DeltaVarVal],
	B1 =.. [Lr,Nv,NewVarval].

generateRateBody([Nv|NewVars],[Lr|LinearRelations],[Ov|OldVars],[DrVal|DerivativeVals],LapsedTime,VarTable,(B1,B2)) :-
	member(var(_,DrVal,_),VarTable),
%%	decimalNumber(DrVal,1,Numerator, Denominator),
	DeltaVarVal =.. [*,DrVal,LapsedTime],
	NewVarval =.. [+,Ov,DeltaVarVal],
	B1 =.. [Lr,Nv,NewVarval],
	generateRateBody(NewVars,LinearRelations,OldVars,DerivativeVals,LapsedTime,VarTable,B2).

generateRateBody([Nv],[Lr],[Ov],[DrVal],LapsedTime,VarTable,B1) :-
	\+ member(var(_,DrVal,_),VarTable),
	decimalNumber(DrVal,1,Numerator, Denominator),
	DeltaVarVal =.. [*,Numerator,LapsedTime],
	Ov1 =.. [*,Denominator,Ov],
	Nv1 =.. [*,Denominator,Nv],
	NewVarval =.. [+,Ov1,DeltaVarVal],
	B1 =.. [Lr,Nv1,NewVarval].

generateRateBody([Nv|NewVars],[Lr|LinearRelations],[Ov|OldVars],[DrVal|DerivativeVals],LapsedTime,VarTable,(B1,B2)) :-
	\+ member(var(_,DrVal,_),VarTable),
	decimalNumber(DrVal,1,Numerator, Denominator),
	DeltaVarVal =.. [*,Numerator,LapsedTime],
	Ov1 =.. [*,Denominator,Ov],
	Nv1 =.. [*,Denominator,Nv],
	NewVarval =.. [+,Ov1,DeltaVarVal],
	B1 =.. [Lr,Nv1,NewVarval],
	generateRateBody(NewVars,LinearRelations,OldVars,DerivativeVals,LapsedTime,VarTable,B2).

integerTest(X) :-
	0.0 is float_fractional_part(X).

decimalNumber(DrValP,DrValQ,X,DrValQ) :-
	integerTest(DrValP),
	X is truncate(DrValP).

decimalNumber(DrValP,DrValQ,Numerator,Denominator) :-
	X is DrValP,
	\+integerTest(X),
	DrValP1 is DrValP*10,
	DrValQ1 is DrValQ*10,
	decimalNumber(DrValP1,DrValQ1,Numerator,Denominator).

/***** replacement ends 23 Nov 2007 **** 15:53 ******/



/***** replaced begins 23 Nov 2007 **** 15:53 ******
%% generateRateBody([],[],[],[],_,true).
generateRateBody([Nv],[Lr],[Ov],[DrVal],LapsedTime,B1) :-
	DeltaVarVal =.. [*,DrVal,LapsedTime],
	NewVarval =.. [+,Ov,DeltaVarVal],
	B1 =.. [Lr,Nv,NewVarval].

generateRateBody([Nv|NewVars],[Lr|LinearRelations],[Ov|OldVars],[DrVal|DerivativeVals],LapsedTime,(B1,B2)) :-
	DeltaVarVal =.. [*,DrVal,LapsedTime],
	NewVarval =.. [+,Ov,DeltaVarVal],
	B1 =.. [Lr,Nv,NewVarval],
	generateRateBody(NewVars,LinearRelations,OldVars,DerivativeVals,LapsedTime,B2).
***** replaced ends 23 Nov 2007 **** 15:53 ******/

/******** Linearized Rate Body Ends LBRBE*****************/


/************ replaced body in lieu of  LBRBE **********
generateRatePartBody(locdecl(_,Derivatives,_),VarTable,(B1,B2)) :-
	generateRateBody1(Derivatives,VarTable,B1),
	copyVars(VarTable,StateArg1),
	stateArg(VarTable,StateArg),
	timeLapsed(StateArg1,StateArg,LapsedTime),
	length(StateArg1,N),
	generateRateBody2(StateArg1,StateArg,N,LapsedTime,B2).
************ replaced body in lieu of  LBRBE ends **********/

timeLapsed(StateArg1,StateArg,LapsedTime) :-
	timeVar(StateArg1,'$VAR'(T1)),
	timeVar(StateArg,'$VAR'(T)),
	LapsedTime =.. [-,'$VAR'(T1),'$VAR'(T)].


generateRateBody2([_],[_],_,_,true).
	
generateRateBody2(['$VAR'(J1)|StateArg1],['$VAR'(J)|StateArg],N,LapsedTime,(B21,B22)) :-
	RateVarJ is J + 3*N,
	Increment =.. [*,'$VAR'(RateVarJ),LapsedTime],
	X1 =.. [+,'$VAR'(J),Increment],
	B21 =.. [is,'$VAR'(J1),X1],
	generateRateBody2(StateArg1,StateArg,N,LapsedTime,B22).


generateRateBody1([],_,true).
generateRateBody1([Derivative],VarTable,B12) :-
	translateDerivativeExpr(Derivative,VarTable,B12).

generateRateBody1([Derivative|Derivatives],VarTable,(B11,B12)) :-
	translateDerivativeExpr(Derivative,VarTable,B11),
	generateRateBody1(Derivatives,VarTable,B12).
	

/*********** Replaced 8 Nov 2007, 5:26 PM *****
significantVars([],_,[]).
significantVars([derivative(rate(ident(Var),num(_)))|Derivatives],VarTable,[AllocId|SignificantVars]) :-
	member(var(Var,AllocId,_),VarTable),
	significantVars(Derivatives,VarTable,SignificantVars).
*********** Replaced 8 Nov 2007, 5:26 PM *****/


/******************** removed completely *** November 12 2007 5:07 PM****************************
%% Replaced by Nov 2007, 5:26 PM
significantVars([],_,[]).
significantVars([derivative(RateExpression)|Derivatives],VarTable,[AllocId|SignificantVars]) :-
	rateExpr2Var(RateExpression,AllocId),
	member(var(Var,AllocId,_),VarTable),
	significantVars(Derivatives,VarTable,SignificantVars).
%% Replaced Nov 2007, 5:26 PM
*********************removed completely *** November 12 2007 5:07 PM ***************************/


/************************************************************************
generateRateBody(Derivatives,VarTable,SignificantVars,B) :-
	generateRateBody1(Derivatives,VarTable,B),
	length(VarTable,NumbOfVars),
	length(SignificantVars,NumbOfSigniVars),
	NumbOfVars =:= (NumbOfSigniVars+1).

generateRateBody(Derivatives,VarTable,SignificantVars,(B1,B2)) :-
	generateRateBody1(Derivatives,VarTable,B1),
	length(VarTable,NumbOfVars),
	length(SignificantVars,NumbOfSigniVars),
	NumbOfVars > (NumbOfSigniVars+1),
	generateRateBody2(VarTable,SignificantVars,B2).

generateRateBody2(VarTable,SignificantVars,B2) :-
	stateArg(VarTable,StateArg),
	timeVar(StateArg,TimeVar),
	append(StateVarsOnly,[TimeVar],StateArg),
	nonSigniVars(StateVarsOnly,SignificantVars,NonSigniVars),
	length(VarTable,N),
	generateRateB2(NonSigniVars,N,B2).

******************************************************************************/
%% generateRateB2([],_,true).

/*****************************************************
generateRateB2(['$VAR'(J)],N,B2) :-
	NewVarIndex is (J+N),
	B2 = ('$VAR'(NewVarIndex) is '$VAR'(J)).
generateRateB2(['$VAR'(J)|NonSigniVars],N,(B,B2)) :-
	NewVarIndex is (J+N),
	B = ('$VAR'(NewVarIndex) is '$VAR'(J)),
	generateRateB2(NonSigniVars,N,B2).
*****************************************************/

nonSigniVars(AllStateVarsOnlyNoTimeVar,SignificantVars,NonSigniVars) :-
	listDiff(SignificantVars,AllStateVarsOnlyNoTimeVar,NonSigniVars).

listDiff([],X,X).
	
listDiff([D|Ds],Xs,Os) :-
	minus(D,Xs,LessD),
	listDiff(Ds,LessD,Os).

minus(_,[],[]).
minus(E,[E|List],List).
minus(E,[E1|List],[E1|Os]) :-
	E \== E1,
	minus(E,List,Os).


/**********************Nov 12 2007 5:00 PM********************************************
generateRateBody1([],_,true).

generateRateBody1([derivative(rate(ident(Var),num(VarVal)))],VarTable,B) :-
	!,
	length(VarTable,N),
	member(var(Var,'$VAR'(J),_),VarTable),
	timeVar(VarTable,var(_VarTime,'$VAR'(T),_)),
	J1 is J+N,
	T1 is T+N,
	B = ('$VAR'(J1) = '$VAR'(J) + VarVal*('$VAR'(T1) - '$VAR'(T)) ).

generateRateBody1([derivative(rate(ident(Var),num(VarVal)))|Derivatives],VarTable,(B1,B)) :-
	length(VarTable,N),
	member(var(Var,'$VAR'(J),_),VarTable),
	timeVar(VarTable,var(_VarTime,'$VAR'(T),_)),
	J1 is J+N,
	T1 is T+N,
	B1 = ('$VAR'(J1) = '$VAR'(J) + VarVal*('$VAR'(T1) - '$VAR'(T)) ),
	generateRateBody1(Derivatives,VarTable,B).
***********************Nov 12 2007 5:00 PM********************************************/


/***********************10*
generateRateBody([],_,true).

generateRateBody([derivative(rate(ident(Var),num(VarVal)))],VarTable,B) :-
	!,
	length(VarTable,N),
	member(var(Var,'$VAR'(J),_),VarTable),
	timeVar(VarTable,var(_VarTime,'$VAR'(T),_)),
	J1 is J+N,
	T1 is T+N,
	B = ('$VAR'(J1) = '$VAR'(J) + VarVal*('$VAR'(T1) - '$VAR'(T)) ).

generateRateBody([derivative(rate(ident(Var),num(VarVal)))|Derivatives],VarTable,(B1,B)) :-
	length(VarTable,N),
	member(var(Var,'$VAR'(J),_),VarTable),
	timeVar(VarTable,var(_VarTime,'$VAR'(T),_)),
	J1 is J+N,
	T1 is T+N,
	B1 = ('$VAR'(J1) = '$VAR'(J) + VarVal*('$VAR'(T1) - '$VAR'(T)) ),
	generateRateBody(Derivatives,VarTable,B).
**************************10*/

% X = lha([vardecl(numeric,t),vardecl(bool,b)],[locdecl(loc_0,[derivative(rate(ident(t),num(+1)))],and(invariant(ident(t)+num(1)<num(-(10))),invariant(ident(t)>num(+8))))],[init(loc_0,[action(ident(t):=num(+0))]),transition(locpair(loc_0,loc_0),[ident(t)==num(+10)],[action(ident(t):=num(+0))])]) ?


% % transition((loc_1,loc_0),(y==9),(x:=0.1)).
% variables
% gamma(loc_1,[loc_0,_,B,_]) :-     B = 2.

gammaPart([],_,_,S0,S0).
gammaPart([Transition|Transitions],K,VarTable,[( logen(P/N,H) :- LogenizedB)|S0],S1) :-
	generateGammaPartHead(Transition,K,VarTable,H),
	functor(H,P,N),
	generateGammaPartBody(Transition,VarTable,B),
	logenize(B,LogenizedB),
	K1 is K+1,
	gammaPart(Transitions,K1,VarTable,S0,S1).

generateGammaPartHead(transition(locpair(Loc1,Loc2),GuardsList,_),K,VarTable,H) :-
	H = (gamma(K,Loc1,[Loc2|StateArg1])),
	% stateArg(VarTable,StateArg),
	ripOffTrues(GuardsList,GuardsList1),
	signiVars(GuardsList1,VarTable,SigniVarTuple),
	write('SigniVarTuple Created its value is'),nl,
	write(SigniVarTuple),nl,
	flatten(SigniVarTuple,SigniVars),
	write('SigniVarTuple Flattened'),nl,
	atomTuple21List(SigniVars,SigniVarsList),
	removeDuplicates(SigniVarsList,SigniVarsList1),
	ripOffTrues(SigniVarsList1,SigniVarsListWithNoTrues),
	var2IndexConverter(SigniVarsListWithNoTrues,SigniVarsJList),
	uListGenerator(VarTable,UListStateArg),
	stateArg1(SigniVarsJList,UListStateArg,StateArg1).


ripOffTrues([],[]).
ripOffTrues([true|Guards],X) :-
	ripOffTrues(Guards,X).

ripOffTrues([NotTrue|Guards],[NotTrue|X]) :-
	NotTrue \= true,
	ripOffTrues(Guards,X).



var2IndexConverter([],[]).
var2IndexConverter(['$VAR'(J)],[J]).
var2IndexConverter(['$VAR'(J)|SigniVars],[J|SigniVarIndexes]) :-
	var2IndexConverter(SigniVars,SigniVarIndexes).






%% signiVars catches the indices of those variables with which a guard exists 	

/*SIGNIFI

signiVars([],_,[]).
signiVars([ident(Var)==num(_)|Guards],VarTable,[J|VarJList]) :-
	member(var(Var,'$VAR'(J),_),VarTable),
	signiVars(Guards,VarTable,VarJList).

**SIGNIFI*/

signiVars([],_,true).

signiVars([Guard],VarTable,Vs) :-
	translateExpr2Vars(Guard,VarTable,Vs).

signiVars([Guard|Guards],VarTable,(Vs1,Vs2)) :-
	translateExpr2Vars(Guard,VarTable,Vs1),
	signiVars(Guards,VarTable,Vs2).




%%  uListGenerator generates a list of underscores of VarTable length 

uListGenerator(VarTable,UListStateArg) :-
	length(VarTable,N),
	U = '$VAR'('_'),
	generateList(U,N,UListStateArg).

stateArg1(RepVarList,UList,StateArg1):-
	arrayRaider(RepVarList,UList,StateArg1).

arrayRaider([],InList,InList).
arrayRaider([I|Is],InList,OutList) :-
	replaceElements(I,InList,0,RepList),
	arrayRaider(Is,RepList,OutList).

replaceElements(_,[],_,[]).
replaceElements(RepIndex,[_|Is],Index,['$VAR'(Index)|RepList]) :-
	RepIndex == Index,
	X is Index+1,
	replaceElements(RepIndex,Is,X,RepList).

replaceElements(RepIndex,[I|Is],Index,[I|RepList]) :-
	RepIndex \== Index,
	X is Index+1,
	replaceElements(RepIndex,Is,X,RepList).


generateGammaPartBody(transition(_,Guards,_),VarTable,B) :-
	generateGammaBody(Guards,VarTable,B).

/* generateGammaBody([],VarTable,B) :-
generateGammaBody(Guards,VarTable,B) :-
	translateExpr(Guards,B,VarTable). */


generateGammaBody([],_,true).

generateGammaBody([Guard],VarTable,TranslatedGuard) :-
	translateExpr(Guard,TranslatedGuard,VarTable).

generateGammaBody([Guard|Guards],VarTable,(TranslatedGuard,TranslatedGuardsRest)) :-
	translateExpr(Guard,TranslatedGuard,VarTable),
	generateGammaBody(Guards,VarTable,TranslatedGuardsRest).




	
% X = lha([vardecl(numeric,t),vardecl(bool,b)],[locdecl(loc_0,[derivative(rate(ident(t),num(+1)))],and(invariant(ident(t)+num(1)<num(-(10))),invariant(ident(t)>num(+8))))],[init(loc_0,[action(ident(t):=num(+0))]),transition(locpair(loc_0,loc_0),[ident(t)==num(+10)],[action(ident(t):=num(+0))])]) ?

% alpha(loc_1,[l1,A1,B1,_],[l0,A2,B2,0]) :-     A2 is 0, B2 is B1.


alphaPart([],_,_,S0,S0).
alphaPart([Transition|Transitions],K,VarTable,[(logen(P/N,H) :- LogenizedB)|S0],S1):-
	generateAlphaHead(Transition,K,VarTable,H),
	functor(H,P,N),
	generateAlphaBody(Transition,VarTable,B),
	logenize(B,LogenizedB),
	K1 is K+1,
	alphaPart(Transitions,K1,VarTable,S0,S1).

generateAlphaHead(transition(locpair(Loc1,Loc2),_,_),K,VarTable,H) :-
	stateArg(VarTable,StateArg),
	reAssignedTimeVar('_',StateArg,StateArgLoc1),
	copyVars2(VarTable,StateArg2),
	reAssignedTimeVar('0',StateArg2,StateArgLoc2),
	H = (alpha(K,Loc1,[Loc2|StateArgLoc1],[Loc2|StateArgLoc2])).

reAssignedTimeVar(NewTimeVar,StateArg,StateArgWithNewTimeVar) :-
	timeVar(StateArg,T),
	append(NonTimeVars,[T],StateArg),
	append(NonTimeVars,['$VAR'(NewTimeVar)],StateArgWithNewTimeVar).

generateAlphaBody(transition(_,_,AlphaList),VarTable,B) :-
	generateActionParticulars(AlphaList,VarTable,ActionVarList,AssignedValList),
	generateRhsOfActions(VarTable,ActionVarList,AssignedValList,NewStateArgVals),
	generateAlphaB(VarTable,NewStateArgVals,B).


generateActionParticulars([],_,[],[]).
generateActionParticulars([action(ident(Var):=ActionRhsExpr)|Alphas],VarTable,[J|ActionVars],[AssignedExprVal|AssignedExprVals]) :-
	translateExpr(ActionRhsExpr,AssignedExprVal,VarTable),
	member(var(Var,'$VAR'(J),_),VarTable),
	generateActionParticulars(Alphas,VarTable,ActionVars,AssignedExprVals).
	
generateRhsOfActions(VarTable,ActionVarList,AssignedValList,NewStateArgVals) :-
	stateArg(VarTable,StateArg),
	updatedStateArg(StateArg,ActionVarList,AssignedValList,NewStateArgVals).

updatedStateArg(StateArg,ActionVarList,AssignedValList,NewStateArgVals) :-
	listRaider(ActionVarList,AssignedValList,StateArg,NewStateArgVals).

listRaider([],[],StateArg,StateArg).
listRaider([ActionVar|ActionVarList],[AssignedVal|AssignedValList],StateArg,NewStateArgVals) :-
	replaceListElements(ActionVar,AssignedVal,0,StateArg,NewStateArgVals1),
	listRaider(ActionVarList,AssignedValList,NewStateArgVals1,NewStateArgVals).


replaceListElements(_,_,_,[],[]).
replaceListElements(RepIndex,AssignedVal,Index,[_|StateArgs],[AssignedVal|NewStateArgVals]) :-
	RepIndex == Index,
	X is Index+1,
	replaceListElements(RepIndex,AssignedVal,X,StateArgs,NewStateArgVals).

replaceListElements(RepIndex,AssignedVal,Index,[S|StateArgs],[S|NewStateArgVals]) :-
	RepIndex \== Index,
	X is Index+1,
	replaceListElements(RepIndex,AssignedVal,X,StateArgs,NewStateArgVals).


/***************************
listRaider12([],[],InList,InList).

listRaider12([ActionVar|ActionVars],[AssignedVal|AssignedVals],InList,OutList) :-
	replaceListElements12(ActionVar,AssignedVal,0,InList,NewStateArgVals),
	listRaider12(ActionVars,AssignedVals,NewStateArgVals,OutList).

%% replaceListElements1 accepts element's index. elementlist, and replacing element and gives out the resultant list of this replacement

replaceListElements12(_,_,_,[],[]).
replaceListElements12(RepIndex,AssignedVal,Index,[_|StateArgs],[AssignedVal|NewStateArgVals]) :-
	RepIndex == Index,
	X is Index+1,
	replaceListElements12(RepIndex,AssignedVal,X,StateArgs,NewStateArgVals).

replaceListElements12(RepIndex,AssignedVal,Index,[_|StateArgs],['$VAR'('_')|NewStateArgVals]) :-
	RepIndex \== Index,
	X is Index+1,
	replaceListElements12(RepIndex,AssignedVal,X,StateArgs,NewStateArgVals).


****************************/


/*1* 

generateAlphaB(VarTable,NewStateArgVals,B) :-
	copyVars2(VarTable,NewStateArgs),
	buildAlphas(NewStateArgs,NewStateArgVals,B). 

*1*/

generateAlphaB(VarTable,NewStateArgVals,B) :-
	copyVars2(VarTable,NewStateArgs),
	timeVar(NewStateArgs,TimeVar),
	append(AllStateVarsOnlyNoTimeVar,[TimeVar],NewStateArgs),
	timeVar(NewStateArgVals,TimeVal),
	append(AllStateArgValsOnlyNoTimeVarVal,[TimeVal],NewStateArgVals),
	buildAlphas(AllStateVarsOnlyNoTimeVar,AllStateArgValsOnlyNoTimeVarVal,B).



buildAlphas([],[],true).

buildAlphas([NewStateArg],[NewStateArgVal],C1) :-
	C1 = (NewStateArg = NewStateArgVal).

buildAlphas([NewStateArg|NewStateArgs],[NewStateArgVal|NewStateArgVals],(C1,S0)) :-
	C1 = (NewStateArg = NewStateArgVal),
	buildAlphas(NewStateArgs,NewStateArgVals,S0).


removeDuplicates([],[]).

removeDuplicates([E|InList],[E|OutList]) :-
	ripOffElementE(E,InList,SeList),
	removeDuplicates(SeList,OutList).


atomTuple21List((X,Y),[X|Tail]) :-
	!,
	atomTuple21List(Y,Tail).

atomTuple21List(X,[X]).


/* removeDups(_,[],[]).
removeDups(E,[E|T],X) :-
	removeDups(E,T,X).

removeDups(E,[H|T],[H|X]) :-
	E \= H,
	removeDups(E,T,X). */

ripOffElementE(_,[],[]).
ripOffElementE(E,[E|T],X) :-
	ripOffElementE(E,T,X).

ripOffElementE(E,[H|T],[H|X]) :-
	H \= E,
	ripOffElementE(E,T,X).


probePart(VarTable,IndexForDollarVar,[(logen(PName/NumOfArgs,H) :- logen(memo,B))|S1],S0) :-
	length(VarTable,N),
	IndexForDollarVar < N-1,
	H = (probe('$VAR'('Loc'),'$VAR'(IndexForDollarVar))),
	functor(H,PName,NumOfArgs),
	B = (rState(['$VAR'('Loc')|StateArgs])),
	generateUList1(VarTable,UList),
	replaceElementAtIndex(IndexForDollarVar,UList,StateArgs),
	X is IndexForDollarVar+1,
	probePart(VarTable,X,S1,S0).

probePart(VarTable,IndexForDollarVar,[true|S1],S0) :-
	length(VarTable,N),
	IndexForDollarVar =:= N-1,
	X is IndexForDollarVar+1,
	probePart(VarTable,X,S1,S0).


probePart(VarTable,IndexForDollarVar,[],[]) :-	
	length(VarTable,N),
	IndexForDollarVar =:= N.

replaceElementAtIndex(IndexForDollarVar,UList,StateArgs) :-
	replaceListElements12(IndexForDollarVar,'$VAR'(IndexForDollarVar),0,UList,StateArgs).

generateUList1(VarTable,UList) :-
	length(VarTable,N),
	generateList('$VAR'('_'),N,UList).

logenize((B,Bs),(logen(rescall,B),LogenizedBs)) :-
	!,
	logenize(Bs,LogenizedBs).
logenize(true,true) :-
	!.
logenize(B,logen(rescall,B)).
