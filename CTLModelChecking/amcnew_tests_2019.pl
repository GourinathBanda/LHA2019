:- module(amcnew_tests_2019,_).


:- use_module(amc_all).


testBakery :-
	F1 = 'Tests/bakery.spec',
	V1 = 'Tests/bakery.versions',
	T1 = 'Tests/bakery.predExistsTable',
	numbervars((X0,X1,_,_,_,_),0,_),
	Phi = neg(ag(implies(prop(X0=2),af(prop(X0=3))))),
	testId('Bakery-1',F1,V1,T1,Phi),
	Phi1 = neg(ag(implies(prop(X1=2),af(prop(X1=3))))),
	testId('Bakery-1.5',F1,V1,T1,Phi1),
	Phi2 = neg(ag(neg(and(prop(X0=3),prop(X1=3))))),
	testId('Bakery-2',F1,V1,T1,Phi2),
	
	F2 = 'Tests/Delzanno/bakery4_ME.transitions.loc.spec',
	V2 = 'Tests/Delzanno/bakery4_ME.transitions.versions.disjoint',
	T2 = 'Tests/Delzanno/bakery4_ME.transitions.loc.predExistsTable',
	numbervars((P1,_,_,_,_,_,_),0,_),
	%Psi = neg(ag(implies(prop(P1=2),af(prop(P1=3))))),
	%testId('Bakery-4.1',F2,V2,T2,Psi),
	%Psi1 = neg(ag(implies(prop(P1=2),af(prop(P1=3))))),
	%testId('Bakery-4.2',F2,V2,T2,Psi1),
	Psi2 = neg(ag(neg(and(prop(P1=3),prop(P1=3))))),
	testId('Bakery-4.3',F2,V2,T2,Psi2).
	
testExs2019 :-
	F1 = 'Tests2019/lhaWaterLevelMonitorWithNoEventsNew.spec',
	V1 = 'Tests2019/versions.out',
	T1 = 'Tests2019/lhaWaterLevelMonitorWithNoEventsNew.predExistsTable',
	numbervars((_X1,X2,_X3,_X4,_X5),0,_),
	PhiT1 = neg(ef(prop(X2=10))), testId('T1',F1,V1,T1, PhiT1),
	PhiT2 = neg(ag(and(prop(X2>=1),prop(X2 =< 12)))), testId('T2',F1,V1,T1, PhiT2).

testExs2019_AllFail :-
	F1 = 'Tests2019/lhaWaterLevelMonitorWithNoEventsNew.spec',
	V1 = 'Tests2019/versions.out',
	T1 = 'Tests2019/lhaWaterLevelMonitorWithNoEventsNew.predExistsTable',
	numbervars((_X1,X2,_X3,_X4,_X5),0,_),
	PhiT1 = neg(eg(prop(X2=10))), testId('T1',F1,V1,T1, PhiT1),
	PhiT23 = neg(ag(prop(X2<1))), testId('T2',F1,V1,T1, PhiT23).


	
testOverlap :-
	F1 = 'Tests/lhaWaterLevelMonitorWithNoEventsNew.spec',
	V1 = 'Tests/lhaWaterLevelMonitorWithNoEventsNew.versions',
	T1 = 'Tests/lhaWaterLevelMonitorWithNoEventsNew.predExistsTable',


	numbervars((_X1,X2,_X3,_X4,_X5),0,_),
	PhiT1 = prop(1>=1), testId('T1',F1,V1,T1, PhiT1),
	PhiT2 = neg(ag(and(prop(X2>=1),prop(X2 =< 12)))), testId('T2',F1,V1,T1, PhiT2).
	
	
	

