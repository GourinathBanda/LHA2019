:- module(appendListOfDisjs,_).

appendListsOfDisjoints((D;Ds),Es,(D;Fs)) :-
	!,
	appendListsOfDisjoints(Ds,Es,Fs).
appendListsOfDisjoints(D,Ds,(D;Ds)).

%%appendListsOfDisjoints(ListOfDisjs1,ListOfDisjs2, AppendedDisjLists12) :-
%%	reverseDisjsList(ListOfDisjs1,emptyDisjsList,ReversedDisjList1),
%%	appDisjLists(ReversedDisjList1,ListOfDisjs2,eDisjList,AppendedDisjLists12).
%
%reverseDisjsList(Disj,TempReversalDisjList,ReversedDisjList) :-
%	Disj \= (_;_),
%	TempReversalDisjList = emptyDisjsList,!,
%	ReversedDisjList = Disj.
%
%reverseDisjsList(Disj,TempReversalDisjList,ReversedDisjList) :-
%        Disj \= (_;_),
%        TempReversalDisjList \= emptyDisjsList,!,
%	ReversedDisjList = (Disj;TempReversalDisjList).
%
%reverseDisjsList((Disj;Disjs),TempReversalDisjList,ReversedDisjList) :-
%	TempReversalDisjList = emptyDisjsList,!,
%	NewTempDisjList= Disj,
%	reverseDisjsList(Disjs,NewTempDisjList,ReversedDisjList).
%
%reverseDisjsList((Disj;Disjs),TempReversalDisjList,ReversedDisjList) :-
%	TempReversalDisjList \= emptyDisjsList,!,
%	NewTempDisjList= (Disj;TempReversalDisjList),
%	reverseDisjsList(Disjs,NewTempDisjList,ReversedDisjList).
%
%
%appDisjLists(Disj,_ListOfDisjs2,InTempAppList,AppendedDisjsList) :-
%        Disj \= (_;_),
%        InTempAppList \= eDisjList,!,
%        AppendedDisjsList = (Disj;InTempAppList).
%
%appDisjLists(Disj,ListOfDisjs2,InTempAppList,AppendedDisjsList) :-
%        Disj \= (_;_),
%        InTempAppList = eDisjList,!,
%        AppendedDisjsList = (Disj;ListOfDisjs2).
%
%appDisjLists((Disj;Disjs),ListOfDisjs2,InTempAppList,AppendedDisjsList) :-
%	InTempAppList \= eDisjList,!,
%	OutTempAppList = (Disj;InTempAppList),
%	appDisjLists(Disjs,ListOfDisjs2,OutTempAppList,AppendedDisjsList).
%
%appDisjLists((Disj;Disjs),ListOfDisjs2,InTempAppList,AppendedDisjsList) :-
%        InTempAppList = eDisjList,!,
%        OutTempAppList = (Disj;ListOfDisjs2),
%        appDisjLists(Disjs,ListOfDisjs2,OutTempAppList,AppendedDisjsList).
%
