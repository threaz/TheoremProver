/* Funktory do budowania klauzul */

:- op(200, fx, ~).
:- op(500, xfy, v).

main(FileName) :-
    readClauses(FileName, Clauses),
    prove(Clauses, Proof),
    writeProof(Proof).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
prove(Clauses, Proof) :-
    makeAxiomList(Clauses, AxiomList),
    proveRec(AxiomList, ProofTmp),
    listToClauses(ProofTmp, Proof).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Rozdziela literały pozytywne od negatywnych. Tworzy dwie osobne ich listy.

separate([], PosUS, Pos, NegUS, Neg) :- sort(PosUS, Pos),
					sort(NegUS, Neg).
separate((~P v R), AccP, Pos, AccN, Neg) :-
    separate(R, AccP, Pos, [P|AccN], Neg), !.
separate((P v R), AccP, Pos, AccN, Neg) :-
    separate(R, [P|AccP], Pos, AccN, Neg), !.
separate(~P, AccP, Pos, AccN, Neg) :- separate([], AccP, Pos, [P|AccN], Neg), !.
separate(P, AccP, Pos, AccN, Neg)  :- separate([], [P|AccP], Pos, AccN, Neg), !.

separate(Clause, Pos, Neg) :- separate(Clause, [], Pos, [], Neg).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Tworzy listę struktur [[Pozytywne], [Negatywne], [Wyprowadzenie], Numer],
% dokładniej, listę aksjomatów od której zaczniemy przeprowadzać dowód.

makeAxiomList([], AxiomListUR, AxiomList, _) :- reverse(AxiomListUR, AxiomList),
						!.
makeAxiomList([H|T], Acc, AxiomList, N) :-
    separate(H, HPosL, HNegL),
    list_to_set(HPosL, HPos),
    list_to_set(HNegL, HNeg),
    N1 is N+1,
    makeAxiomList(T, [[HPos, HNeg, [axiom], N]|Acc], AxiomList, N1).

makeAxiomList(Clauses, AxiomList) :-
    makeAxiomList(Clauses, [], AxiomList, 1).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Na podstawie dwóch struktur reprezentujących klauzule próbuje wyprowadzić nową.
% Wyrzuca powtarzające się literały.

makeNewClause([Pos1, Neg1, _, N1], [Pos2, Neg2, _, N2], LastN, NewClause) :-
    intersection(Pos1, Neg2, Res1),
    intersection(Pos2, Neg1, Res2),
    union(Res1, Res2, U1),
    length(U1, 1),
    union(Pos1, Pos2, PosTmp),
    union(Neg1, Neg2, NegTmp),
    list_to_set(PosTmp, PosSet),
    list_to_set(NegTmp, NegSet),
    subtract(PosSet, U1, Pos),
    subtract(NegSet, U1, Neg),
    sort(Pos, PosSorted),
    sort(Neg, NegSorted),
    NextN is LastN+1,
    NewClause = [PosSorted, NegSorted, [N1, N2], NextN].
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Szuka sprzeczności używając jednej klauzuli

findContradiction([[X], [], _, N], [N, N1], [[[], [X], _, N1]|_]) :- !.
findContradiction([[],  [X], _, N], [N, N1], [[[X], [], _, N1]|_]) :- !.
findContradiction(X, Path, [_|T]) :- findContradiction(X, Path, T).

% Wykorzystując poprzedni predykat przeszukuje całą listę w poszukiwaniu
% sprzeczności. W przypadku jej znalezienia, zmienna N zunifikuje się z numerami
% klauzul, które tę sprzeczność powodują.

isContradictory([H|T], N) :- findContradiction(H, N, T), !.
isContradictory([_|T], N) :- isContradictory(T, N).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Moja implementacja predykatu member. Jest tutaj konieczna, ponieważ porównujemy
% ze sobą jedynie listy literałów pozytywnych oraz negatywnych, a nie całe struktury.

clauseAlreadyExists([Pos, Neg, _, _], [[Pos, Neg, _, _]|_]) :- !.
clauseAlreadyExists(Clause, [_|T]) :- clauseAlreadyExists(Clause, T).   
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Używając Clause szuka w liście ClausesList rezolwenty Clause i innej klauzuli.

findNewClause(Clause, [H|_], ClausesList, NClauses, NewClause) :-
    makeNewClause(Clause, H, NClauses, NewClause),
    not(clauseAlreadyExists(NewClause, ClausesList)).
findNewClause(Clause, [_|T], ClausesList, NClauses, NewClause) :-
    findNewClause(Clause, T, ClausesList, NClauses, NewClause).

% Używa poprzedniego predykatu do przeszukania każdej klauzuli z każdą.

findNewClauseInWholeList([H|_], ClausesList, NewClause) :-
    length(ClausesList, NElems),
    findNewClause(H, ClausesList, ClausesList, NElems, NewClause), !.
findNewClauseInWholeList([_|T], ClausesList, NewClause) :-
    findNewClauseInWholeList(T, ClausesList, NewClause).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Konwertuje listę literałów pozytywnych z powrotem do postaci używającej operatora v.

elementToClause([H], H) :- !.
elementToClause([H|T], Clause) :- elementToClause(T, Clause1),
				  Clause = H v Clause1.

% To samo, tylko dla literałów negatywnych.

elementToClauseNeg([H], ~H) :- !.
elementToClauseNeg([H|T], Clause) :- elementToClauseNeg(T, Clause1),
				     Clause = ~H v Clause1.

% Łączy ze sobą dwie klauzule: pozytywne i negatywne.
mergeTwoClauses(Clause1, Clause2, Clause1 v Clause2).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Zamienia pochodzenie klauzuli, z listy na postać "bez listy".

convertOrigin([axiom], axiom).
convertOrigin([X, Y], (X, Y)).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Zamienie całą listę struktur, na której operujemy przez całe zadanie
% na listę klauzul wraz z ich pochodzeniem.

listToClauses([], ClausesR, Clauses) :- reverse(ClausesR, Clauses), !.
listToClauses([[[], [], Path, _]], Acc, Clauses) :-
    convertOrigin(Path, PathC),
    listToClauses([], [([], PathC)|Acc], Clauses), !.
listToClauses([[Pos, [], Path, _]|T], Acc, Clauses) :-
    elementToClause(Pos, PosC),
    convertOrigin(Path, PathC),
    listToClauses(T, [(PosC, PathC)|Acc], Clauses), !.
listToClauses([[[], Neg, Path, _]|T], Acc, Clauses) :-
    elementToClauseNeg(Neg, NegC),
    convertOrigin(Path, PathC),
    listToClauses(T, [(NegC, PathC)|Acc], Clauses), !.
listToClauses([[Pos, Neg, Path, _]|T], Acc, Clauses) :-
    elementToClause(Pos, PosC),
    elementToClauseNeg(Neg, NegC),
    mergeTwoClauses(PosC, NegC, Clause),
    convertOrigin(Path, PathC),
    listToClauses(T, [(Clause, PathC)|Acc], Clauses), !.

listToClauses(List, Clauses) :- listToClauses(List, [], Clauses).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Serce programu w wersji rekurencyjnej. Wywołuje go oredykat prove/2.
% Sprawdzamy najpierw, czy dostarczony zbiór klauzul (już w postaci struktur [_,_,_,_])
% jest sprzeczny. Jeżeli jest sprzeczny, dokładamy na koniec listy klauzulę pustą
% wraz ze sposobem jej wyprowadzenia. W p.p. dokładamy nową klauzulę, ale wywołujemy
% się też rekurencyjnie.

proveRec(ClausesList, Proof) :-
    (isContradictory(ClausesList, Path)
     -> append(ClausesList, [[[], [], Path, 0]], Proof), !
     ;  findNewClauseInWholeList(ClausesList, ClausesList, NewClause),
	append(ClausesList, [NewClause], NewClausesList),
	proveRec(NewClausesList, Proof)).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

readClauses(FileName, Clauses) :-
   open(FileName, read, Fd),
   read(Fd, Clauses),
   close(Fd).

writeProof(Proof) :-
   maplist(clause_width, Proof, Sizes),
   max_list(Sizes, ClauseWidth),
   length(Proof, MaxNum),
   write_length(MaxNum, NumWidth, []),
   nl,
   writeClauses(Proof, 1, NumWidth, ClauseWidth),
   nl.

clause_width((Clause, _), Size) :-
   write_length(Clause, Size, []).

writeClauses([], _, _, _).
writeClauses([(Clause,Origin) | Clauses], Num, NumWidth, ClauseWidth) :-
   format('~t~d~*|.  ~|~w~t~*+  (~w)~n',
          [Num, NumWidth, Clause, ClauseWidth, Origin]),
   Num1 is Num + 1,
   writeClauses(Clauses, Num1, NumWidth, ClauseWidth).


