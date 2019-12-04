/*Projeto Lógica*/

% Predicados auxiliares (conetivos)
:-op(100, fy, 'neg').
:-op(200, xfy, 'e').
:-op(300, xfy, 'ou').
:-op(400, xfy, 'imp').

acrescenta(X,[],[X]).
acrescenta(X,L,[X|L]).
concatena([],L,L).
concatena([X|R],L,[X|S]):- concatena(R,L,S).

/* membro/2 é tal que membro(X,L) tem o valor verdadeiro se X pertence à lista L*/
membro(X, [X | _]).
membro(X, [_ | C]):-membro(X, C).


/* comprimento/2 é tal que comprimento(L,N) é verdadeiro se N é o 
comprimento da lista L*/
comprimento([], 0).
comprimento([A|X], N):-comprimento(X, N1), N is N1+1.


eliminarep([],[]).
eliminarep([X|R],S):- membro(X,R), eliminarep(R,S).
eliminarep([X|R],[X|S]):- not(membro(X,R)), eliminarep(R,S).


/* enesimo/3 é tal que enesimo(N,L,X) é verdadeiro se N é um número
natural positivo e X é o elemento que está na posição N da lista L*/
enesimo(1,[X|L],X).
enesimo(N,[X|L],Y):-enesimo(N1,L,Y), N is N1+1.


/* calc_valor/4 é tal que ao executar uma consulta do tipo 
calc_valor(F,S,L,V) onde F é uma fórmula da Linguagem neg, e, ou e imp,
S é uma lista, sem repetições, dos símbolos proposicionais que ocorrem
em dita fórmula e L uma lista de 0s e 1s com o mesmo comprimento da lista
S, o interpretador Prolog devolverá V, o valor lógico de F por qualquer
valoração v que atribui a cada símbolo proposicional da lista S o valor 
lógico que ocorre na posição correspondente na lista L*/
calc_valor(F,L1,L2,V):- enesimo(N,L1,F), enesimo(N,L2,V).
calc_valor(neg X,L1,L2,0):- calc_valor(X,L1,L2,1).
calc_valor(neg X,L1,L2,1):- calc_valor(X,L1,L2,0).
calc_valor(X e Y, L1,L2,1) :- calc_valor(X,L1,L2,1),calc_valor(Y,L1,L2,1).
calc_valor(X e Y, L1,L2,0) :- not(calc_valor(X e Y,L1,L2,1)).
calc_valor(X ou Y, L1,L2,0) :- calc_valor(X,L1,L2,0),calc_valor(Y,L1,L2,0).
calc_valor(X ou Y, L1,L2,1) :- not(calc_valor(X ou Y,L1,L2,0)).
calc_valor(X imp Y,L1,L2,0):- calc_valor(X,L1,L2,1), calc_valor(Y,L1,L2,0).
calc_valor(X imp Y,L1,L2,1):- not(calc_valor(X imp Y,L1,L2,0)).


/* lista_n_0s_e_1s/2 é tal que lista_n_0s_e_1s(N,L) é verdadeiro se
L é uma lista constituída apenas por 0s e 1s de comprimento N, sendo
N um número inteiro não negativo*/
lista_n_0s_e_1s(0,[]).
lista_n_0s_e_1s(N,[0|L]):- N>0, N1 is N-1, lista_n_0s_e_1s(N1,L).
lista_n_0s_e_1s(N,[1|L]):- N>0, N1 is N-1, lista_n_0s_e_1s(N1,L).


todas_listas_0s_1s(N,R):- findall(L,lista_n_0s_e_1s(N,L),R), write(R).

/* simb_prop/2 é tal que sim_prop(Y,Y) é verdadeiro se Y é simbolo proposicional */
simb_prop(F,F):- not(F = neg X), not(F = X e Y), not(F = X ou Y), not(F = X imp Y).
simb_prop(neg F, Z) :- simb_prop(F,Z).
simb_prop(X e Y,U) :- simb_prop(X,U).
simb_prop(X e Y,I) :- simb_prop(Y,I).
simb_prop(X ou Y,U) :- simb_prop(X,U).
simb_prop(X ou Y,I) :- simb_prop(Y,I).
simb_prop(X imp Y,U) :- simb_prop(X,U).
simb_prop(X imp Y,I) :- simb_prop(Y,I).

/*simbolos_formula/2 é tal que simbolos_formula(F,L) sendo L a lista com todos 
os simbolos proposicionais da formula F*/
simbolos_formula(F,L) :- findall(U,simb_prop(F,U),T), eliminarep(T,L).

/*simbolos_conjunto/2 é tal que simbolos_conjunto(L1,L2) sendo L2 a 
lista de todos os simbolos proposicionais que ocorrem nalguma formula da lista de formulas L1*/
simbolos_conjunto([],[]).
simbolos_conjunto([F|R],L) :- simbolos_formula(F,T), simbolos_conjunto(R,U), concatena(T,U,Y), eliminarep(Y,L).

