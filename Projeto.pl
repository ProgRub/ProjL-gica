/*Projeto Lógica*/

/* 
Elementos do grupo:
Diego Andrés da Silva Briceño (2043818),
Filipe Orlando Namora Gomes (2045218),
José Alejandro Ferreira Gouveia (2028616),
Rúben José Gouveia Rodrigues (2046018)
*/


% Predicados auxiliares (conetivos)
:-op(100, fy, 'neg').
:-op(200, xfy, 'e').
:-op(300, xfy, 'ou').
:-op(400, xfy, 'imp').


/*acrescenta/3 é tal que acrescenta(X,L1,L2) tem o valor verdadeiro se L2 é a lista que
 resulta de colocar o elemento X na cabeça da lista L1*/
acrescenta(X,[],[X]).
acrescenta(X,L,[X|L]).

/*concatena/3 é tal que concatena(L1,L2,L3) é verdadeiro se L3 é a lista que resulta de
juntar as listas L1 e L2*/
concatena([],L,L).
concatena([X|R],L,[X|S]):- concatena(R,L,S).

/* membro/2 é tal que membro(X,L) tem o valor verdadeiro se X pertence à lista L*/
membro(X, [X | _]).
membro(X, [_ | C]):-membro(X, C).


/* comprimento/2 é tal que comprimento(L,N) é verdadeiro se N é o 
comprimento da lista L*/
comprimento([], 0).
comprimento([A|X], N):-comprimento(X, N1), N is N1+1.

/*eliminarep/2 é tal que eliminarep(X,Y) é verdadeiro se Y é a lista que resulta de retirar
da lista X todos exceto a ultima ocorrencia de cada um dos seus elementos*/
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


/*todas_listas_0s_1s/2 é tal que todas_listas_0s_1s(N,L) recebe um número inteiro 
não negativo N e devolve a lista L constituida por todas as listas de comprimento N
constituidas por Os e 1s.*/
todas_listas_0s_1s(N,R):- findall(L,lista_n_0s_e_1s(N,L),R).

/* simb_prop/2 é tal que sim_prop(Y,Y) é verdadeiro se Y é simbolo proposicional */
simb_prop(F,F):- not(F = neg X), not(F = X e Y), not(F = X ou Y), not(F = X imp Y).
simb_prop(neg F, Z) :- simb_prop(F,Z).
simb_prop(X e Y,U) :- simb_prop(X,U).
simb_prop(X e Y,I) :- simb_prop(Y,I).
simb_prop(X ou Y,U) :- simb_prop(X,U).
simb_prop(X ou Y,I) :- simb_prop(Y,I).
simb_prop(X imp Y,U) :- simb_prop(X,U).
simb_prop(X imp Y,I) :- simb_prop(Y,I).


/*simbolos_formula/2 é tal que simbolos_formula(F,L) é verdadeiro se L é a lista com todos 
os simbolos proposicionais da formula F*/
simbolos_formula(F,L) :- findall(U,simb_prop(F,U),T), eliminarep(T,L).

/*simbolos_conjunto/2 é tal que simbolos_conjunto(L1,L2) é verdadeiro se L2 é a 
lista de todos os simbolos proposicionais que ocorrem nalguma formula da lista de formulas L1*/
simbolos_conjunto([],[]).
simbolos_conjunto([F|R],L) :- simbolos_formula(F,T), simbolos_conjunto(R,U), concatena(T,U,Y), eliminarep(Y,L).

/*todas_valoracoes_satisfazem/2 é tal que todas_valoracoes_satisfazem(F,V) é verdadeiro se V é 
a lista de todas as valoracoes que satisfazem a formula F*/
todas_valoracoes_satisfazem(F,V):- simbolos_formula(F,L), comprimento(L,N), todas_listas_0s_1s(N,R), findall(A,valoracao_satisfaz(F,L,R,A),V).

/*valoracao_satisfaz/4 é tal que valoracao_satisfaz(F,S,L,V) é verdadeiro se V é uma valoracao de
L que satisfaz a formula F, sendo S a lista de simbolos proposicionais de F.*/
valoracao_satisfaz(F,S,[X|T],X):- calc_valor(F,S,X,1).
valoracao_satisfaz(F,S,[X|T],R):- valoracao_satisfaz(F,S,T,R).


/*juntar_conjunto/2 é tal que juntar_conjunto(L,V) é verdadeiro se V é a formula que se obtem
de concatenar todas as formulas da lista L com e´s */
juntar_conjunto([X|[]],X).
juntar_conjunto([H|R],P):- juntar_conjunto(R,T),P= H e T.

/* ************** Exercicio 1 ************** */
/*valoracoes_satisfazem_conjunto/3 é tal que valoracoes_satisfazem_conjunto(L,C,V) é verdadeiro se V é a lista de 
todas valoracoes que satisfazem a formula que resulta de concatenar todas as formulas de L com a formula C*/
valoracoes_satisfazem_conjunto(L,C,V) :- simbolos_conjunto(L,C), juntar_conjunto(L,F), todas_valoracoes_satisfazem(F,V).


/* -------------------------------------------------------*/

/*elimina/3 é tal que elimina(X,L1,L2) é verdadeiro se L2 é a lista que resulta de retirar 
da lista L1 todas as ocorrências do elemento X*/
elimina(X,[],[]).
elimina(X,[X|L],L1):- elimina(X,L,L1).
elimina(X,[Y|L],[Y|L1]):- not(Y=X), elimina(X,L,L1).

/*elimina_lista/3 é tal que elimina_lista(X,Y,L) é verdadeiro se L é a lista que resulta de retirar
da lista Y todas as ocorrências dos elementos da lista X*/
elimina_lista([],L,L).
elimina_lista([X|R],T,L):- elimina(X,T,P), elimina_lista(R,P,L).



/* ************** Exercicio 2 ************** */
/*conseq_semantica/2 é tal que conseq_semantica(L,F) é verdadeiro se F é consequencia semantica do conjunto de formulas L*/
conseq_semantica([],F):- todas_valoracoes_satisfazem(F,T), simbolos_formula(F,Q),comprimento(Q,N), todas_listas_0s_1s(N,E), elimina_lista(T,E,O),O=[],(O=[] -> write("E consequencia semantica"),nl,write([]),nl; write("Nao e consequencia semantica"),nl,write(Q),nl,write(O)),!.
conseq_semantica(L,F):- juntar_conjunto(L,V), J= V imp F, todas_valoracoes_satisfazem(J,T), simbolos_formula(J,Q),comprimento(Q,N), todas_listas_0s_1s(N,E), elimina_lista(T,E,O),O=[],(O=[] -> write("E consequencia semantica"),nl,write(L),nl; write("Nao e consequencia semantica"),nl,write(Q),nl,write(O)),!.


/* -------------------------------------------------------*/

/*junta_elem_listaconj/3 é tal que junta_elem_listaconj(E,L1,L2) é verdadeiro se ..........!!!!!*/
junta_elem_listaconj(E,[],[]).
junta_elem_listaconj(E,[X|R],[[E|X]|S]):- junta_elem_listaconj(E,R,S).

/*partes/2 é tal que partes(L,P) é verdadeiro se P é o conjunto das partes do conjunto L*/
partes([],[[]]).
partes([X|R],P) :- partes(R,S), junta_elem_listaconj(X,S,T), concatena(S,T,P).

subconjuntos_conjunto(C,P) :- partes(C,P).
predicado(C,F,V):- partes(C,P),todas_conseq_semantica(P,F,V),write(V).
todas_conseq_semantica([],_,[]).
todas_conseq_semantica([X|R], F, [X|T]) :- conseq_semantica(X,F), todas_conseq_semantica(R,F,T).
todas_conseq_semantica([X|R],F,T) :- todas_conseq_semantica(R,F,T).



membro_listas([X|R],[Y|L],Y) :- membro(X,Y),membro_listas(R,Y,Y).
membro_listas([X|R],[_|L],Y) :- membro_listas([X|R],L,Y).


predicado([X|[]],[X]).
predicado([X|R],L) :- membro_listas(X,R,Y),!,elimina(Y,R,T), predicado([X|T],Q), concatena([X],Q,E),eliminarep(E,L).
predicado([X|R],L) :- predicado(R,L).

minimais(C,F,L) :- predicado(C,F,T),predicado(T,L).