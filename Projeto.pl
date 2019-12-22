/*Projeto Lógica Computacional*/

/*
Elementos do grupo:
Diego Andrés da Silva Briceño (2043818),
Filipe Orlando Namora Gomes (2045218),
José Alejandro Ferreira Gouveia (2028616),
Rúben José Gouveia Rodrigues (2046018)
*/


/* Predicados auxiliares (conetivos)*/
:-op(100, fy, 'neg').
:-op(200, xfy, 'e').
:-op(300, xfy, 'ou').
:-op(400, xfy, 'imp').


/*acrescenta/3 é tal que acrescenta(X,L1,L2) tem o valor verdadeiro se L2 é a lista que  resulta de colocar o elemento X na cabeça da lista L1*/
acrescenta(X,[],[X]).
acrescenta(X,L,[X|L]).

/*concatena/3 é tal que concatena(L1,L2,L3) é verdadeiro se L3 é a lista que resulta de juntar as listas L1 e L2*/
concatena([],L,L).
concatena([X|R],L,[X|S]) :- concatena(R,L,S).

/* membro/2 é tal que membro(X,L) tem o valor verdadeiro se X pertence à lista L*/
membro(X, [X | _]).
membro(X, [_ | C]) :- membro(X, C).


/* comprimento/2 é tal que comprimento(L,N) é verdadeiro se N é o comprimento da lista L*/
comprimento([], 0).
comprimento([_|X], N) :-comprimento(X, N1), N is N1+1.

/*eliminarep/2 é tal que eliminarep(X,Y) é verdadeiro se Y é a lista que resulta de retirar da lista X todos exceto a ultima ocorrencia de cada um dos seus elementos*/
eliminarep([],[]).
eliminarep([X|R],S) :- membro(X,R), eliminarep(R,S).
eliminarep([X|R],[X|S]) :- not(membro(X,R)), eliminarep(R,S).


/* enesimo/3 é tal que enesimo(N,L,X) é verdadeiro se N é um número natural positivo e X é o elemento que está na posição N da lista L*/
enesimo(1,[X|_],X).
enesimo(N,[_|L],Y) :- enesimo(N1,L,Y), N is N1+1.


/* calc_valor/4 é tal que ao executar uma consulta do tipo calc_valor(F,S,L,V) onde F é uma fórmula da Linguagem neg, e, ou e imp, S é uma lista, sem repetições, dos símbolos proposicionais que ocorrem
em dita fórmula e L uma lista de 0s e 1s com o mesmo comprimento da lista S, o interpretador Prolog devolverá V, o valor lógico de F por qualquer
valoração v que atribui a cada símbolo proposicional da lista S o valor lógico que ocorre na posição correspondente na lista L*/
calc_valor(F,L1,L2,V) :- enesimo(N,L1,F), enesimo(N,L2,V).
calc_valor(neg X,L1,L2,0) :- calc_valor(X,L1,L2,1).
calc_valor(neg X,L1,L2,1) :- calc_valor(X,L1,L2,0).
calc_valor(X e Y, L1,L2,1) :- calc_valor(X,L1,L2,1),calc_valor(Y,L1,L2,1).
calc_valor(X e Y, L1,L2,0) :- not(calc_valor(X e Y,L1,L2,1)).
calc_valor(X ou Y, L1,L2,0) :- calc_valor(X,L1,L2,0),calc_valor(Y,L1,L2,0).
calc_valor(X ou Y, L1,L2,1) :- not(calc_valor(X ou Y,L1,L2,0)).
calc_valor(X imp Y,L1,L2,0) :- calc_valor(X,L1,L2,1), calc_valor(Y,L1,L2,0).
calc_valor(X imp Y,L1,L2,1) :- not(calc_valor(X imp Y,L1,L2,0)).


/* lista_n_0s_e_1s/2 é tal que lista_n_0s_e_1s(N,L) é verdadeiro se L é uma lista constituída apenas por 0s e 1s de comprimento N, sendo N um número inteiro não negativo*/
lista_n_0s_e_1s(0,[]).
lista_n_0s_e_1s(N,[0|L]) :- N>0, N1 is N-1, lista_n_0s_e_1s(N1,L).
lista_n_0s_e_1s(N,[1|L]) :- N>0, N1 is N-1, lista_n_0s_e_1s(N1,L).


/*todas_listas_0s_1s/2 é tal que todas_listas_0s_1s(N,L) recebe um número inteiro não negativo N e devolve a lista L constituida por todas as listas de comprimento N constituidas por Os e 1s.*/
todas_listas_0s_1s(N,R) :- findall(L,lista_n_0s_e_1s(N,L),R).

/* simb_prop/2 é tal que sim_prop(Y,Y) é verdadeiro se Y é simbolo proposicional */
simb_prop(F,F) :- not(F = neg X), not(F = X e Y), not(F = X ou Y), not(F = X imp Y).
simb_prop(neg F, Z) :- simb_prop(F,Z).
simb_prop(X e _,U) :- simb_prop(X,U).
simb_prop(_ e Y,I) :- simb_prop(Y,I).
simb_prop(X ou _,U) :- simb_prop(X,U).
simb_prop(_ ou Y,I) :- simb_prop(Y,I).
simb_prop(X imp _,U) :- simb_prop(X,U).
simb_prop(_ imp Y,I) :- simb_prop(Y,I).


/*simbolos_formula/2 é tal que simbolos_formula(F,L) é verdadeiro se L é a lista com todos os simbolos proposicionais da formula F*/
simbolos_formula(F,L) :- findall(U,simb_prop(F,U),T), eliminarep(T,L).

/*simbolos_conjunto/2 é tal que simbolos_conjunto(L1,L2) é verdadeiro se L2 é a lista de todos os simbolos proposicionais que ocorrem nalguma formula da lista de formulas L1*/
simbolos_conjunto([],[]).
simbolos_conjunto([F|R],L) :- simbolos_formula(F,T), simbolos_conjunto(R,U), concatena(T,U,Y), eliminarep(Y,L).

/*todas_valoracoes_satisfazem/2 é tal que todas_valoracoes_satisfazem(F,V) é verdadeiro se V é a lista de todas as valoracoes que satisfazem a formula F*/
todas_valoracoes_satisfazem(F,V) :- simbolos_formula(F,L), comprimento(L,N), todas_listas_0s_1s(N,R), findall(A,valoracao_satisfaz(F,L,R,A),V).

/*valoracao_satisfaz/4 é tal que valoracao_satisfaz(F,S,L,V) é verdadeiro se V é uma valoracao de L que satisfaz a formula F, sendo S a lista de simbolos proposicionais de F.*/
valoracao_satisfaz(F,S,[X|_],X) :- calc_valor(F,S,X,1).
valoracao_satisfaz(F,S,[_|T],R) :- valoracao_satisfaz(F,S,T,R).


/*juntar_conjunto/2 é tal que juntar_conjunto(L,V) é verdadeiro se V é a formula que se obtem de concatenar todas as formulas da lista L com e´s */
juntar_conjunto([X|[]],X).
juntar_conjunto([H|R],P) :- juntar_conjunto(R,T),P= H e T.

/*imprime_valoracoes/3 é tal que imprime_valoracoes(L,L,X) recebe uma lista L de simbolos proposicionais de uma dada formula e uma lista X com todas as valoracoes que satisfazem
a mesma formula, e imprime as valoracoes correspondentes a cada simbolo proposicional que permite satisfazer a formula.*/
imprime_valoracoes(L,L,[]).
imprime_valoracoes([],[],[]).
imprime_valoracoes(L,[X|R],[[V1|V2]|O]) :- write("v("), write(X), write(") = "), write(V1), (not(V2=[]) -> write(" e "),imprime_valoracoes(L,R,[V2|O]); (not(O=[]) -> nl, write("ou "), imprime_valoracoes(L,L,O);imprime_valoracoes(L,L,O))).


/* ************** Exercicio 1 ************** */
/*exercicio1/1 é tal que exercicio1(L) recebe um conjunto de formulas L e devolve a informacao de todas as valoracoes que satisfazem esse conjunto*/
/*Baseamos o nosso raciocinio no facto de uma valoração satisfazer um conjunto de fórmulas ser equivalente a essa valoração satisfazer a fórmula obtida de juntar todas as fórmulas do conjunto com e´s
Logo, a funçao simbolos_conjunto descobrirá os simbolos proposicionais presentes no conjunto de fórmulas, para o imprimir das valorações, juntar_conjunto juntará todas as fórmulas do conjuntos usando e´s , de modo a obter uma fórmula
E obtemos as valoracoes que satisfazem a fórmula mencionada anteriormente, e é mostrado ao utilizador as valorações que satisfazem o conjunto, ou o facto de não haver valorações que satisfazem o conjunto*/
exercicio1(L) :- simbolos_conjunto(L,C), write("O conjunto de simbolos proposicionais do conjunto de formulas "), write(L), write(" e: "), write(C),nl, juntar_conjunto(L,F),todas_valoracoes_satisfazem(F,V), (V=[] -> write("Nao existe nenhuma valoracao que satisfaca todas as formulas do conjunto: "), write(L); write("As formulas do conjunto sao satisfeitas, por qualquer valoracao v, tal que: "),nl, imprime_valoracoes(C,C,V)),!.

/*Exemplos de objetivos que podem ser executados para testar o programa:
 - existem valoracoes que satisfazem: 
 exercicio1([p imp (neg r imp q),r ou (p e q)]).
 exercicio1([p imp q, q imp r, q imp t, neg(r e t)]).

 - nao existem valoracoes que satisfazem: 
 exercicio1([(p ou q) imp neg r, q e r]).
 exercicio1([p imp neg q, q imp neg r, p e neg p]).
 */

/* -------------------------------------------------------*/

/*elimina/3 é tal que elimina(X,L1,L2) é verdadeiro se L2 é a lista que resulta de retirar da lista L1 todas as ocorrências do elemento X*/
elimina(_,[],[]).
elimina(X,[X|L],L1) :- elimina(X,L,L1).
elimina(X,[Y|L],[Y|L1]) :- not(Y=X), elimina(X,L,L1).

/*elimina_lista/3 é tal que elimina_lista(X,Y,L) é verdadeiro se L é a lista que resulta de retirar da lista Y todas as ocorrências dos elementos da lista X*/
elimina_lista([],L,L).
elimina_lista([X|R],T,L) :- elimina(X,T,P), elimina_lista(R,P,L).



/* ************** Exercicio 2 ************** */
/*exercicio2/2 é tal que exercicio2(L,F) é verdadeiro se F é consequencia semantica do conjunto de formulas L*/
/*Baseamos o nosso raciocinio no facto de ´F ser consequência semântica de C´ ser equivalente a ´(todas as fórmulas de C concatenadas com e´s) implica F´ ser tautologia, temos 2 casos:
Se o conjunto de fórmulas é vazio, verificamos se F é uma tautologia, obtendo todas as valorações que satisfazem F, comparando essa lista com a lista de todas as valorações possíveis para a fórmula, por meio de eliminação,
Isto é, usando o elimina_lista, vamos eliminar todas as valorações que satisfazem F do conjunto de todas as valorações possíveis e, se a lista obtida for [], então sabemos que é tautologia e informamos o utilizador de tal
Se tal não acontecer, o utilizador é informado e também é informado uma valoração que não satisfaz, daí o elimina_lista, o resultado desta clausula é a lista de valorações que prova que F não é tautologia, e assim damos o exemplo ao utilizador.
Se o conjunto não for vazio, o raciocinio é o mesmo, só que junta-se as fórmulas do conjunto com e´s ,  graças à clausula juntar_conjunto, e juntamos a fórmula resultante com a fórmula que queremos ver se é consequência semântica
Com um implica, como a propriedade diz, e de seguida o procedimento é idêntico ao indicado anteriormente, para a fórmula J= V imp F.*/
exercicio2([],F) :- todas_valoracoes_satisfazem(F,T), simbolos_formula(F,Q), comprimento(Q,N), todas_listas_0s_1s(N,E), elimina_lista(T,E,O), (O=[] -> write("'"), write(F), write("' e tautologia."), nl;  write("'"), write(F), write("' nao e tautologia."), nl, write("Uma valoracao que nao verifica este facto e, por exemplo: "), imprime_valoracoes(Q,Q,O)), !.
exercicio2(L,F) :- juntar_conjunto(L,V), J= V imp F, todas_valoracoes_satisfazem(J,T), simbolos_formula(J,Q), comprimento(Q,N), todas_listas_0s_1s(N,E), elimina_lista(T,E,O), (O=[] -> write("'"), write(F), write("' e consequencia semantica de "), write(L), nl; write("'"), write(F), write("' nao e consequencia semantica de "), write(L),nl, write("Uma valoracao que nao verifica este facto e, por exemplo: "), O= [B|_], imprime_valoracoes(Q,Q,[B])), !.

/*Exemplos de objetivos que podem ser executados para testar o programa:
 - e consequencia semantica:
 exercicio2([p imp (r imp q), r ou q], p imp q).
 exercicio2([p imp q, q imp r, q imp t, neg(r e t)], neg p).

 - nao e consequencia semantica: 
 exercicio2([p imp (r imp q), r ou q], q).
 exercicio2([neg t,t imp q, neg p ou q], q).
 */


/* -------------------------------------------------------*/

/*junta_elem_listaconj/3 é um predicado auxiliar ao predicado partes*/
junta_elem_listaconj(_,[],[]).
junta_elem_listaconj(E,[X|R],[[E|X]|S]) :- junta_elem_listaconj(E,R,S).

/*partes/2 é tal que partes(L,P) é verdadeiro se P é o conjunto das partes do conjunto L*/
partes([],[[]]).
partes([X|R],P) :- partes(R,S), junta_elem_listaconj(X,S,T), concatena(S,T,P).

/*conseq_semantica/2 é tal que conseq_semantica(L,F) se F é consequencia semantica de L
O raciocinio usado aqui é o raciocinio usado no exercicio2, só que já não é utilizado o elimina_lista pois esta clausula já não informará o utilizador de nada, é uma clausula auxiliar ao todas_conseq_semantica
Por isso, simplesmente compara-se a lista de valorações que satisfazem o facto de F ser consequência semântica de L com todas as valorações possíveis, se as listas são iguais, então F é consequência semântica de L*/
conseq_semantica([],F) :- todas_valoracoes_satisfazem(F,T), simbolos_formula(F,Q),comprimento(Q,N), todas_listas_0s_1s(N,E), T=E,!.
conseq_semantica(L,F) :- juntar_conjunto(L,V), J= V imp F, todas_valoracoes_satisfazem(J,T), simbolos_formula(J,Q),comprimento(Q,N), todas_listas_0s_1s(N,E),T=E,!.

/*lista_conseq_semanticas/3 é tal que lista_conseq_semanticas(C,F,L) é verdadeiro se L é a lista de todos os subconjuntos de C tal que F é consequencia semantica dos subconjuntos*/
lista_conseq_semanticas(C,F,V) :- partes(C,P), todas_conseq_semantica(P,F,V).

/*todas_conseq_semantica/3 é tal que todas_conseq_semantica(P,F,L) é verdadeiro se L é a lista de todos os conjuntos de P dos quais F é consequencia semantica*/
todas_conseq_semantica([],_,[]).
todas_conseq_semantica([X|R], F, [X|T]) :- conseq_semantica(X,F), todas_conseq_semantica(R,F,T).
todas_conseq_semantica([_|R],F,T) :- todas_conseq_semantica(R,F,T).

/*membro_listas/3 é tal que membro_listas(L,T,X), é verdadeiro se X é uma lista da lista T tal que todos os elementos da lista L são membros da lista X
Esta clausula será util para saber os conjuntos minimais pois se esta clausula é verdade, todos os membros de L estão na lista X da lista T e procedemos a eliminar a lista X, como se pode ver na clausula minimais_aux*/
membro_listas([],_,_).
membro_listas([X|R],[Y|L],Y) :- membro(X,Y), membro_listas(R,[Y|L],Y).
membro_listas([X|R],[_|L],Y) :- membro_listas([X|R],L,Y).

/*minimais_aux/2 é tal que minimais_aux(L,R) é verdadeiro se R é a lista que contém todos os conjuntos minimais de L, com repetidos*/
minimais_aux([X|[]],[X]).
minimais_aux([X|R],[X|L]) :- membro_listas(X,R,Y),!, elimina(Y,R,T), minimais_aux([X|T],L).
minimais_aux([_|R],L) :- minimais_aux(R,L).

/*minimais/3 é tal que minimais(C,F,L) é verdadeiro se L é a lista dos subconjuntos minimais de C tal que F é consequencia semantica dos subconjuntos*/
minimais(C,F,L) :- lista_conseq_semanticas(C,F,T), minimais_aux(T,R), eliminarep(R,L).


/* ************** Exercicio 3 ************** */
/*exercicio3/2 é tal que é imprimida a informacao do conjunto de todos os subconjuntos minimais do conjunto de formulas C dos quais a formula F é conquencia semantica*/
exercicio3(C,F) :- (minimais(C,F,L) -> (L=[[]] -> write("A formula '"), write(F),write("' e tautologia."); write("O conjunto de todos os subconjuntos minimais de "), write(C), write(" dos quais '"), write(F), write("' e consequencia semantica e: "), nl, write(L)); write("Nao existe nenhum subconjunto de "), write(C), write(" que tenha como consequencia semantica a formula '"), write(F), write("'.")), !.

/*Exemplos de objetivos que podem ser executados para testar o programa:
 - existem subconjuntos minimais como conquencia semantica: 
 exercicio3([p imp q, p ou q,p,q],q).
 exercicio3([p imp q, p ou q,p ou r,p], r imp p).

 - nao existem subconjuntos minimais como conquencia semantica: 
 exercicio3([p imp q, p ou q,q],p e q).
 exercicio3([p imp q, p ou q,p ou r, r imp q], r).
 */
