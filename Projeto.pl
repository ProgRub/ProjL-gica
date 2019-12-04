/*Projeto Lógica

lista_n_0s_e_1s(0,[]).
lista_n_0s_e_1s(N,[0|L]):- N>0, N1 is N-1, lista_n_0s_e_1s(N1,L).
lista_n_0s_e_1s(N,[1|L]):- N>0, N1 is N-1, lista_n_0s_e_1s(N1,L).