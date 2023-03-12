%*******************************************************************************
%                                    AETOILE
%*******************************************************************************

/*
Rappels sur l'algorithme
 
- structures de donnees principales = 2 ensembles : P (etat pendants) et Q (etats clos)
- P est dedouble en 2 arbres binaires de recherche equilibres (AVL) : Pf et Pu
 
   Pf est l'ensemble des etats pendants (pending states), ordonnes selon
   f croissante (h croissante en cas d'egalite de f). Il permet de trouver
   rapidement le prochain etat a developper (celui qui a f(U) minimum).
   
   Pu est le meme ensemble mais ordonne lexicographiquement (selon la donnee de
   l'etat). Il permet de retrouver facilement n'importe quel etat pendant

   On gere les 2 ensembles de fa�on synchronisee : chaque fois qu'on modifie
   (ajout ou retrait d'un etat dans Pf) on fait la meme chose dans Pu.

   Q est l'ensemble des etats deja developpes. Comme Pu, il permet de retrouver
   facilement un etat par la donnee de sa situation.
   Q est modelise par un seul arbre binaire de recherche equilibre.

Predicat principal de l'algorithme :

   aetoile(Pf,Pu,Q)

   - reussit si Pf est vide ou bien contient un etat minimum terminal
   - sinon on prend un etat minimum U, on genere chaque successeur S et les valeurs g(S) et h(S)
	 et pour chacun
		si S appartient a Q, on l'oublie
		si S appartient a Ps (etat deja rencontre), on compare
			g(S)+h(S) avec la valeur deja calculee pour f(S)
			si g(S)+h(S) < f(S) on reclasse S dans Pf avec les nouvelles valeurs
				g et f 
			sinon on ne touche pas a Pf
		si S est entierement nouveau on l'insere dans Pf et dans Ps
	- appelle recursivement etoile avec les nouvelles valeurs NewPF, NewPs, NewQs

*/

%*******************************************************************************

:- ['avl.pl'].       % predicats pour gerer des arbres bin. de recherche   
:- ['taquin.pl'].    % predicats definissant le systeme a etudier

%*******************************************************************************

main :-
	% initialisations Pf, Pu et Q 

	% lancement de Aetoile
	initial_state(S0),
	G0 is 0,
	heuristique(S0,H0),
	F0 is G0+H0,
	empty(Pf),
	empty(Pu),
	empty(Q),
	insert([[F0,H0,G0],S0],Pf,Pf1),
	insert([S0,[F0,H0,G0],nil,nil], Pu, Pu1),
	aetoile(Pf1,Pu1,Q).




%*******************************************************************************
%Cas trival pas de solution.
aetoile([],[],_):- print('PAS de SOLUTION : L’ETAT FINAL N’EST PAS ATTEIGNABLE !').
aetoile(Pf, Pu, Q) :-
	suppress_min([[FI,HI,GI],UI],Pf,PfInt),
	(final_state(UI)->
		%Cas trivial si l'état actuel est l'état final
		belongs([UI,[FI,HI,GI],Pere,Action],Pu),
		insert([UI,[FI,HI,GI],Pere,Action],Q,Qf),
		affiche_solution(Qf,[UI,[FI,HI,GI],Pere,Action])
		;
		%Cas général, suppression du noeud frère associé dans Pu
		suppress([UI,[FI,HI,GI],Pere,Action],Pu,PuInt),
		%Développement de U
		expand([[FI,HI,GI],UI],Successors),
		loop_successors(Successors,PuInt,PfInt,Q,PuNew,PfNew),
		insert([UI,[FI,HI,GI],Pere,Action],Q,QNew),
		aetoile(PfNew,PuNew,QNew)
	).
	
	
%loop_successor
treat_1successor([V,[F,H,G],U,Av],Pu,Pf,Q,PuAux,PfAux):-
	((belongs([V,_,_,_],Q))-> 
	PuAux=Pu,PfAux=Pf
	;
		((suppress([V,[Fold,Hold,Gold],_Uold,_Aold],Pu,PuInt))->
				(([Fold,Hold,Gold]@>[F,H,G])->
				suppress([[Fold,Hold,Gold],V],Pf,PfInt),
				insert([V,[F,H,G],U,Av],PuInt,PuAux),
				insert([[F,H,G],V],PfInt,PfAux)
				;
				PuAux=Pu,
				PfAux=Pf
				)
		;
		insert([[F,H,G],V],Pf,PfAux),
		insert([V,[F,H,G],U,Av],Pu,PuAux)
		)
	).

loop_successors([],Pu,Pf,_,Pu,Pf).
loop_successors([First|Rest],Pu,Pf,Q,PuNew,PfNew):-
	treat_1successor(First,Pu,Pf,Q,PuAux,PfAux),
	loop_successors(Rest,PuAux,PfAux,Q,PuNew,PfNew).


%Test Unitaire
test_unitaire:-
	initial_state(S0),
	G0 is 0,
	heuristique(S0,H0),
	F0 is G0+H0,
	empty(Pf),
	empty(Pu),
	empty(Q),
	insert([[F0,H0,G0],S0],Pf,Pf1),
	insert([S0,[F0,H0,G0], nil, nil],Pu,Pu1),
	expand([[F0,H0,G0],S0],Successors),
	loop_successors(Successors,Pu1,Pf1,Q,PuNew,PfNew),
	writeln('Pf\n'),
	put_flat(PfNew),
	writeln('\nPu'),
	put_flat(PuNew).


%Av action pour aller à V, Kuv coût de l'action pour aller de U à V
%On stock dans successors avec le findall les successeurs potentiels

expand([[_F,_H,G],U],Successors):-
	findall([V,[Fv,Gv,Hv],U,Av],(rule(Av,Kuv,U,V),heuristique(V,Hv),Gv is G+Kuv, Fv is Hv+Gv),Successors).



affiche_solution(Q,[Actuel,Val,Pere,A]):-
	suppress([Actuel,Val,Pere,A],Q,Qp),
	(
		belongs([Pere,Valp,Perep,Ap],Q)->
		affiche_solution(Qp,[Pere,Valp,Perep,Ap]),
		writeln(A),
		write_state(Actuel)
	;
		writeln('Début')
	).
	
/* RunTime test */

test_time(Runtime) :-
	get_time(Start),
	main,
	get_time(Stop),
	Runtime is Stop-Start.
