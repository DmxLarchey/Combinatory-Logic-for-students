## Aux étudiants M1 de l'UE *Preuves et démonstrations automatisées*

### Confluence de la logique combinatoire en Coq

Bonjour à tous,

Comme indiqué en TP, voici les instructions pour la réalisation
du projet correspondant à l'UE *Preuves et démonstrations automatisées.*

Vous pouvez télécharger l'archive du projet via l'interface
de GitHub (Download ZIP) oubien cloner le projet via

```
git clone https://github.com/DmxLarchey/Combinatory-Logic-for-students.git
```

Une fois dans le repertoire des fichiers *.v (code source Coq),
vous pouvez taper les commandes

```
make all
coqide *.v & 
```

Les dépendances entre les fichiers source Coq sont les suivantes:

```
tacs.v		:
rel.v		: tacs.v
square.v        : tacs.v rel.v
cl.v		:
cl_eq.v		: cl.v
cl_confluent.v	: rel.v square.v cl.v
cl_beta.v	: tacs.v rel.v square.v cl.v cl_eq.v cl_confluent.v
cl_beta_inv.v	: cl.v cl_eq.v cl_beta.v
cl_normal.v  	: rel.v cl.v cl_eq.v cl_beta.v cl_beta_inv.v
cl_beta_redex.v	: rel.v cl.v cl_eq.v cl_beta.v cl_beta_inv.v cl_normal.v
```

Je vous rappelle que le but du projet est de 
**compléter les preuves manquantes** ou 
partiellement manquantes dans les fichiers
**rel.v**, **square.v**, **cl_eq.v**,
**cl_confluent.v**, **cl_beta.v**,
**cl_beta_inv.v** et **cl_normal.v**
(elles se terminent par *Admitted.*) 
Quand vous aurez terminé,
toutes vos preuves devraient se terminer par *Qed.*
Vous pouvez procéder dans l'ordre que vous souhaitez
mais sachez cependant que l'on comprend mieux un énoncé
une fois qu'on a terminé sa preuve. Les dépendances entre 
les fichiers source Coq sont la contrepartie des
dépendances entre certains théorèmes.

Le résultat de votre travail est à me rendre par email
(larchey@loria.fr) à la date du 23 mai 2017. Le travail
est **individuel** même si vous pouvez échanger des idées
entre vous pour résoudre les exercices. N'oubliez pas
de consulter la documentation en ligne de Coq

http://coq.inria.fr/documentation

Je vous rappelle en outre qu'aucune preuve nouvelle n'est
à inventer, certaines ont été *réalisées à la main* lors du
premier cours. Pour les autres, le principe d'induction utilisé
dans la preuve est systématiquement fourni. 
Votre travail est la mise en oeuvre formelle de ces
preuves informelles dans l'outil Coq.

Enfin, nous organiserons une **soutenance sur machine** d'une
durée individuelle d'environ 15m le **jeudi 25 mai 2017**
(date à confirmer) où vous nous présenterez le résultat de
votre travail et nous exposerez les éventuelles difficultés
que vous avez rencontrées.

Bon travail

Dominique Larchey-Wendling

