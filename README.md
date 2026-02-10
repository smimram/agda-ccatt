Unbiased closed categories formalized in Agda
=============================================

This is the formalization associated to the paper [_An unbiased simply typed combinatory logic_](http://www.lix.polytechnique.fr/Labo/Samuel.Mimram/docs/mimram_cccatt.pdf). More precisely, we show the equivalence between

- our calculus of unbiased combinators and
- simply typed combinatory logic.

It mainly consists of the following files:

- [Ty.agda](agda/Ty.agda): type variables, types, type substitutions,
- [CL.agda](agda/CL.agda): simply typed combinatory logic,
- [CC.agda](agda/CC.agda): unbiased combinators,
- [Equivalence.agda](agda/Equivalence.agda): the equivalence between the above two.

Some current limitations of the formalization (that could be lifted in the future):

- we handle only the implicational fragment only, although adding support for products should not be significantly more difficult,
- we do not formalize pasting schemes: we simply suppose in [Ty.agda](agda/Ty.agda) that some types are pasting, and that implies that they are uniquely inhabited,
- some easy familiar properties are not fully formalized (such as traditional lemmas on contexts).

We have also tried a [cubical approach](experiments/cubical) which did not go through.
