# Unbiased bicategories

We show that there is an equivalence between

- 2-dimensional models of CaTT
- bicategories

This is done by implementing polygraphs (in low dimensions) as a type-theoretic structure.

## Pasting schemes

A *pasting shape* is the shape of a pasting scheme. For instance, in dimension 1, a pasting shape is a natural number, e.g. `3` encodes the shape

$$
x → y → z → w
$$

consisting of 3 composable arrow. A *pasting scheme* of this shape is actually the data of a substitution toward this pasting shape, ie the data of 4 0-cells and 3-cells as above, with no restriction. For instance, given an endomorphism $f : x → x$, we have a pasting scheme

$$
x \overset f\to x \overset f\to x \overset f\to x
$$
