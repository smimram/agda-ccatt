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

## Coherences

With this version, already in dimension 2, it seems difficult to express coherences. A naive (and wrong) approach (which is the one currently implemented) would consists in saying

> given a 2-dimensional pasting scheme $π$, a term $f$ in $∂⁻(π)$ and a term $g$ in $∂⁺(π)$, we have a coherence $f ⇒ g$.

This is however wrong because we are considering substituted ps. For instance, in the shape of a 2-globe, consider the pasting scheme $α : f ⇒ f : x → x$ (where $f$ is an endomorphism). We do not expect to have a coherence from $f∘f ⇒ f$ for instance.
