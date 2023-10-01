# Resizing by PropTruncation

The **resizable** propositional truncation
is a variant of usual propositional truncation
in homotopy type theory.
The only difference is that the resulting type
can be placed in any universe you like.
This means the type formation rule now becomes

$$
\frac
{
\ell \ \ \ell' : \mathsf{Level}
\quad \ \
\Gamma \ \vdash X : \mathsf{Type} \ \ \ell
}
{
\Gamma \ \vdash || X || : \mathsf{Type} \ \ \ell'
}
$$

All other rules remain the same.
The usual one is simply the special case when $\ell=\ell'$.
There are, in fact, two versions of it,
as we can use either judgemental or propositional equality in the
formulation of the $\beta$-rule.
In the former case, it is called **strict**,
and in the latter case, it is referred to as **weak**.

The main purpose is to reformulate Voevodsky's axiom of proposition resizing.
In `Resizing.agda`, we show that

> Weak PropTruncation $+$ Resizing $=$ Resizable Weak PropTruncation

In other words, the existence of the usual weak propositional truncation, together with the validity of the proposition resizing axiom, is equivalent to the existence of weak resizable propositional truncation.

The proof is not complicated and can be seen as a direct corollary of "the type $A$ is a weak propositional truncation of the type $B$" is preserved
by equivalence.
For convenience,
we used in the proof some lemmas from the $\textsf{Cubical Agda}$ library.
However, it should be emphasized that this result relies solely on vanilla HoTT, and even the univalence axiom is not required.

This result shows the consistency of resizable *weak* propositional truncation. What about the *strict* one?
Perhaps it's not too hard to construct a model that justifies the strict version. Another interesting question is whether or not it could lead to a constructive version of propositional resizing.
