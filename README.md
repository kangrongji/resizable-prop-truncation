# Resizing by Propositional Truncation

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
\Gamma \ \vdash  \| X \| : \mathsf{Type} \ \ \ell'
}
$$

The usual propositional truncation simply the case when $\ell=\ell'$.
All other rules remain the same.
There are two versions of it,
as we can use either judgemental or propositional equality in the
formulation of the $\beta$-rule.
In the former case, we call it **strict**,
and in the latter case, we refer to it as **weak**.

The main use of it is to reformulate Voevodsky's axiom of proposition resizing.
In `Resizing.agda`, we show that

> Weak PropTruncation $+$ Resizing $=$ Resizable Weak PropTruncation

In other words, the existence of the usual weak propositional truncation, together with the validity of the proposition resizing axiom, is equivalent to the existence of weak resizable propositional truncation.

The proof is not complicated and can be seen as a direct corollary of that the property "$A \ \textsf{is a propositional truncation of} \ B$" is preserved
by equivalence.
For convenience,
we use some lemmas from the `Cubical Agda` library.
It should be noted that this result relies solely on vanilla HoTT, and even the univalence axiom is not required.

What would happen if we use the *strict* one?
