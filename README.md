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

The usual one is simply the case when $\ell=\ell'$.
All other rules remain the same.
There are two versions of it,
as we can use either judgemental or propositional equality in the
formulation of the $\beta$-rule.
In the former case, we call it **strict**,
and in the latter case, we refer to it as **weak**.

The main purpose of it is to reformulate Voevodsky's axiom of proposition resizing.
In `Resizing.agda`, we show that

> Weak PropTruncation $+$ Resizing $=$ Resizable Weak PropTruncation

In other words, the existence of the usual weak propositional truncation, together with the validity of the proposition resizing axiom, is equivalent to the existence of weak resizable propositional truncation.

The proof is not complicated and can be seen as a direct corollary of the fact that "the type $A$ is a weak propositional truncation of the type $B$" is preserved
by equivalences.
For convenience,
we use some lemmas from the `Cubical Agda` library in the proof.
However, it should be emphasized that this result relies solely on vanilla HoTT, and even the univalence axiom is not required.

What would happen if we use the *strict* one?
Would it be able to provide a constructive version of propositional resizing?
