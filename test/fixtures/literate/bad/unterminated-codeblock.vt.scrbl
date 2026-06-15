@p{This card opens a Violet code block on the next line but never closes it.
   The code inside is well-typed, so the unterminated block is the only fault:
   the weaver must reject it instead of swallowing the rest of the document.}

@vt|{
\universe U
\let id (A : U) (x : A) : A => x
