@title{Identity}
@date{2026-06-22}

@p{A literate card mixes scribble prose - including forms like @date{...}
   whose first character is a digit - with Violet code blocks. Checking the
   card must scan the @vt|{}| blocks and elaborate only the code, rather than
   parsing the whole document as Violet source.}

@vt|{
\universe U
\let id (A : U) (x : A) : A => x
}|

@p{The identity is reused below to confirm cross-block scope holds.}

@vt|{
\let id-again (A : U) : A -> A => id A
}|
