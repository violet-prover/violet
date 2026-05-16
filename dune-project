(lang dune 3.17)

(name violet)

(generate_opam_files true)

(source
 (uri "git+https://codeberg.org/dannypsnl/violet.git"))

(homepage "https://violet-lang.org")

(documentation "https://violet-lang.org")

(bug_reports "https://codeberg.org/dannypsnl/violet/issues")

(authors "Lîm Tsú-thuàn")

(maintainers "Lîm Tsú-thuàn")

(license LICENSE)

(package
 (name violet)
 (synopsis "A small dependent type language")
 (description "Violet is a small dependent type language.")
 (depends
  (ocaml (>= 5.3))
  dune
  cmdliner
  eio
  eio_main
  tsort
  ppx_expect
  violet_kernel
  violet_elab)
 (tags
  ("dependent-types" "type-theory" "proof-assistant")))

(package
 (name violet_kernel)
 (synopsis "Violet kernel (trusted core)")
 (depends (ocaml (>= 5.3)) dune ppx_deriving ppx_expect bwd))

(package
 (name violet_elab)
 (synopsis "Violet elaborator")
 (depends (ocaml (>= 5.3)) dune ppx_deriving ppx_expect asai algaeff yuujinchou bwd eio))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
