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
  linenoise
  violet_kernel
  violet_surface
  violet_elab
  violet_literate
  violet_langserver)
 (tags
  ("dependent-types" "type-theory" "proof-assistant")))

(package
 (name violet_common)
 (synopsis "Violet shared diagnostics")
 (depends (ocaml (>= 5.3)) dune ppx_deriving asai))

(package
 (name violet_kernel)
 (synopsis "Violet kernel (trusted core)")
 (depends (ocaml (>= 5.3)) dune ppx_deriving ppx_expect bwd))

(package
 (name violet_surface)
 (synopsis "Violet surface syntax (parser and AST)")
 (depends (ocaml (>= 5.3)) dune ppx_deriving ppx_expect violet_kernel asai yuujinchou))

(package
 (name violet_elab)
 (synopsis "Violet elaborator")
 (depends (ocaml (>= 5.3)) dune ppx_deriving ppx_expect violet_surface asai algaeff yuujinchou bwd eio))

(package
 (name violet_interactive)
 (synopsis "Violet interactive query layer")
 (depends (ocaml (>= 5.3)) dune violet_elab violet_kernel asai))

(package
 (name violet_project)
 (synopsis "Violet project loader and manifest management")
 (depends (ocaml (>= 5.3)) dune base-unix violet_surface violet_elab tsort ppx_deriving ppx_expect))

(package
 (name violet_literate)
 (synopsis "Violet literate programming (weave)")
 (depends
  (ocaml (>= 5.3))
  dune
  ppx_expect
  violet_common
  violet_surface
  violet_elab
  violet_project
  violet_interactive
  violet_kernel
  asai
  tsort
  base-unix
  yuujinchou))

(package
 (name violet_langserver)
 (synopsis "Violet language server (LSP)")
 (depends
  (ocaml (>= 5.3))
  dune
  violet_interactive
  violet_elab
  violet_kernel
  violet_project
  violet_literate
  asai
  eio
  linol
  linol-eio
  tsort
  ppx_expect))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
