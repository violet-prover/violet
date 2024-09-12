open Cmdliner

let version = "0.1.0"

let lex_cmd ~env =
  let _ = env in
  let arg_file =
    let doc = "The program file to load." in
    Arg.required
    @@ Arg.pos 0 (Arg.some Arg.file) None
    @@ Arg.info [] ~docv:"PROG" ~doc
  in
  let doc = "Load input program file into REPL" in
  let man = [ `S Manpage.s_description; `P "" ] in
  let info = Cmd.info "load" ~version ~doc ~man in
  Cmd.v info
    Term.(
      const (fun filename -> 
        let _ = Gamma.Parser.parse_file filename in 
      ())
      $ arg_file)

let cmd ~env =
  let doc = "gamma" in
  let man = [ `S Manpage.s_bugs; `S Manpage.s_authors; `P "Lîm Tsú-thuàn" ] in

  let info = Cmd.info "gamma" ~version ~doc ~man in
  Cmd.group info [ lex_cmd ~env ]

let () = 
  Eio_main.run @@ fun env ->
  exit @@ Cmd.eval ~catch:false @@ cmd ~env
