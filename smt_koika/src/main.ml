open Koika_smt
open Syntax
open Cmdliner
open File_switch

let query_model =
  let doc = "Query model if SAT" in
  Arg.(value & flag & info["q"; "query"] ~doc)

let print_solver =
  let doc = "Print solver" in
  Arg.(value & flag & info["p"; "print_solver"] ~doc)

let model_outfile =
  let doc = "output model" in
  Arg.(value & (opt (some string) None) & info ["o";"output"] ~doc)

let cmd =
  let exec query_flag print_solver_flag model_outfile =
    let file = File_switch.file in
    do_file file query_flag print_solver_flag model_outfile in
  let info = Cmd.info "koika_smt" in
  Cmd.v info Term.(const exec (* $ file_chooser *) $ query_model $ print_solver $ model_outfile )

let main () = exit (Cmd.eval cmd)
let () = main ()


