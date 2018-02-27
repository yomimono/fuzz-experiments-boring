(* stedolan: I've also been playing with ocaml-test-omp (but not very seriously yet), to try and find bugs in the ocaml typechecker
   I think at least we should be able to reproduce https://caml.inria.fr/mantis/view.php?id=7712
  x I tweaked `position_to_crowbar`, `constant_to_crowbar` and the generators for identifiers to generate much fewer values
   before, it seemed to waste a lot of its time mutating location information which didn't change any behaviour
   (I suppose it would be cool to determine that automagically, but I'm not sure how)
   so I think a test that generates only programs of the form `type t = <type> let f : <type> = function <pats>` would be interesting
  x we could constrain the right-hand side of each <pat> to be a constant constructor or a variable
   which is big enough to exercise all of the GADT pattern-matching stuff, but small enough that fuzzing won't get lost in the expression language or the module language *)

let () =
  (* get an arbitrary type, but always call it `t` *)
  let type_named ~name : Parsetree.type_declaration Crowbar.gen = Crowbar.(map [Parsetree_406.type_declaration_to_crowbar] (fun d ->
      Parsetree.{d with ptype_name = (Location.mknoloc name)}))
  in
  let constrained_by ~name : Parsetree.core_type =
    Ast_helper.Typ.mk @@ Parsetree.Ptyp_constr ((Location.mknoloc (Longident.parse name)),[]) in
  Crowbar.(add_test ~name:"make a program" [type_named ~name:"t"; list Parsetree_406.case_to_crowbar] (fun t cases ->
      let open Parsetree in
      let name = "f" in
      let function_exp =
        { pexp_loc = Location.none; pexp_attributes = [];
          pexp_desc = Pexp_function cases} in
      let constrained_exp =
        { pexp_loc = Location.none; pexp_attributes = [];
          pexp_desc = Pexp_constraint (function_exp, constrained_by ~name:"t")} in
      let exp_vb = Ast_helper.Vb.mk (Ast_helper.Pat.mk (Ppat_var (Location.mknoloc name))) constrained_exp in
      let exp_str =
        { pstr_loc = Location.none; pstr_desc = Pstr_value (Asttypes.Nonrecursive, [exp_vb])} in
      let t_str = 
        { pstr_loc = Location.none; pstr_desc = Pstr_type (Asttypes.Recursive, [t])}
      in
      let program = [t_str; exp_str] in
      (* if we print it, can we read it back? *)
      let program_str = Format.asprintf "%a@." Pprintast.structure program in
      Format.printf "%a@." Pprintast.structure program;
      let lexbuf = Lexing.from_string program_str in
      Env.set_unit_name "Radmod"; (* how side-effecting is this? *)
      try ((ignore @@ Typemod.type_implementation "string1" "/tmp/lollerskates" "string2"
              (Compmisc.initial_env ()) (Parse.implementation lexbuf)); Crowbar.fail "I somehow made a well-typed program, plz alert media")
      with
      | Typemod.Error (_, env, e) -> Format.eprintf "%a\n%!" (Typemod.report_error env) e
      | Typetexp.Error (_, env, e) -> Format.eprintf "%a\n%!" (Typetexp.report_error env) e
      | Typecore.Error (_, env, e) -> Format.eprintf "%a\n%!" (Typecore.report_error env) e
      | Typedecl.Error (_, e) -> Format.eprintf "%a\n%!" Typedecl.report_error e
      | Syntaxerr.Error _ -> Printf.eprintf "Syntax error\n%!"
      | Lexer.Error _ -> Printf.eprintf "Lexing error\n%!"
    ));
