module HM = Zoo.Main (struct

    let name = "HM"

    type command = Syntax.command

    let options = []

    type environment = {
      ty : Env.t ;
      name: Syntax.Rename.env ;
      value: Eval.env ;
    }
    let add_def x ty v env = {
      ty = Env.add x ty env.ty ;
      name = Syntax.Rename.add x.name x env.name ;
      value = Eval.add x v env.value ;
    }
    let initial_environment = {
      ty = Builtin.initial_env;
      name = Syntax.Rename.SMap.empty ;
      value = Eval.initial_env ;
    }

    let read_more str = 
      let i = ref (String.length str - 1) in
      while !i >= 0 && List.mem str.[!i] [' '; '\n'; '\t'; '\r'] do decr i done ;
      !i < 1 || (str.[!i] <> ';' || str.[!i - 1] <> ';')

    let file_parser = Some (Parser.file Lexer.token)
    let toplevel_parser = Some (Parser.toplevel Lexer.token)

    let exec env c =
      let c = Syntax.Rename.command env.name c in
      match c with
      | Syntax.Def (x, e) ->
        let constr, types, scheme =
          try Typing.infer_top env.ty e
          with
          | Typing.Unif.Fail (ty1, ty2) ->
            Zoo.error ~kind:"Type error"
              "Cannot unify types %a and %a@."
              Printer.typ ty1 Printer.typ ty2
          | Env.Type_not_found name -> 
            Zoo.error "Unknwon type %a" Printer.name name
          | Env.Var_not_found name -> 
            Zoo.error "Unknwon variable %a" Printer.name name
        in 
        let v = Eval.execute env.value e in
        let env = { env with ty = types } in
        Zoo.print_info "@[<2>%a@ : @[%a@]@ = @[%a@]@.%a@.%a@."
          Printer.name x  Printer.scheme scheme  Printer.value v
          Printer.constr constr
          Printer.env env.ty ;
        add_def x scheme v env
  end)

let () = HM.main ()
