module Crowbar = struct
  include Crowbar
  let string = (choose
                  [ const "a"; const "b";
                    const "B"; const "A";
                    const "foo"; const "bar";
                    const "baz"; const "quux";
                    const "porg"; const "morp";])
  let bytes = string
end


module Location = struct
  include Location
  let to_crowbar = Crowbar.const Location.none
end

module Asttypes = struct
  include Ast_406.Asttypes
  type 'a l = [%import: 'a Asttypes.loc] [@@deriving crowbar]
  type arg_label_ = [%import: Asttypes.arg_label] [@@deriving crowbar]
  type label_ = [%import: Asttypes.label] [@@deriving crowbar]
  type closed_flag_ = [%import: Asttypes.closed_flag] [@@deriving crowbar]
  type rec_flag_ = [%import: Asttypes.rec_flag] [@@deriving crowbar]
  type direction_flag_ = [%import: Asttypes.direction_flag] [@@deriving crowbar]
  type override_flag_ = [%import: Asttypes.override_flag] [@@deriving crowbar]
  type variance_ = [%import: Asttypes.variance] [@@deriving crowbar]
  type private_flag_ = [%import: Asttypes.private_flag] [@@deriving crowbar]
  type mutable_flag_ = [%import: Asttypes.mutable_flag] [@@deriving crowbar]
  type virtual_flag_ = [%import: Asttypes.virtual_flag] [@@deriving crowbar]
  let loc_to_crowbar = l_to_crowbar
  let arg_label_to_crowbar = arg_label__to_crowbar
  let closed_flag_to_crowbar = closed_flag__to_crowbar
  let label_to_crowbar = label__to_crowbar
  let rec_flag_to_crowbar = rec_flag__to_crowbar
  let direction_flag_to_crowbar = direction_flag__to_crowbar
  let override_flag_to_crowbar = override_flag__to_crowbar
  let variance_to_crowbar = variance__to_crowbar
  let private_flag_to_crowbar = private_flag__to_crowbar
  let mutable_flag_to_crowbar = mutable_flag__to_crowbar
  let virtual_flag_to_crowbar = virtual_flag__to_crowbar
end

module Longident = struct
  include Longident
      (* if we make Lapply's, we can easily trigger a Misc.fatal_error from Longident.last, so don't do that *)
  let to_crowbar = Crowbar.(map [bytes] (fun l -> Lident l));
end

open Asttypes

type constant = [%import: Parsetree.constant]
(* constant has a number of constraints expressed in parsetree.mli *)
let constant_to_crowbar = Crowbar.(choose [
    map [int; option (choose [const 'n'; const 'l'; const 'L'])] (fun s n -> Parsetree.Pconst_integer (string_of_int s, n));
    map [uint8] (fun c -> Parsetree.Pconst_char (Char.chr c));
    map [bytes; option bytes] (fun s delim -> Parsetree.Pconst_string (s, delim));
    map [float; (* it seems no char will be accepted by the typechecker as the second argument of Pconst_float, so never make any *)
         const None] (fun f n -> Parsetree.Pconst_float (string_of_float f, n))
  ])

module Parsetree = struct
  include Ast_406.Parsetree
  (* failing to constrain this triggers an assertion failure in typing/typetexp.ml:284 *)
  (* the constraint isn't documented in parsetree.mli but it seems unsurprising *)
  let ptype_params_to_crowbar =
    let ptype_param_core_type_descs = Crowbar.(choose [
      const Ptyp_any;
      map [string] (fun i -> Ptyp_var i);
    ]) in
    Crowbar.(list @@ map [ptype_param_core_type_descs; variance_to_crowbar]
               (fun ct v -> (Ast_helper.Typ.mk ct), v))
end

type attribute = [%import: Parsetree.attribute]
and extension = [%import: Parsetree.extension]
and attributes = [%import: Parsetree.attributes] [@@generator Crowbar.const []]
and payload = [%import: Parsetree.payload]
and object_field = [%import: Parsetree.object_field]
and core_type = [%import: Parsetree.core_type]
and core_type_desc = [%import: Parsetree.core_type_desc] [@@generator
  Crowbar.(let ct = unlazy core_type_to_crowbar in
           choose [const Parsetree.Ptyp_any;
                   map [string] (fun i -> Ptyp_var i);
                   map [arg_label_to_crowbar; ct; ct] (fun a b c -> Ptyp_arrow (a, b, c));
                   (* failing to give the minimum number of elements to
                      Ptyp_tuple results in many assertion failures.
                      the invariant is documented in parsetree.mli:89 *)
                   map [ct; ct; list ct] (fun a b l -> Ptyp_tuple (a::b::l));
                   map [Longident.to_crowbar; list ct] (fun i l ->
                       Ptyp_constr (Location.mknoloc i, l));
                   map [list (unlazy object_field_to_crowbar); closed_flag_to_crowbar]
                       (fun l f -> Ptyp_object (l, f));
                   map [Longident.to_crowbar; list ct] (fun i l ->
                       Ptyp_class (Location.mknoloc i, l));
                   map [ct; string] (fun c i -> Ptyp_alias (c, i));
                   map [list (unlazy row_field_to_crowbar);
                        closed_flag_to_crowbar;
                        option (list label_to_crowbar)]
                     (fun rl c llo -> Ptyp_variant (rl, c, llo)); (* I bet the first one is really list1 *)
                   (* no Ptyp_poly, because it "can only appear in the following context" *)
                   map [(unlazy package_type_to_crowbar)] (fun p -> Ptyp_package p);
                   (* no point in making extensions, they'll be rejected by the typechecker *)
          ])] (* I'm going to hell for this *)
and package_type = [%import: Parsetree.package_type]
and row_field = [%import: Parsetree.row_field]
and pattern = [%import: Parsetree.pattern]
and pattern_desc = [%import: Parsetree.pattern_desc] [@@generator
  (* this is for the purpose of our tests, not required by type machinery *)
    Crowbar.(choose [
        map [bytes] (fun var_name -> Parsetree.Ppat_var (Location.mknoloc var_name));
        map [constant_to_crowbar] (fun c -> Parsetree.Ppat_constant c);
      ])]
and expression = [%import: Parsetree.expression]
and expression_desc = [%import: Parsetree.expression_desc] [@@generator Crowbar.(
    let exp = unlazy expression_to_crowbar in
    let lid_loc = map [Longident.to_crowbar] Location.mknoloc in
    choose [
      map [lid_loc] (fun l -> Pexp_ident l);
      map [constant_to_crowbar] (fun c -> Pexp_constant c);
      map [rec_flag_to_crowbar;
           list (unlazy value_binding_to_crowbar);
           exp] (fun r l e -> Pexp_let (r, l, e));
      map [list (unlazy case_to_crowbar)] (fun l -> Pexp_function l);
      (* Pexp_fun is special (see parsetree.mli:255) *)
      map [
        Crowbar.choose [
          (* if there is an expression, only Optional is valid, so the choices are
             really map an arbitrary arg_label to none, or
             Optional label, Some expression *)
          map [arg_label_to_crowbar] (fun l -> (l, None));
          map [string; exp] (fun i e -> (Optional i, Some e))
        ];
        unlazy pattern_to_crowbar; exp]
        (fun (a, b) c d -> Pexp_fun (a, b, c, d));
      map [exp;
           (* list1 documented as required in parsetree.mli:264 *)
           list1 (map [arg_label_to_crowbar; exp] (fun a b -> a, b))]
        (fun e l -> Pexp_apply (e, l));
      map [exp; list (unlazy case_to_crowbar)] (fun e l ->
          Pexp_match (e, l));
      map [exp; list (unlazy case_to_crowbar)] (fun e l ->
          Pexp_try (e, l));
      (* n must be at least 2 from parsetree.mli:273 *)
      map [exp; exp; list exp] (fun a b c -> Pexp_tuple (a::b::c));
      map [lid_loc; option exp] (fun i e -> Pexp_construct (i, e));
      map [label_to_crowbar; option exp]
        (fun l e -> Pexp_variant (l, e));
      map [list1 (map [lid_loc; exp] (fun l e -> l, e)); option exp]
        (fun l e -> Pexp_record (l, e));
      map [exp; lid_loc] (fun e l -> Pexp_field (e, l));
      map [exp; lid_loc; exp] (fun e1 l e2 -> Pexp_setfield (e1, l, e2));
      map [list exp] (fun l -> Pexp_array l);
      map [exp; exp; option exp] (fun i t e -> Pexp_ifthenelse (i, t, e));
      map [exp; exp] (fun e1 e2 -> Pexp_sequence (e1, e2));
      map [exp; exp] (fun e1 e2 -> Pexp_while (e1, e2));
      map [(unlazy pattern_to_crowbar); exp; exp; direction_flag_to_crowbar; exp]
        (fun p e1 e2 d e3 -> Pexp_for (p, e1, e2, d, e3));
      map [exp; unlazy core_type_to_crowbar] (fun e c -> Pexp_constraint (e, c));
      map [exp; option (unlazy core_type_to_crowbar); unlazy core_type_to_crowbar]
        (fun e oc c -> Pexp_coerce (e, oc, c));
      map [exp; string] (fun e s -> Pexp_send (e, Location.mknoloc s));
      map [lid_loc] (fun l -> Pexp_new l);
      map [string; exp] (fun i e -> Pexp_setinstvar ((Location.mknoloc i), e));
      map [list (map [string; exp] (fun i e -> (Location.mknoloc i, e)))] (fun l -> Pexp_override l);
      (* map [string; (unlazy module_expr_to_crowbar); exp] (fun s m e -> Pexp_letmodule (Location.mknoloc s, m, e)); *) (* don't mess around in the module language *)
      map [unlazy extension_constructor_to_crowbar; exp] (fun c e -> Pexp_letexception (c, e));
      map [exp] (fun e -> Pexp_assert e);
      map [exp] (fun e -> Pexp_lazy e);
      map [exp; option (unlazy core_type_to_crowbar)] (fun e c -> Pexp_poly (e, c)); (* parsetree.mli: Pexp_poly can only be used as the expression under Cfk_concrete for methods, so we'd expect this to cause some trouble *)
      map [unlazy class_structure_to_crowbar] (fun c -> Pexp_object c);
      map [string; exp] (fun s e -> Pexp_newtype (Location.mknoloc s, e));
      (* map [unlazy module_expr_to_crowbar] (fun m -> Pexp_pack m); *) (* don't get lost in module language *)
      (* Pexp_open would go here *)
      (* skip Pexp_extension *)
      (* and Pexp_unreachable :) *)
    ]
  )]
and case = [%import: Parsetree.case]
and value_description = [%import: Parsetree.value_description]
and type_declaration = [%import: Parsetree.type_declaration] [@@generator
  Crowbar.(let ct = unlazy core_type_to_crowbar in
           map [string;
                Parsetree.ptype_params_to_crowbar;
                list (map [ct; ct; Location.to_crowbar] (fun t1 t2 l -> (t1, t2, l)));
                unlazy type_kind_to_crowbar;
                private_flag_to_crowbar;
                option ct;
                const [];
                Location.to_crowbar;]
             (fun name ptype_params ptype_cstrs ptype_kind ptype_private
               ptype_manifest ptype_attributes ptype_loc ->
               let ptype_name = Location.mknoloc name in
               Parsetree.{ptype_name; ptype_params; ptype_cstrs; ptype_kind; ptype_private
                  ; ptype_manifest; ptype_attributes; ptype_loc })
  )]
and type_kind = [%import: Parsetree.type_kind] [@@generator
   (* need a custom generator to respect invariants documented in parsetree.mli:406 and 408 *)
  Crowbar.(choose [
      const Ptype_abstract;
      map [list1 (unlazy constructor_declaration_to_crowbar)] (fun l -> Ptype_variant l);
      map [list1 (unlazy label_declaration_to_crowbar)] (fun l -> Ptype_record l);
      const Ptype_open;
    ])]
and label_declaration = [%import: Parsetree.label_declaration]
and constructor_declaration = [%import: Parsetree.constructor_declaration]
and constructor_arguments = [%import: Parsetree.constructor_arguments] [@@generator
   (* typing/typedecl.transl_labels asserts that label declarations are not the empty list,
      so this custom generator is needed for list1 *)
  Crowbar.(choose [
      map [list (unlazy core_type_to_crowbar)] (fun l -> Pcstr_tuple l);
      map [list1 (unlazy label_declaration_to_crowbar)] (fun l -> Pcstr_record l);
    ])]
and type_extension = [%import: Parsetree.type_extension]
and extension_constructor = [%import: Parsetree.extension_constructor]
and extension_constructor_kind = [%import: Parsetree.extension_constructor_kind]
and class_type = [%import: Parsetree.class_type]
and class_type_desc = [%import: Parsetree.class_type_desc]
and class_signature = [%import: Parsetree.class_signature]
and class_type_field = [%import: Parsetree.class_type_field]
and class_type_field_desc = [%import: Parsetree.class_type_field_desc]
and 'a class_infos = [%import: 'a Parsetree.class_infos]
and class_description = [%import: Parsetree.class_description]
and class_type_declaration = [%import: Parsetree.class_type_declaration]
and class_expr = [%import: Parsetree.class_expr]
and class_expr_desc = [%import: Parsetree.class_expr_desc]
and class_structure = [%import: Parsetree.class_structure]
and class_field = [%import: Parsetree.class_field]
and class_field_desc = [%import: Parsetree.class_field_desc]
and class_field_kind = [%import: Parsetree.class_field_kind]
and class_declaration = [%import: Parsetree.class_declaration]
and module_type = [%import: Parsetree.module_type]
and module_type_desc = [%import: Parsetree.module_type_desc]
and signature = [%import: Parsetree.signature]
and signature_item = [%import: Parsetree.signature_item]
and signature_item_desc = [%import: Parsetree.signature_item_desc] [@@generator
   (* custom generator needed because parsing/pprintast.ml has an assert false triggered for Psig_type (_, []) *)
  Crowbar.(choose [
      map [unlazy value_description_to_crowbar] (fun d -> Psig_value d);
      map [rec_flag_to_crowbar; list1 @@ unlazy type_declaration_to_crowbar] (fun r l -> Psig_type (r, l));
      map [unlazy type_extension_to_crowbar] (fun e -> Psig_typext e);
      map [unlazy extension_constructor_to_crowbar] (fun e -> Psig_exception e);
      (* skip Psig_module *)
      (* skip Psig_recmodule *)
      (* skip Psig_modtype *)
      map [unlazy open_description_to_crowbar] (fun d -> Psig_open d);
      map [unlazy include_description_to_crowbar] (fun d -> Psig_include d);
      (* might want to cut the class stuff too *)
      map [list @@ unlazy class_description_to_crowbar] (fun l -> Psig_class l);
      map [list @@ unlazy class_type_declaration_to_crowbar] (fun l -> Psig_class_type l);
      (* no attributes *)
      (* no extensions *)
    ])]
and module_declaration = [%import: Parsetree.module_declaration]
and module_type_declaration = [%import: Parsetree.module_type_declaration]
and open_description = [%import: Parsetree.open_description]
and 'a include_infos = [%import: 'a Parsetree.include_infos]
and include_description = [%import: Parsetree.include_description]
and include_declaration = [%import: Parsetree.include_declaration]
and with_constraint = [%import: Parsetree.with_constraint]
and module_expr = [%import: Parsetree.module_expr]
and module_expr_desc = [%import: Parsetree.module_expr_desc]
and structure = [%import: Parsetree.structure]
and structure_item = [%import: Parsetree.structure_item]
and structure_item_desc = [%import: Parsetree.structure_item_desc] [@@generator
   (* custom generator needed because parsing/pprintast.ml:1216 has an assert false for Pstr_type (_, []) *)
  Crowbar.(choose [
      map [unlazy expression_to_crowbar; const []] (fun e a -> Pstr_eval (e, a));
      map [rec_flag_to_crowbar; list (unlazy value_binding_to_crowbar)] (fun f l -> Pstr_value (f, l));
      map [unlazy value_description_to_crowbar] (fun d -> Pstr_primitive d);
      map [rec_flag_to_crowbar; list1 (unlazy type_declaration_to_crowbar)] (fun f l -> Pstr_type (f, l));
      map [unlazy type_extension_to_crowbar] (fun e -> Pstr_typext e);
      map [unlazy extension_constructor_to_crowbar] (fun e -> Pstr_exception e);
      (* might want to cut the module stuff *)
      (* indeed, do cut them, because we trigger parsing/pprint.ast.ml:1325 with them *) (*
      map [unlazy module_binding_to_crowbar] (fun b -> Pstr_module b);
      map [list @@ unlazy module_binding_to_crowbar] (fun b -> Pstr_recmodule b); (* this list probably needs to be nonempty, but that's not documented so let's see how it does *)
      map [unlazy module_type_declaration_to_crowbar] (fun d -> Pstr_modtype d); *)
      map [unlazy open_description_to_crowbar] (fun d -> Pstr_open d);
      (* might want to cut the class stuff too *)
      map [list @@ unlazy class_declaration_to_crowbar] (fun l -> Pstr_class l);
      map [list @@ unlazy class_type_declaration_to_crowbar] (fun l -> Pstr_class_type l);
      map [unlazy include_declaration_to_crowbar] (fun d -> Pstr_include d);
      (* don't bother with attributes *)
      (* also don't bother with extensions *)
    ]
   )]
and value_binding = [%import: Parsetree.value_binding]
and module_binding = [%import: Parsetree.module_binding]
[@@deriving crowbar]
