open Asttypes
type attribute = string loc * payload
and extension = string loc * payload
and attributes = attribute list
and payload =
and core_type =
and core_type_desc =
  | Ptyp_any
  | Ptyp_var of string
  | Ptyp_arrow of label * core_type * core_type
  | Ptyp_tuple of core_type list
  | Ptyp_constr of Longident.t loc * core_type list
  | Ptyp_object of (string * attributes * core_type) list * closed_flag
  | Ptyp_class of Longident.t loc * core_type list
  | Ptyp_alias of core_type * string
  | Ptyp_variant of row_field list * closed_flag * label list option
  | Ptyp_poly of string list * core_type
  | Ptyp_package of package_type
  | Ptyp_extension of extension
and package_type = Longident.t loc * (Longident.t loc * core_type) list
and row_field =
  | Rtag of label * attributes * bool * core_type list
  | Rinherit of core_type
and pattern =
    {
     ppat_desc: pattern_desc;
     ppat_loc: Location.t;
     ppat_attributes: attributes; 
    }
and pattern_desc =
  | Ppat_any
  | Ppat_var of string loc
  | Ppat_alias of pattern * string loc
  | Ppat_constant of constant
  | Ppat_interval of constant * constant
  | Ppat_tuple of pattern list
  | Ppat_construct of Longident.t loc * pattern option
  | Ppat_variant of label * pattern option
  | Ppat_record of (Longident.t loc * pattern) list * closed_flag
  | Ppat_array of pattern list
  | Ppat_or of pattern * pattern
  | Ppat_constraint of pattern * core_type
  | Ppat_type of Longident.t loc
  | Ppat_lazy of pattern
  | Ppat_unpack of string loc
  | Ppat_exception of pattern
  | Ppat_extension of extension
and expression =
    {
     pexp_desc: expression_desc;
     pexp_loc: Location.t;
     pexp_attributes: attributes; 
    }
and expression_desc =
  | Pexp_ident of Longident.t loc
  | Pexp_constant of constant
  | Pexp_let of rec_flag * value_binding list * expression
  | Pexp_function of case list
  | Pexp_fun of label * expression option * pattern * expression
  | Pexp_apply of expression * (label * expression) list
  | Pexp_match of expression * case list
  | Pexp_try of expression * case list
  | Pexp_tuple of expression list
  | Pexp_construct of Longident.t loc * expression option
  | Pexp_variant of label * expression option
  | Pexp_record of (Longident.t loc * expression) list * expression option
  | Pexp_field of expression * Longident.t loc
  | Pexp_setfield of expression * Longident.t loc * expression
  | Pexp_array of expression list
  | Pexp_ifthenelse of expression * expression * expression option
  | Pexp_sequence of expression * expression
  | Pexp_while of expression * expression
  | Pexp_for of
      pattern *  expression * expression * direction_flag * expression
        (* for i = E1 to E2 do E3 done      (flag = Upto)
           for i = E1 downto E2 do E3 done  (flag = Downto)
         *)
  | Pexp_constraint of expression * core_type
  | Pexp_coerce of expression * core_type option * core_type
        (* (E :> T)        (None, T)
           (E : T0 :> T)   (Some T0, T)
         *)
  | Pexp_send of expression * string
  | Pexp_new of Longident.t loc
  | Pexp_setinstvar of string loc * expression
  | Pexp_override of (string loc * expression) list
  | Pexp_letmodule of string loc * module_expr * expression
  | Pexp_assert of expression
        (* assert E
           Note: "assert false" is treated in a special way by the
           type-checker. *)
  | Pexp_lazy of expression
  | Pexp_poly of expression * core_type option
        (* Used for method bodies.
           Can only be used as the expression under Cfk_concrete
           for methods (not values). *)
  | Pexp_object of class_structure
  | Pexp_newtype of string * expression
  | Pexp_pack of module_expr
        (* (module ME)
           (module ME : S) is represented as
           Pexp_constraint(Pexp_pack, Ptyp_package S) *)
  | Pexp_open of override_flag * Longident.t loc * expression
        (* let open M in E
           let! open M in E
        *)
  | Pexp_extension of extension
and case =   
    {
     pc_lhs: pattern;
     pc_guard: expression option;
     pc_rhs: expression;
    }
and value_description =
    {
     pval_name: string loc;
     pval_type: core_type;
     pval_prim: string list;
     pval_attributes: attributes;  
     pval_loc: Location.t;
    }
(*
  val x: T                            (prim = [])
  external x: T = "s1" ... "sn"       (prim = ["s1";..."sn"])
  Note: when used under Pstr_primitive, prim cannot be empty
*)
and type_declaration =
    {
     ptype_name: string loc;
     ptype_params: (core_type * variance) list;
     ptype_cstrs: (core_type * core_type * Location.t) list;
     ptype_kind: type_kind;
     ptype_private: private_flag;   
     ptype_manifest: core_type option;  
     ptype_attributes: attributes;   
     ptype_loc: Location.t;
    }
(*
  type t                     (abstract, no manifest)
  type t = T0                (abstract, manifest=T0)
  type t = C of T | ...      (variant,  no manifest)
  type t = T0 = C of T | ... (variant,  manifest=T0)
  type t = {l: T; ...}       (record,   no manifest)
  type t = T0 = {l : T; ...} (record,   manifest=T0)
  type t = ..                (open,     no manifest)
*)
and type_kind =
  | Ptype_abstract
  | Ptype_variant of constructor_declaration list
  | Ptype_record of label_declaration list
  | Ptype_open
and label_declaration =
    {
     pld_name: string loc;
     pld_mutable: mutable_flag;
     pld_type: core_type;
     pld_loc: Location.t;
     pld_attributes: attributes; 
    }
(*  { ...; l: T; ... }            (mutable=Immutable)
    { ...; mutable l: T; ... }    (mutable=Mutable)
    Note: T can be a Ptyp_poly.
*)
and constructor_declaration =
    {
     pcd_name: string loc;
     pcd_args: core_type list;
     pcd_res: core_type option;
     pcd_loc: Location.t;
     pcd_attributes: attributes; 
    }
(*
  | C of T1 * ... * Tn     (res = None)
  | C: T0                  (args = [], res = Some T0)
  | C: T1 * ... * Tn -> T0 (res = Some T0)
*)
and type_extension =
    {
     ptyext_path: Longident.t loc;
     ptyext_params: (core_type * variance) list;
     ptyext_constructors: extension_constructor list;
     ptyext_private: private_flag;
     ptyext_attributes: attributes;   
    }
(*
  type t += ...
*)
and extension_constructor =
    {
     pext_name: string loc;
     pext_kind : extension_constructor_kind;
     pext_loc : Location.t;
     pext_attributes: attributes; 
    }
and extension_constructor_kind =
    Pext_decl of core_type list * core_type option
      (*
         | C of T1 * ... * Tn     ([T1; ...; Tn], None)
         | C: T0                  ([], Some T0)
         | C: T1 * ... * Tn -> T0 ([T1; ...; Tn], Some T0)
       *)
  | Pext_rebind of Longident.t loc
      (*
         | C = D
       *)
and class_type =
    {
     pcty_desc: class_type_desc;
     pcty_loc: Location.t;
     pcty_attributes: attributes; 
    }
and class_type_desc =
  | Pcty_constr of Longident.t loc * core_type list
        (* c
           ['a1, ..., 'an] c *)
  | Pcty_signature of class_signature
  | Pcty_arrow of label * core_type * class_type
        (* T -> CT       (label = "")
           ~l:T -> CT    (label = "l")
           ?l:T -> CT    (label = "?l")
         *)
  | Pcty_extension of extension
and class_signature =
    {
     pcsig_self: core_type;
     pcsig_fields: class_type_field list;
    }
(* object('selfpat) ... end
   object ... end             (self = Ptyp_any)
 *)
and class_type_field =
    {
     pctf_desc: class_type_field_desc;
     pctf_loc: Location.t;
     pctf_attributes: attributes; 
    }
and class_type_field_desc =
  | Pctf_inherit of class_type
  | Pctf_val of (string * mutable_flag * virtual_flag * core_type)
  | Pctf_method  of (string * private_flag * virtual_flag * core_type)
        (* method x: T
           Note: T can be a Ptyp_poly.
         *)
  | Pctf_constraint  of (core_type * core_type)
  | Pctf_attribute of attribute
  | Pctf_extension of extension
and 'a class_infos =
    {
     pci_virt: virtual_flag;
     pci_params: (core_type * variance) list;
     pci_name: string loc;
     pci_expr: 'a;
     pci_loc: Location.t;
     pci_attributes: attributes;  
    }
(* class c = ...
   class ['a1,...,'an] c = ...
   class virtual c = ...
   Also used for "class type" declaration.
*)
and class_description = class_type class_infos
and class_type_declaration = class_type class_infos
and class_expr =
    {
     pcl_desc: class_expr_desc;
     pcl_loc: Location.t;
     pcl_attributes: attributes; 
    }
and class_expr_desc =
  | Pcl_constr of Longident.t loc * core_type list
  | Pcl_structure of class_structure
  | Pcl_fun of label * expression option * pattern * class_expr
  | Pcl_apply of class_expr * (label * expression) list
  | Pcl_let of rec_flag * value_binding list * class_expr
        (* let P1 = E1 and ... and Pn = EN in CE      (flag = Nonrecursive)
           let rec P1 = E1 and ... and Pn = EN in CE  (flag = Recursive)
         *)
  | Pcl_constraint of class_expr * class_type
  | Pcl_extension of extension
and class_structure =
    {
     pcstr_self: pattern;
     pcstr_fields: class_field list;
    }
(* object(selfpat) ... end
   object ... end           (self = Ppat_any)
 *)
and class_field =
    {
     pcf_desc: class_field_desc;
     pcf_loc: Location.t;
     pcf_attributes: attributes; 
    }
and class_field_desc =
  | Pcf_inherit of override_flag * class_expr * string option
        (* inherit CE
           inherit CE as x
           inherit! CE
           inherit! CE as x
         *)
  | Pcf_val of (string loc * mutable_flag * class_field_kind)
        (* val x = E
           val virtual x: T
         *)
  | Pcf_method of (string loc * private_flag * class_field_kind)
  | Pcf_constraint of (core_type * core_type)
  | Pcf_initializer of expression
  | Pcf_attribute of attribute
  | Pcf_extension of extension
and class_field_kind =
  | Cfk_virtual of core_type
  | Cfk_concrete of override_flag * expression
and class_declaration = class_expr class_infos
and module_type =
    {
     pmty_desc: module_type_desc;
     pmty_loc: Location.t;
     pmty_attributes: attributes; 
    }
and module_type_desc =
  | Pmty_ident of Longident.t loc
  | Pmty_signature of signature
  | Pmty_functor of string loc * module_type option * module_type
  | Pmty_with of module_type * with_constraint list
  | Pmty_typeof of module_expr
  | Pmty_extension of extension
  | Pmty_alias of Longident.t loc
and signature = signature_item list
and signature_item =
    {
     psig_desc: signature_item_desc;
     psig_loc: Location.t;
    }
and signature_item_desc =
  | Psig_value of value_description
        (*
          val x: T
          external x: T = "s1" ... "sn"
         *)
  | Psig_type of type_declaration list
  | Psig_typext of type_extension
  | Psig_exception of extension_constructor
  | Psig_module of module_declaration
  | Psig_recmodule of module_declaration list
  | Psig_modtype of module_type_declaration
        (* module type S = MT
           module type S *)
  | Psig_open of open_description
  | Psig_include of include_description
  | Psig_class of class_description list
  | Psig_class_type of class_type_declaration list
  | Psig_attribute of attribute
  | Psig_extension of extension * attributes
and module_declaration =
    {
     pmd_name: string loc;
     pmd_type: module_type;
     pmd_attributes: attributes; 
     pmd_loc: Location.t;
    }
and module_type_declaration =
    {
     pmtd_name: string loc;
     pmtd_type: module_type option;
     pmtd_attributes: attributes; 
     pmtd_loc: Location.t;
    }
(* S = MT
   S       (abstract module type declaration, pmtd_type = None)
*)
and open_description =
    {
     popen_lid: Longident.t loc;
     popen_override: override_flag;
     popen_loc: Location.t;
     popen_attributes: attributes;
    }
(* open! X - popen_override = Override (silences the 'used identifier
                              shadowing' warning)
   open  X - popen_override = Fresh
 *)
and 'a include_infos =
    {
     pincl_mod: 'a;
     pincl_loc: Location.t;
     pincl_attributes: attributes;
    }
and include_description = module_type include_infos
and include_declaration = module_expr include_infos
and with_constraint =
  | Pwith_type of Longident.t loc * type_declaration
        (* with type X.t = ...
           Note: the last component of the longident must match
           the name of the type_declaration. *)
  | Pwith_module of Longident.t loc * Longident.t loc
  | Pwith_typesubst of type_declaration
  | Pwith_modsubst of string loc * Longident.t loc
and module_expr =
    {
     pmod_desc: module_expr_desc;
     pmod_loc: Location.t;
     pmod_attributes: attributes; 
    }
and module_expr_desc =
  | Pmod_ident of Longident.t loc
  | Pmod_structure of structure
  | Pmod_functor of string loc * module_type option * module_expr
  | Pmod_apply of module_expr * module_expr
  | Pmod_constraint of module_expr * module_type
  | Pmod_unpack of expression
  | Pmod_extension of extension
and structure = structure_item list
and structure_item =
    {
     pstr_desc: structure_item_desc;
     pstr_loc: Location.t;
    }
and structure_item_desc =
  | Pstr_eval of expression * attributes
  | Pstr_value of rec_flag * value_binding list
        (* let P1 = E1 and ... and Pn = EN       (flag = Nonrecursive)
           let rec P1 = E1 and ... and Pn = EN   (flag = Recursive)
         *)
  | Pstr_primitive of value_description
  | Pstr_type of type_declaration list
  | Pstr_typext of type_extension
  | Pstr_exception of extension_constructor
        (* exception C of T
           exception C = M.X *)
  | Pstr_module of module_binding
  | Pstr_recmodule of module_binding list
  | Pstr_modtype of module_type_declaration
  | Pstr_open of open_description
  | Pstr_class of class_declaration list
  | Pstr_class_type of class_type_declaration list
  | Pstr_include of include_declaration
  | Pstr_attribute of attribute
  | Pstr_extension of extension * attributes
and value_binding =
  {
    pvb_pat: pattern;
    pvb_expr: expression;
    pvb_attributes: attributes;
    pvb_loc: Location.t;
  }
and module_binding =
    {
     pmb_name: string loc;
     pmb_expr: module_expr;
     pmb_attributes: attributes;
     pmb_loc: Location.t;
    }
type toplevel_phrase =
  | Ptop_def of structure
  | Ptop_dir of string * directive_argument
and directive_argument =
  | Pdir_none
  | Pdir_string of string
  | Pdir_int of int
  | Pdir_ident of Longident.t
  | Pdir_bool of bool
