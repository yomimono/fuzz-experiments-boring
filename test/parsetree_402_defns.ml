type attribute = string loc * payload
and extension = string loc * payload
and attributes = attribute list
and payload =
and core_type =
and core_type_desc =
and package_type = Longident.t loc * (Longident.t loc * core_type) list
and row_field =
and pattern =
and pattern_desc =
and expression =
and expression_desc =
and case =   
and value_description =
and type_declaration =
and type_kind =
and label_declaration =
and constructor_declaration =
and type_extension =
and extension_constructor =
and extension_constructor_kind =
and class_type =
and class_type_desc =
and class_signature =
and class_type_field =
and class_type_field_desc =
and 'a class_infos =
and class_description = class_type class_infos
and class_type_declaration = class_type class_infos
and class_expr =
and class_expr_desc =
and class_structure =
and class_field =
and class_field_desc =
and class_field_kind =
and class_declaration = class_expr class_infos
and module_type =
and module_type_desc =
and signature = signature_item list
and signature_item =
and signature_item_desc =
and module_declaration =
and module_type_declaration =
and open_description =
and 'a include_infos =
and include_description = module_type include_infos
and include_declaration = module_expr include_infos
and with_constraint =
and module_expr =
and module_expr_desc =
and structure = structure_item list
and structure_item =
and structure_item_desc =
and value_binding =
and module_binding =
type toplevel_phrase =
and directive_argument =