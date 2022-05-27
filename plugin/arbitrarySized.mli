val replace : 'a -> 'a -> 'a list -> 'a list
val arbitrarySized_body :
  GenericLib.ty_ctr ->
  GenericLib.ctr_rep list -> GenericLib.var list -> GenericLib.coq_expr
val arbitrarySized_decl :
  GenericLib.ty_ctr ->
  GenericLib.ctr_rep list -> GenericLib.var list -> GenericLib.coq_expr
val shrink_decl :
  GenericLib.ty_ctr ->
  (GenericLib.constructor * GenericLib.coq_type) list ->
  GenericLib.var list -> bool -> GenericLib.coq_expr
val show_decl :
  GenericLib.ty_ctr -> GenericLib.ctr_rep list -> 'a -> bool -> GenericLib.coq_expr
