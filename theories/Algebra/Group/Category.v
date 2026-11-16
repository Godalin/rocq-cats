From Cats Require Export
  Algebra.Group.Core
  Algebra.Monoid.Category
  Cat.Groupoid.Core.

Local Open Scope monoid_scope.

(** * Groups as Single-Object Groupoids

    Reuse the monoid category, selecting inverses as arrow inverses.
    Enable the resulting groupoid structure explicitly. *)

(** * 群的单对象群胚解释

    复用幺半群范畴，以群逆作为箭头的逆，所得群胚结构须显式启用。 *)

Program Definition MonoidCat_IsGroupoid (G : Group)
  : B(G) ⦂ Gpd
  :=
  {|groupoid_iso X Y g :=
      (g⁻¹; (@mul_inv_l _ _ (@isGroup _ (hasGroup G)) g,
              @mul_inv_r _ _ (@isGroup _ (hasGroup G)) g))
  |}.

(** Bundle the original one-object category and its inverses.
    This keeps the specified setoid equality and stores no second operation. *)

(** 将原单对象范畴与其群逆打包，保留指定广集相等，不另存运算。 *)

Definition GroupGpd (G : Group)
  : Gpd
  := GpdFromProperty B(G) (MonoidCat_IsGroupoid G).

(** Endomorphisms at any specified object of a groupoid form a group.
    This construction requires no equality of object representatives. *)

(** 群胚任意指定对象处的自态射构成群，不要求对象代表之间原生相等。 *)

Program Definition EndHasGroup (C : Cat) `{HC : !IsGroupoid C}
    (X : @Ob C)
  : HasGroup (EndMonoid C X)
  :=
  {|inv f := @groupoid_inv C HC X X f
  ; isGroup :=
      {|mul_inv_l := @groupoid_inv_l C HC X X
      ; mul_inv_r := @groupoid_inv_r C HC X X
      |}
  |}.

(** The existing endomorphism group reads this exact monoid and extension. *)

(** 现有自态射群读取恰好该幺半群及扩充。 *)

Definition EndGroup (C : Cat) `{HC : !IsGroupoid C} (X : @Ob C)
  : Group
  := GroupFromExtension (EndMonoid C X) (EndHasGroup C X).
