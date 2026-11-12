From Cats Require Export
  Cat.Monoidal.Binoidal
  Cat.Premonoidal.Laws.

Local Open Scope monoidal_scope.

(** * Monoidal Categories as Premonoidal Categories

    Reuse the original unit, structure maps and their inverses. Separate
    naturality is a special case of the existing joint naturality.
    This adapter is explicit while the monoidal hierarchy is migrated. *)

(** * 幺半范畴作为预幺半范畴

    复用原单位对象、结构映射及其逆。分别自然性是已有联合自然性的特例。
    在幺半层级迁移期间，此适配器保持显式。 *)

Section Monoidal.
Context {C : Cat} `{MC : !MonoidalCat C}.

(** No tensor action or structural inverse is selected a second time. *)

(** 不再次选取张量作用或结构同构的逆。 *)

Program Definition MonoidalPremonoidal
  : PremonoidalCat C
  :=
  {|PremonoidalB := MonoidalBinoidal
  ; PremonoidalUnit := I⊗[MC]
  ; premonoidal_associator X Y Z :=
      (α⊗[X; Y; Z]; tensor_assoc_iso X Y Z)
  ; premonoidal_left_unitor X := (λ⊗[X]; tensor_unit_l_iso X)
  ; premonoidal_right_unitor X := (ρ⊗[X]; tensor_unit_r_iso X)
  ; premonoidal_assoc_central X Y Z := monoidal_arrow_central _
  ; premonoidal_unit_l_central X := monoidal_arrow_central _
  ; premonoidal_unit_r_central X := monoidal_arrow_central _
  ; premonoidal_unit_l_natural X Y f := tensor_unit_l_natural f
  ; premonoidal_unit_r_natural X Y f := tensor_unit_r_natural f
  ; premonoidal_pentagon W X Y Z := monoidal_pentagon W X Y Z
  ; premonoidal_triangle X Y := monoidal_triangle X Y
  |}.
Next Obligation.
  pose proof (tensor_assoc_natural f (@id Y) (@id Z)) as H.
  rewrite tensor_map_id in H. exact H.
Defined.
Next Obligation.
  exact (tensor_assoc_natural (@id X) g (@id Z)).
Defined.
Next Obligation.
  pose proof (tensor_assoc_natural (@id X) (@id Y) h) as H.
  rewrite tensor_map_id in H. exact H.
Defined.

End Monoidal.
