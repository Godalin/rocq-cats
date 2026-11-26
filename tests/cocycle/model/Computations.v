From Cats Require Import
  Instance.Bool.CocycleModel
  Instance.Set.Simplicial.Horn.

(** * Computing with the Boolean Model

    Inspect the retained triangle label, face restrictions and repeated
    positions. These checks exercise the actual simplicial functor rather
    than only the earlier standalone cocycle. *)

Fail Definition unchosen_boolean_monoid
  : @HasUnit BoolS_Semigroup (Semigroup_hasMagma BoolS_Semigroup)
  := ltac:(typeclasses eauto).

(** A simplicial model alone does not implicitly select Kan fillers. *)

Fail Definition unchosen_boolean_cocycle_fillers
  : HasKanFillers BoolCocycleModel
  := ltac:(typeclasses eauto).

(** The increasing triangle retains its actual Boolean coefficient. *)

Example triangle_label_computes
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) bool_cocycle_triangle = true.
Proof. reflexivity. Qed.

Example unit_label_computes
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid)) bool_cocycle_unit_triangle = false.
Proof. reflexivity. Qed.

Example identity_restriction_computes
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
      (BoolCocycleModel[(@Cat.Core.id Δ 2)]Δ bool_cocycle_triangle) = true.
Proof. reflexivity. Qed.

(** Each of the three actual faces has the unit triangle label on its
    repeated-position test triangle in degree one. *)

Example face_labels_compute (i : Fin@{Set} 3)
  : (lower (d[BoolCocycleModel; 1; i] bool_cocycle_triangle))⟦
      @Cat.Core.id [Ord 1] fin_first, ordinal_step fin_first⟧₂ = false.
Proof. destruct i as [[] | [[] | [[] | []]]]; reflexivity. Qed.

Example degenerate_triangle_labels_compute (i : Fin@{Set} 2)
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
      (s[BoolCocycleModel; 1; i] (two_cocycle_simplex_unit (M := BoolS_Monoid) 1)) = false.
Proof. destruct i as [[] | [[] | []]]; reflexivity. Qed.

(** Selection after repetition reads positions 0,0,2, so it is normalized. *)

Example collapsed_operator_computes
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
      (BoolCocycleModel[δ[1; fin_next fin_first] ∘ σ[1; fin_first]]Δ
        bool_cocycle_triangle) = false.
Proof. reflexivity. Qed.
