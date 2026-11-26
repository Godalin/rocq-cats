From Cats Require Import
  Algebra.Group.Cocycle
  Instance.Bool.CocycleKan.

Local Open Scope ordinal_scope.

(** * Computing Chosen Horn Fillers

    Imports retain explicit selection of coefficient and Kan structures.
    After enabling them locally, inspect actual selected simplices in all
    five branches of the construction. *)

Fail Definition unchosen_boolean_group
  : @HasInverse BoolS_Monoid (Monoid_hasMagma BoolS_Monoid) (hasUnit BoolS_Monoid)
  := _.

Fail Definition unchosen_boolean_commutativity
  : IsCommMagma BoolS_Monoid
  := _.

Fail Definition unchosen_boolean_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Local Existing Instance BoolCocycleModel_HasKanFillers.

(** Fill the actual restriction of a supplied simplex. The theorem does
    not promise to recover that simplex in the nonunique second dimension. *)

Definition bool_chosen_filler {n : nat} (i : Ordinal (S n))
    (x : BoolCocycleModel (S n))
  : BoolCocycleModel (S n)
  := (horn_fill (x↾Λ[BoolCocycleModel; S n; i])).1.

(** The one-dimensional branch selects the unit edge. *)

Example one_horn_computes (i : Ordinal 1)
  : (lower (bool_chosen_filler i (two_cocycle_simplex_unit (M := BoolS_Monoid) 1)))⟦
      ordinal_step fin_first,
      (@Cat.Core.id [Ord 1] (fin_next fin_first))⟧₂ = false.
Proof. reflexivity. Defined.

(** A two-horn sees only edges, so its selected triangle can have a
    different label from the original triangle. *)

Example two_horn_computes (i : Ordinal 2)
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
      (bool_chosen_filler i bool_cocycle_triangle) = false.
Proof. reflexivity. Defined.

(** A nonconstant coefficient table exercises all four missing faces. *)

Definition bool_tetrahedron
  : BoolCocycleModel 3
  :=
  {|lower := (TetrahedronTwoCocycle (M := BoolS_Monoid)) false true true false eq_refl
  |}.

(** Every three-horn completion computes all four original coefficients,
    including the missing face rather than only retained faces. *)

Example three_horns_compute (i : Ordinal 3)
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid)
        (d[BoolCocycleModel; 2; fin_first]
          (bool_chosen_filler i bool_tetrahedron)),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
        (d[BoolCocycleModel; 2; fin_first⁺]
          (bool_chosen_filler i bool_tetrahedron)),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
        (d[BoolCocycleModel; 2; fin_first⁺⁺]
          (bool_chosen_filler i bool_tetrahedron)),
      (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
        (d[BoolCocycleModel; 2; fin_first⁺⁺⁺]
          (bool_chosen_filler i bool_tetrahedron))) =
      (true, true, false, false).
Proof. destruct i as [[] | [[] | [[] | [[] | []]]]]; reflexivity. Defined.

(** A normalized table with three nonunit triangles exercises the critical
    fourth-dimensional branch. All five equations compute by xor. *)

Definition bool_four_simplex
  : BoolCocycleModel 4
  :=
  {|lower := (PentachoronTwoCocycle (M := BoolS_Monoid)) true false false true true
      false false false false false
      eq_refl eq_refl eq_refl eq_refl eq_refl
  |}.

(** Even when its containing tetrahedron is omitted, triangle 012 is
    retained and its coefficient computes to the original value. *)

Example four_horns_compute (i : Ordinal 4)
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
      (BoolCocycleModel[δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺⁺]]Δ
        (bool_chosen_filler i bool_four_simplex)) = true.
Proof.
  destruct i as [[] | [[] | [[] | [[] | [[] | []]]]]]; reflexivity.
Defined.

(** Every five-horn branch reconstructs the unit table from its actual
    restrictions. Both outer indices and every inner index are checked. *)

Example five_horns_compute (i : Ordinal 5)
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
      (BoolCocycleModel[δ[4; fin_first⁺⁺⁺⁺⁺] ∘F
        δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺⁺]]Δ
        (bool_chosen_filler i (two_cocycle_simplex_unit (M := BoolS_Monoid) 5))) = false.
Proof.
  destruct i as [[] | [[] | [[] | [[] | [[] | [[] | []]]]]]]; reflexivity.
Defined.

(** A larger stable dimension follows the recursive family rather than a
    finite list of hard-coded dimensions. *)

Example six_horn_computes
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
      (BoolCocycleModel[δ[5; fin_first⁺⁺⁺⁺⁺⁺] ∘F δ[4; fin_first⁺⁺⁺⁺⁺] ∘F
        δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺⁺]]Δ
        (bool_chosen_filler fin_first⁺⁺⁺
          (two_cocycle_simplex_unit (M := BoolS_Monoid) 6))) = false.
Proof. reflexivity. Defined.
