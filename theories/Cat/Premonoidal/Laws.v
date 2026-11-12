From Cats Require Export
  Cat.Premonoidal.Core.
From Cats Require Import
  Cat.Isomorphism
  Cat.Natural.

Local Open Scope binoidal_scope.
Local Open Scope premonoidal_scope.

(** * Derived Inverse Laws

    Inverse structure maps introduce no new choices or axioms. Centrality
    follows from the general binoidal inverse theorem; naturality follows
    by inverting the vertical isomorphisms of each forward square. *)

(** * 导出的逆向定律

    逆结构映射不增加选择或公理。中心性来自双侧张量的一般取逆定理；自然性
    来自对每个正向方块的竖直同构取逆。 *)

Section InverseLaws.
Context {C : Cat} `{PC : !PremonoidalCat C}.

(** The inverse associator is central. *)

(** 逆结合子是中心态射。 *)

Definition premonoidal_assoc_inv_central (X Y Z : @Ob C)
  : is_central αₚ⁻¹[X; Y; Z]
  := central_inv (premonoidal_associator X Y Z)
    (premonoidal_assoc_central X Y Z).

(** The inverse left unitor is central. *)

(** 逆左单位子是中心态射。 *)

Definition premonoidal_unit_l_inv_central (X : @Ob C)
  : is_central λₚ⁻¹[X]
  := central_inv (premonoidal_left_unitor X) (premonoidal_unit_l_central X).

(** The inverse right unitor is central. *)

(** 逆右单位子是中心态射。 *)

Definition premonoidal_unit_r_inv_central (X : @Ob C)
  : is_central ρₚ⁻¹[X]
  := central_inv (premonoidal_right_unitor X) (premonoidal_unit_r_central X).

(** The inverse left unitor is natural in its variable. *)

(** 逆左单位子在其变量上自然。 *)

Lemma premonoidal_unit_l_inv_natural {X Y : @Ob C} (f : Hom X Y)
  : λₚ⁻¹[Y] ∘ f ≈ (Iₚ[PC] ⊲ f) ∘ λₚ⁻¹[X].
Proof.
  exact (iso_square_inv
    (premonoidal_left_unitor X) (premonoidal_left_unitor Y)
    (Iₚ[PC] ⊲ f) f (premonoidal_unit_l_natural f)).
Qed.

(** The inverse right unitor is natural in its variable. *)

(** 逆右单位子在其变量上自然。 *)

Lemma premonoidal_unit_r_inv_natural {X Y : @Ob C} (f : Hom X Y)
  : ρₚ⁻¹[Y] ∘ f ≈ (f ⊳ Iₚ[PC]) ∘ ρₚ⁻¹[X].
Proof.
  exact (iso_square_inv
    (premonoidal_right_unitor X) (premonoidal_right_unitor Y)
    (f ⊳ Iₚ[PC]) f (premonoidal_unit_r_natural f)).
Qed.

(** The inverse associator is natural in the left position. *)

(** 逆结合子在左侧位置自然。 *)

Lemma premonoidal_assoc_inv_natural_l {X X' : @Ob C}
    (Y Z : @Ob C) (f : Hom X X')
  : αₚ⁻¹[X'; Y; Z] ∘ (f ⊳ (Y ⊗ Z)) ≈
      ((f ⊳ Y) ⊳ Z) ∘ αₚ⁻¹[X; Y; Z].
Proof.
  exact (iso_square_inv
    (premonoidal_associator X Y Z) (premonoidal_associator X' Y Z)
    ((f ⊳ Y) ⊳ Z) (f ⊳ (Y ⊗ Z))
    (premonoidal_assoc_natural_l Y Z f)).
Qed.

(** The inverse associator is natural in the middle position. *)

(** 逆结合子在中间位置自然。 *)

Lemma premonoidal_assoc_inv_natural_m {Y Y' : @Ob C}
    (X Z : @Ob C) (g : Hom Y Y')
  : αₚ⁻¹[X; Y'; Z] ∘ (X ⊲ (g ⊳ Z)) ≈
      ((X ⊲ g) ⊳ Z) ∘ αₚ⁻¹[X; Y; Z].
Proof.
  exact (iso_square_inv
    (premonoidal_associator X Y Z) (premonoidal_associator X Y' Z)
    ((X ⊲ g) ⊳ Z) (X ⊲ (g ⊳ Z))
    (premonoidal_assoc_natural_m X Z g)).
Qed.

(** The inverse associator is natural in the right position. *)

(** 逆结合子在右侧位置自然。 *)

Lemma premonoidal_assoc_inv_natural_r {Z Z' : @Ob C}
    (X Y : @Ob C) (h : Hom Z Z')
  : αₚ⁻¹[X; Y; Z'] ∘ (X ⊲ (Y ⊲ h)) ≈
      ((X ⊗ Y) ⊲ h) ∘ αₚ⁻¹[X; Y; Z].
Proof.
  exact (iso_square_inv
    (premonoidal_associator X Y Z) (premonoidal_associator X Y Z')
    ((X ⊗ Y) ⊲ h) (X ⊲ (Y ⊲ h))
    (premonoidal_assoc_natural_r X Y h)).
Qed.

End InverseLaws.

(** A fixed pair of contexts has its associator natural transformation. *)

(** 一对固定上下文具有相应的结合子自然变换。 *)

Program Definition PremonoidalContextAssociatorN {C : Cat}
    `{PC : !PremonoidalCat C} (Z W : @Ob C)
  : BinoidalLeftF (Z ⊗ W) ⇒ (BinoidalLeftF Z ∘F BinoidalLeftF W)
  :=
  {|nt X := αₚ[Z; W; X]
  |}.
Next Obligation. exact (premonoidal_assoc_natural_r Z W f). Defined.

(** The left unitor is natural from the unit context to identity. *)

(** 左单位子是从单位上下文到恒等的自然变换。 *)

Program Definition PremonoidalLeftUnitorN {C : Cat}
    `{PC : !PremonoidalCat C}
  : BinoidalLeftF (Iₚ[PC]) ⇒ IdF
  :=
  {|nt X := λₚ[X]
  |}.
Next Obligation. exact (premonoidal_unit_l_natural f). Defined.

(** Separate associator naturality also respects ordered sequences of
    three arrows. This does not require joint functoriality of the tensor. *)

(** 结合子的分别自然性也保持三条态射的有序组合，不要求张量的联合函子性。 *)

Lemma premonoidal_assoc_sequence_natural {C : Cat}
    `{PC : !PremonoidalCat C} {X X' Y Y' Z Z' : @Ob C}
    (f : Hom X X') (g : Hom Y Y') (h : Hom Z Z')
  : αₚ[X'; Y'; Z'] ∘ binoidal_sequence (binoidal_sequence f g) h ≈
      binoidal_sequence f (binoidal_sequence g h) ∘ αₚ[X; Y; Z].
Proof.
  unfold binoidal_sequence.
  rewrite binoidal_right_comp, binoidal_left_comp, <- !comp_assoc.
  rewrite (@premonoidal_assoc_natural_r C PC Z Z' X' Y' h).
  rewrite !comp_assoc. apply comp_proper; [reflexivity |].
  rewrite <- comp_assoc,
    (@premonoidal_assoc_natural_m C PC Y Y' X' Z g), comp_assoc.
  apply comp_proper; [reflexivity |].
  exact (@premonoidal_assoc_natural_l C PC X X' Y Z f).
Qed.
