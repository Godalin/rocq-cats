From Cats Require Export
  Cat.Monoidal.Premonoidal.
From Cats Require Import
  Cat.Isomorphism
  Cat.Natural.

Local Open Scope monoidal_scope.
Local Open Scope ob_scope.

(** * Derived Inverse Laws

    Inverse structure maps introduce no new choices or axioms. Centrality
    follows from the general binoidal inverse theorem; naturality follows
    by inverting the vertical isomorphisms of each forward square. *)

(** * 导出的逆向定律

    逆结构映射不增加选择或公理。中心性来自双侧张量的一般取逆定理；自然性
    来自对每个正向方块的竖直同构取逆。 *)

Section InverseLaws.
Context {C : Cat} `{BC : !HasBinoidal C}.

(** The inverse associator is central. *)

(** 逆结合子是中心态射。 *)

Definition tensor_assoc_inv_central `{AC : !@HasTensorAssoc C BC}
    (X Y Z : @Ob C)
  : is_central α⁻¹[X; Y; Z]
  := central_inv (tensor_assoc X Y Z)
    (tensor_assoc_central X Y Z).

(** The inverse left unitor is central. *)

(** 逆左单位子是中心态射。 *)

Definition tensor_unitor_l_inv_central `{UC : !@HasTensorUnitors C BC}
    (X : @Ob C)
  : is_central λ⁻¹[X]
  := central_inv (tensor_unitor_l X) (tensor_unitor_l_central X).

(** The inverse right unitor is central. *)

(** 逆右单位子是中心态射。 *)

Definition tensor_unitor_r_inv_central `{UC : !@HasTensorUnitors C BC}
    (X : @Ob C)
  : is_central ρ⁻¹[X]
  := central_inv (tensor_unitor_r X) (tensor_unitor_r_central X).

(** The inverse left unitor is natural in its variable. *)

(** 逆左单位子在其变量上自然。 *)

Lemma tensor_unitor_l_inv_natural `{UC : !@HasTensorUnitors C BC}
    {X Y : @Ob C} (f : Hom X Y)
  : λ⁻¹[Y] ∘ f ≈ (𝐈[UC] ⊲ f) ∘ λ⁻¹[X].
Proof.
  exact (iso_square_inv
    (tensor_unitor_l X) (tensor_unitor_l Y)
    (𝐈[UC] ⊲ f) f (tensor_unitor_l_natural f)).
Qed.

(** The inverse right unitor is natural in its variable. *)

(** 逆右单位子在其变量上自然。 *)

Lemma tensor_unitor_r_inv_natural `{UC : !@HasTensorUnitors C BC}
    {X Y : @Ob C} (f : Hom X Y)
  : ρ⁻¹[Y] ∘ f ≈ (f ⊳ 𝐈[UC]) ∘ ρ⁻¹[X].
Proof.
  exact (iso_square_inv
    (tensor_unitor_r X) (tensor_unitor_r Y)
    (f ⊳ 𝐈[UC]) f (tensor_unitor_r_natural f)).
Qed.

(** The inverse associator is natural in the left position. *)

(** 逆结合子在左侧位置自然。 *)

Lemma tensor_assoc_inv_natural_l `{AC : !@HasTensorAssoc C BC}
    {X X' : @Ob C}
    (Y Z : @Ob C) (f : Hom X X')
  : α⁻¹[X'; Y; Z] ∘ (f ⊳ (Y ⊗ Z)) ≈
      ((f ⊳ Y) ⊳ Z) ∘ α⁻¹[X; Y; Z].
Proof.
  exact (iso_square_inv
    (tensor_assoc X Y Z) (tensor_assoc X' Y Z)
    ((f ⊳ Y) ⊳ Z) (f ⊳ (Y ⊗ Z))
    (tensor_assoc_natural_l Y Z f)).
Qed.

(** The inverse associator is natural in the middle position. *)

(** 逆结合子在中间位置自然。 *)

Lemma tensor_assoc_inv_natural_m `{AC : !@HasTensorAssoc C BC}
    {Y Y' : @Ob C}
    (X Z : @Ob C) (g : Hom Y Y')
  : α⁻¹[X; Y'; Z] ∘ (X ⊲ (g ⊳ Z)) ≈
      ((X ⊲ g) ⊳ Z) ∘ α⁻¹[X; Y; Z].
Proof.
  exact (iso_square_inv
    (tensor_assoc X Y Z) (tensor_assoc X Y' Z)
    ((X ⊲ g) ⊳ Z) (X ⊲ (g ⊳ Z))
    (tensor_assoc_natural_m X Z g)).
Qed.

(** The inverse associator is natural in the right position. *)

(** 逆结合子在右侧位置自然。 *)

Lemma tensor_assoc_inv_natural_r `{AC : !@HasTensorAssoc C BC}
    {Z Z' : @Ob C}
    (X Y : @Ob C) (h : Hom Z Z')
  : α⁻¹[X; Y; Z'] ∘ (X ⊲ (Y ⊲ h)) ≈
      ((X ⊗ Y) ⊲ h) ∘ α⁻¹[X; Y; Z].
Proof.
  exact (iso_square_inv
    (tensor_assoc X Y Z) (tensor_assoc X Y Z')
    ((X ⊗ Y) ⊲ h) (X ⊲ (Y ⊲ h))
    (tensor_assoc_natural_r X Y h)).
Qed.

End InverseLaws.
