From Cats Require Export
  Cat.Monoidal.PremonoidalLaws.
From Cats Require Import
  Cat.Isomorphism.

Local Open Scope monoidal_scope.
Local Open Scope ob_scope.

(** * Symmetric Premonoidal Categories

    Central exchange coherently swaps ordinary tensor positions. Its
    naturality uses one computation at a time and asserts no interchange
    of two effects. Involution supplies the inverse and derives naturality
    in the other variable, without storing either twice. *)

(** * 对称预幺半范畴

    中心交换相干地互换通常张量位置。其自然性每次只使用一个计算，不主张
    两个效应的交换律。对合性提供逆，并导出另一变量的自然性，均不重复保存。 *)

Minks.Mixin HasTensorSym (C : Cat)
  extends HasBinoidal C
  :=
  { tensor_sym (X Y : @Ob C)
    : Hom (X ⊗ Y) (Y ⊗ X)
  ; tensor_sym_central (X Y : @Ob C)
    : is_central (tensor_sym X Y)
  ; tensor_sym_involutive (X Y : @Ob C)
    : tensor_sym Y X
      ∘ tensor_sym X Y ≈ id

  (** Store naturality in the left position; right naturality is derived. *)

  (** 保存左位置自然性；右位置自然性随后导出。 *)

  ; tensor_sym_natural_l {X X' : @Ob C}
      (Y : @Ob C) (f : Hom X X')
    : tensor_sym X' Y ∘ (f ⊳ Y) ≈
        (Y ⊲ f) ∘ tensor_sym X Y
  }.

Arguments tensor_sym {C BC S} _ _ : rename.

(** The selected exchange agrees with the selected associator. *)

(** 选定交换与选定结合子满足六边形。 *)

Minks.Mixin IsSymHexagon (C : Cat)
  extends HasTensorSym C, HasTensorAssoc C
  :=
  { tensor_sym_hexagon (X Y Z : @Ob C)
    : α[Y; Z; X] ∘
        (tensor_sym X (Y ⊗ Z) ∘ α[X; Y; Z]) ≈
        (Y ⊲ tensor_sym X Z) ∘
          (α[Y; X; Z] ∘ (tensor_sym X Y ⊳ Z))
  }.

Arguments tensor_sym_hexagon {C BC S AC H} _ _ _ : rename.

(** The selected exchange agrees with the two selected unitors. *)

(** 选定交换与两个选定单位子相容。 *)

Minks.Mixin IsSymUnit (C : Cat)
  extends HasTensorSym C, HasTensorUnitors C
  :=
  { tensor_sym_unit (X : @Ob C)
    : λ[X] ∘ tensor_sym X (𝐈[hasTensorUnitors]) ≈ ρ[X]
  }.

Arguments tensor_sym_unit {C BC S UC H} _ : rename.

(** Extend one premonoidal category by its chosen symmetric exchange. *)

(** 在一份预幺半范畴上加入选定的对称交换。 *)

Minks.Struct SymPremonoidalCat
  extends PremonoidalCat
  with  hasTensorSym : HasTensorSym,
        isSymHexagon : IsSymHexagon,
        isSymUnit : IsSymUnit
  exports HasSymPremonoidal.

Notation "'σₚ[' X ';' Y ']'" := (tensor_sym X Y)
  : monoidal_scope.

(** ** Derived Symmetry Laws

    Fix a symmetric exchange on the selected tensor. Derive the inverse
    and other-variable naturality, and recover the right action. *)

(** ** 导出的对称定律

    固定选定张量上的对称交换，导出取逆及另一变量的自然性，再用对称性恢复右作用。 *)

Section Derived.
Context {C : Cat} `{BC : !HasBinoidal C}
  `{S : !@HasTensorSym C BC}.

(** The chosen inverse of exchange is exchange in the opposite order. *)

(** 交换的选定逆就是反序交换。 *)

Definition TensorSymIso (X Y : @Ob C)
  : (X ⊗ Y) ≅ (Y ⊗ X)
  := (σₚ[X; Y]; (σₚ[Y; X];
    (tensor_sym_involutive X Y,
      tensor_sym_involutive Y X))).

(** Invert the left-variable square to obtain right-variable naturality. *)

(** 对左变量方块取逆，得到右变量自然性。 *)

Lemma tensor_sym_natural_r {Y Y' : @Ob C}
    (X : @Ob C) (g : Hom Y Y')
  : σₚ[X; Y'] ∘ (X ⊲ g) ≈ (g ⊳ X) ∘ σₚ[X; Y].
Proof.
  exact (iso_square_inv (TensorSymIso Y X)
    (TensorSymIso Y' X) (g ⊳ X) (X ⊲ g)
    (tensor_sym_natural_l X g)).
Qed.

(** Conjugation by exchange recovers right action from left action. *)

(** 沿交换共轭，从左作用恢复右作用。 *)

Lemma tensor_r_sym {X Y : @Ob C}
    (Z : @Ob C) (f : Hom X Y)
  : f ⊳ Z ≈ σₚ[Z; Y] ∘ ((Z ⊲ f) ∘ σₚ[X; Z]).
Proof.
  apply (iso_cancel_l (TensorSymIso Y Z)).
  rewrite <- !comp_assoc,
    (@tensor_sym_involutive C BC S Z Y), comp_id_l.
  exact (tensor_sym_natural_l Z f).
Qed.

End Derived.
