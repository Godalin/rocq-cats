From Cats Require Export
  Cat.Premonoidal.Laws.
From Cats Require Import
  Cat.Isomorphism.

Local Open Scope binoidal_scope.
Local Open Scope premonoidal_scope.

(** * Symmetric Premonoidal Categories

    Central exchange coherently swaps ordinary tensor positions. Its
    naturality uses one computation at a time and asserts no interchange
    of two effects. Involution supplies the inverse and derives naturality
    in the other variable, without storing either twice. *)

(** * 对称预幺半范畴

    中心交换相干地互换通常张量位置。其自然性每次只使用一个计算，不主张
    两个效应的交换律。对合性提供逆，并导出另一变量的自然性，均不重复保存。 *)

Class SymmetricPremonoidalCat (C : Cat)
  :=
  (** Inherit the unit, tensor actions and coherence from one parent. *)

  (** 从唯一父结构继承单位、张量作用及相干性。 *)

  { SymmetricPremonoidalP :> PremonoidalCat C

  (** The exchange maps are central and reverse each other. *)

  (** 交换映射为中心态射，彼此互逆。 *)

  ; premonoidal_symmetry (X Y : @Ob C) : Hom (X ⊗ Y) (Y ⊗ X)
  ; premonoidal_symmetry_central (X Y : @Ob C)
    : is_central (premonoidal_symmetry X Y)
  ; premonoidal_symmetry_involutive (X Y : @Ob C)
    : premonoidal_symmetry Y X ∘ premonoidal_symmetry X Y ≈ id

  (** Store naturality in the left position; right naturality is derived. *)

  (** 保存左位置自然性；右位置自然性随后导出。 *)

  ; premonoidal_symmetry_natural_l {X X' : @Ob C}
      (Y : @Ob C) (f : Hom X X')
    : premonoidal_symmetry X' Y ∘ (f ⊳ Y) ≈
        (Y ⊲ f) ∘ premonoidal_symmetry X Y

  (** Exchange agrees with reassociation and the two unitors. *)

  (** 交换与括号重排及两个单位子相容。 *)

  ; premonoidal_symmetry_hexagon (X Y Z : @Ob C)
    : αₚ[Y; Z; X] ∘
        (premonoidal_symmetry X (Y ⊗ Z) ∘ αₚ[X; Y; Z]) ≈
        (Y ⊲ premonoidal_symmetry X Z) ∘
          (αₚ[Y; X; Z] ∘ (premonoidal_symmetry X Y ⊳ Z))
  ; premonoidal_symmetry_unit (X : @Ob C)
    : λₚ[X] ∘ premonoidal_symmetry X (Iₚ[SymmetricPremonoidalP]) ≈ ρₚ[X]
  }.

Arguments SymmetricPremonoidalP {_} _.
Arguments premonoidal_symmetry {_ _} _ _.

(** Register the same parent for inherited instance search. *)

(** 为继承实例搜索注册同一个父结构。 *)

#[export] Existing Instance SymmetricPremonoidalP.

Notation "'σₚ[' X ';' Y ']'" := (premonoidal_symmetry X Y)
  : premonoidal_scope.

Section Derived.
Context {C : Cat} `{SP : !SymmetricPremonoidalCat C}.

(** The chosen inverse of exchange is exchange in the opposite order. *)

(** 交换的选定逆就是反序交换。 *)

Definition PremonoidalSymmetryIso (X Y : @Ob C)
  : (X ⊗ Y) ≅ (Y ⊗ X)
  := (σₚ[X; Y]; (σₚ[Y; X];
    (premonoidal_symmetry_involutive X Y,
      premonoidal_symmetry_involutive Y X))).

(** Invert the left-variable square to obtain right-variable naturality. *)

(** 对左变量方块取逆，得到右变量自然性。 *)

Lemma premonoidal_symmetry_natural_r {Y Y' : @Ob C}
    (X : @Ob C) (g : Hom Y Y')
  : σₚ[X; Y'] ∘ (X ⊲ g) ≈ (g ⊳ X) ∘ σₚ[X; Y].
Proof.
  exact (iso_square_inv (PremonoidalSymmetryIso Y X)
    (PremonoidalSymmetryIso Y' X) (g ⊳ X) (X ⊲ g)
    (premonoidal_symmetry_natural_l X g)).
Qed.

(** Conjugation by exchange recovers right action from left action. *)

(** 沿交换共轭，从左作用恢复右作用。 *)

Lemma premonoidal_right_symmetry {X Y : @Ob C}
    (Z : @Ob C) (f : Hom X Y)
  : f ⊳ Z ≈ σₚ[Z; Y] ∘ ((Z ⊲ f) ∘ σₚ[X; Z]).
Proof.
  apply (iso_cancel_l (PremonoidalSymmetryIso Y Z)).
  rewrite <- !comp_assoc, premonoidal_symmetry_involutive, comp_id_l.
  exact (premonoidal_symmetry_natural_l Z f).
Qed.

End Derived.
