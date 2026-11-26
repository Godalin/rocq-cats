From Cats Require Import
  Cat.Monoidal.Symmetric
  Cat.Monoidal.Monoid.

(** Local reverse packers test the two parents of a symmetric monoidal category. *)

(** 局部的反向打包函数检验对称幺半范畴的两种父结构。 *)

Section Symmetric.
#[local] Canonical symmetric_on_monoidal (M : MonoidalCat)
    `{S : !HasTensorSym M} `{H : !IsSymHexagon M} `{U : !IsSymUnit M}
  : SymMonoidalCat := SymMonoidalCatOfMonoidalCat M S H U.
#[local] Canonical symmetric_on_premonoidal (P : SymPremonoidalCat)
    `{I : !IsMagmoidal P}
  : SymMonoidalCat := SymMonoidalCatOfSymPremonoidalCat P I.

(** The symmetric premonoidal parent needs interchange. *)

(** 对称预幺半父结构还需交换律。 *)

Section OtherParent.
Context (P : SymPremonoidalCat).
Timeout 3 Fail Definition missing_interchange : SymMonoidalCat := P.
Context `{I : !IsMagmoidal P}.
Definition from_premonoidal : SymMonoidalCat := P.
Example keeps_interchange : SymMonoidalCat_interchange from_premonoidal = I := eq_refl.
End OtherParent.

(** Both parents inherit the choices of one supplied symmetric interface. *)

(** 两个父结构继承同一份对称接口的选择。 *)

Section FromRelative.
Context (C : Cat) `{R : !HasSymMonoidal C}.
Let parent := MonoidalCatOfHasMonoidal C (_ : HasMonoidal C).
Definition from_relative : SymMonoidalCat := parent.
Example stored_symmetry
  : SymMonoidalCat_hasTensorSym from_relative = HasSymMonoidal_hasTensorSym R
  := eq_refl.
Example all_components
  : from_relative = SymMonoidalCatOfHasSymMonoidal C R
  := eq_refl.
Let other_parent := SymPremonoidalCatOfHasSymPremonoidal C (_ : HasSymPremonoidal C).
Definition from_other_relative : SymMonoidalCat := other_parent.
Example parents_agree : from_relative = from_other_relative := eq_refl.
End FromRelative.

(** An independent interface on the same category may select a different tensor. *)

(** 同一范畴上的独立接口可以选择另一份张量。 *)

Section WrongTensor.
Context (M : MonoidalCat) `{R : !HasSymMonoidal M}.
Timeout 3 Fail Definition unrelated_tensor : SymMonoidalCat := M.
End WrongTensor.

Context (M : MonoidalCat) `{S : !HasTensorSym M} `{H : !IsSymHexagon M}.
Timeout 3 Fail Definition missing_unit : SymMonoidalCat := M.
Context `{U : !IsSymUnit M}.
Definition sym : SymMonoidalCat := M.
Example exact_sym : sym = SymMonoidalCatOfMonoidalCat M S H U := eq_refl.
Definition assembled : HasSymMonoidal M := _.
Definition monoids : Cat := MonoidCat sym.
End Symmetric.
