From Cats Require Import
  Cat.Monoidal.Functor
  Cat.Monoidal.Monoid
  Cat.Monoidal.Symmetric.

(** * Fixed-category monoidal interface

    Extracting and packing preserve every component of the monoidal
    structure on the original category. *)

Example fixed_monoidal_round_trip (M : MonoidalCat)
  : MonoidalCatOfHasMonoidal M (MonoidalCatToHasMonoidal M) = M.
Proof. destruct M. reflexivity. Qed.

(** Both views expose the same triangle witness. *)

Example fixed_monoidal_triangle (M : MonoidalCat)
  : HasMonoidal_isPremonoidal (MonoidalCatToHasMonoidal M)
    = PremonoidalCat_isPremonoidal (MonoidalCatToPremonoidalCat M)
  := eq_refl.

(** ** Two monoidal structures on one category

    The unit comparison goes from the chosen target unit to the image
    of the chosen source unit. Both units live in [C]. *)

Section TwoUnits.
Context {C : Cat} (source target : HasMonoidal C)
  (F : @LaxMonoidalFct C C source target).

Local Open Scope monoidal_scope.
Local Notation "'𝐈₁'" := (𝐈[HasMonoidal_unitors source])
  (at level 0)
  : monoidal_scope.
Local Notation "'𝐈₂'" := (𝐈[HasMonoidal_unitors target])
  (at level 0)
  : monoidal_scope.

Check φ₀[F] : Hom 𝐈₂ (F 𝐈₁).
Fail Check φ₀[F] : Hom 𝐈₁ (F 𝐈₂).
Check lax_tensorN (hasLaxMonoidalF F)
  : (tensorF (IM := HasMonoidal_interchange target) ∘F (F ×F F))
      ⇒ (F ∘F tensorF (IM := HasMonoidal_interchange source)).
Fail Check lax_tensorN (hasLaxMonoidalF F)
  : (tensorF (IM := HasMonoidal_interchange source) ∘F (F ×F F))
      ⇒ (F ∘F tensorF (IM := HasMonoidal_interchange target)).
End TwoUnits.

(** Two monoid structures on the same object retain their own operations. *)

Section MonoidChoices.
Local Open Scope monoidal_scope.
Context {C : Cat} `{MC : HasMonoidal C} (A : C) (P Q : HasMonoidObj A).

Example first_unit
  : e[MakeMonoidObj A P] = @monoid_obj_unit _ _ A P
  := eq_refl.
Example second_mul
  : m[MakeMonoidObj A Q] = @monoid_obj_mul _ _ A Q
  := eq_refl.
End MonoidChoices.

(** The exported constructor assembles the five selected components. *)

(** 导出接口的构造器组装选定的五个组件。 *)

Section ComponentAssembly.
Context (C : Cat) `{B : !HasBinoidal C} `{A : !HasTensorAssoc C}
  `{I : !IsMagmoidal C} `{U : !HasTensorUnitors C}.
Timeout 3 Fail Definition missing_triangle : HasMonoidal C := _.
Context `{P : !IsPremonoidal C}.
Definition assembled_from_components : HasMonoidal C := _.
Example selected_components
  : assembled_from_components = MakeHasMonoidal C B A I U P
  := eq_refl.
End ComponentAssembly.

(** A supplied symmetric structure determines the monoidal structure
    used by the category of monoid objects. *)

(** 给定的对称幺半结构确定构造幺半对象范畴所用的幺半结构。 *)

Section SymmetricMonoids.
Context (C : Cat) `{S : !HasSymMonoidal C}.
Definition monoids : Cat := MonoidCat C.
Example symmetric_selection : (_ : HasMonoidal C) =
    MakeHasMonoidal C (HasSymMonoidal_hasBinoidal S) (HasSymMonoidal_associator S)
      (HasSymMonoidal_interchange S) (HasSymMonoidal_unitors S)
      (HasSymMonoidal_isPremonoidal S) := eq_refl.
End SymmetricMonoids.
