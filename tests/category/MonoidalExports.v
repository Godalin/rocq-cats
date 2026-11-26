From Cats Require Import
  Cat.Monoidal.Functor
  Cat.Monoidal.Monoid.

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
