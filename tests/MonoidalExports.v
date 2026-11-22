From Cats Require Import
  Cat.Monoidal.Functor.

(** * Fixed-category monoidal interface

    Extracting and packing preserve every component of the monoidal
    structure on the original category. *)

(** * 固定范畴上的幺半接口

    提取与打包保留原范畴上的每个幺半结构组件。 *)

Example fixed_monoidal_round_trip (M : MonoidalCat)
  : MonoidalCatOfHasMonoidal M (MonoidalCatToHasMonoidal M) = M.
Proof. destruct M. reflexivity. Qed.

(** Both views expose the same triangle witness. *)

(** 两条视图给出同一份三角形见证。 *)

Example fixed_monoidal_triangle (M : MonoidalCat)
  : HasMonoidal_isPremonoidal (MonoidalCatToHasMonoidal M)
    = PremonoidalCat_isPremonoidal (MonoidalCatToPremonoidalCat M)
  := eq_refl.

(** ** Two monoidal structures on one category

    The unit comparison goes from the chosen target unit to the image
    of the chosen source unit. Both units live in [C]. *)

(** ** 同一范畴上的两套幺半结构

    单位比较从选定的目标单位映向选定的来源单位的函子像。两个单位都在 [C] 中。 *)

Section TwoUnits.
Context {C : Cat} (source target : HasMonoidal C)
  (F : LaxMonoidalFct source target).

Local Open Scope monoidal_scope.
Local Notation "'𝐈₁'" := (𝐈[HasMonoidal_unitors source])
  (at level 0)
  : monoidal_scope.
Local Notation "'𝐈₂'" := (𝐈[HasMonoidal_unitors target])
  (at level 0)
  : monoidal_scope.

Check φ₀[F] : Hom 𝐈₂ (F 𝐈₁).
Fail Check φ₀[F] : Hom 𝐈₁ (F 𝐈₂).
End TwoUnits.
