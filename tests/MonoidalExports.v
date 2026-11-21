From Cats Require Import
  Cat.Monoidal.Monoidal.

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
