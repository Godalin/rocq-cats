From Cats Require Export
  Cat.Monoidal.Semigroupal
  Cat.Monoidal.Premonoidal.

(** * Monoidal Categories

    A monoidal category extends a semigroupal category by unitors
    compatible with its associator. *)

(** * 幺半范畴

    幺半范畴在半群张量范畴上增加与结合子相容的单位子。 *)

(** Combine the two branches on their shared binoidal tensor and associator. *)

(** 在共享的双侧张量和结合子上组合两条分支。 *)

Minks.Struct MonoidalCat
  extends SemigroupalCat, PremonoidalCat
  exports HasMonoidal [carrier].
