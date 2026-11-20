From Cats Require Export
  Cat.Monoidal.Semigroupal
  Cat.Monoidal.Premonoidal.

(** * Monoidal Categories

    A monoidal category extends the chosen premonoidal structure by
    interchange on its tensor actions. *)

(** * 幺半范畴

    幺半范畴在选定预幺半结构的张量作用上增加交换律。 *)

(** Select compatible premonoidal data with interchange on a fixed category. *)

(** 在固定范畴上选取相容的预幺半数据，并为其张量作用提供交换律。 *)

Class HasMonoidal (C : Cat)
  :=
  { monoidal_hasBinoidal :> HasBinoidal C

  ; monoidal_hasPremonoidal
    :> HasPremonoidal C monoidal_hasBinoidal

  ; isMagmoidal
    :: IsMagmoidal monoidal_hasBinoidal
  }.

Arguments monoidal_hasBinoidal {_} _.
Arguments monoidal_hasPremonoidal {_} _.
Arguments isMagmoidal {_} _.

#[export] Existing Instance monoidal_hasBinoidal.
#[export] Existing Instance monoidal_hasPremonoidal.

(** A complete monoidal category owns a single premonoidal parent. The
    interchange witness refers to that parent's stored tensor actions. *)

(** 完整幺半范畴保存唯一预幺半父结构。交换律见证依赖该父结构保存的张量作用。 *)

Record MonoidalCat
  := MonoidalCatOfPremonoidalCat
  { MonoidalCatToPremonoidalCat
    :> PremonoidalCat

  ; monoidalCat_isMagmoidal
    :: IsMagmoidal (hasBinoidal MonoidalCatToPremonoidalCat)
  }.

Arguments MonoidalCatOfPremonoidalCat _ _ : clear implicits.

(** Read the same tensor, coherence and interchange on the underlying category. *)

(** 在底层范畴上读取同一份张量、相干性及交换律。 *)

Definition hasMonoidal (MC : MonoidalCat)
  : HasMonoidal MC
  :=
  {|monoidal_hasBinoidal := hasBinoidal MC
  ; monoidal_hasPremonoidal := hasPremonoidal MC
  ; isMagmoidal := monoidalCat_isMagmoidal MC
  |}.

#[export] Existing Instance hasMonoidal.
