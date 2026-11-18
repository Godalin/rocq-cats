From Cats Require Export
  Cat.Premonoidal.Associator
  Cat.Premonoidal.Unitor.

Local Open Scope binoidal_scope.
Local Open Scope premonoidal_scope.

(** * Premonoidal Categories

    Combine an independently chosen associator and unitors on the same
    tensor actions. Their triangle is the only additional compatibility
    condition; pentagon belongs to the associator characterization. *)

(** * 预幺半范畴

    在同一张量作用上组合独立选择的结合子和单位子。三角形是唯一新增相容条件；
    五边形属于结合子的刻画。 *)

(** ** Compatibility of Fixed Choices

    Fix the same named category and tensor for both packages. The triangle
    compares their existing maps without choosing a new one. *)

(** ** 固定选择的相容性

    为两份选择固定同一具名范畴及张量；三角形比较已有映射，不作新的选择。 *)

Section Compatibility.
Context {C : Cat} `{BC : !HasBinoidal C}
  (AC : HasAssociator C BC) (UC : HasUnitors C BC).
Local Existing Instance AC.
Local Existing Instance UC.

Class IsPremonoidal
  :=
  { premonoidal_compatible_triangle (X Y : C)
    : (X ⊲ λₚ[Y]) ∘ αₚ[X; Iₚ[UC]; Y] ≈ ρₚ[X] ⊳ Y
  }.

End Compatibility.

Arguments premonoidal_compatible_triangle
  {C BC AC UC IsPremonoidal} _ _.

(** The fixed-parent extension stores each package once. Their shared
    tensor is an index, not an additional selected field. *)

(** 固定父结构上的扩展各保存一份选择；共享张量作为索引，不另存一份选择。 *)

Class HasPremonoidal (C : Cat) (BC : HasBinoidal C)
  :=
  { hasAssociator :> HasAssociator C BC
  ; hasUnitors :> HasUnitors C BC
  ; isPremonoidal :: IsPremonoidal hasAssociator hasUnitors
  }.

Arguments hasAssociator {_ _} _.
Arguments hasUnitors {_ _} _.
Arguments isPremonoidal {_ _ _}.
#[export] Existing Instance hasAssociator.
#[export] Existing Instance hasUnitors.

(** A complete category owns one binoidal parent and its extension. Its
    constructor and projections already supply the inheritance conversions. *)

(** 完整范畴拥有唯一双侧张量父结构及其扩展；构造器和投影已提供继承转换。 *)

Record PremonoidalCat
  := PremonoidalCatOfBinoidalCat
  { PremonoidalCatToBinoidalCat :> BinoidalCat

  ; hasPremonoidal
    :: HasPremonoidal PremonoidalCatToBinoidalCat
        (hasBinoidal PremonoidalCatToBinoidalCat)
  }.

Arguments PremonoidalCatOfBinoidalCat _ _ : clear implicits.

(** The selected packages satisfy their supplied triangle. *)

(** 选定的两份结构满足给定三角形。 *)

Lemma premonoidal_triangle {C : Cat} `{BC : !HasBinoidal C}
    `{PC : !HasPremonoidal C BC} (X Y : C)
  : (X ⊲ λₚ[Y]) ∘ αₚ[X; Iₚ[PC]; Y] ≈ ρₚ[X] ⊳ Y.
Proof.
  exact (premonoidal_compatible_triangle
    (IsPremonoidal := isPremonoidal) X Y).
Qed.
