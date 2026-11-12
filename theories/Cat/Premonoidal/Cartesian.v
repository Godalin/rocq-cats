From Cats Require Export
  Cat.Premonoidal.Symmetric
  Cat.Monoidal.Cartesian.
From Cats Require Import
  Cat.Terminal
  Cat.Product.Transport.

(** * Cartesian Exchange

    Finite products extend their existing monoidal structure by canonical
    exchange. Only the new symmetry laws are proved here; all premonoidal
    data and coherence are inherited from the same cartesian parent. *)

(** * 笛卡尔交换

    有限积通过规范交换扩展其已有幺半结构。此处仅证明新增对称定律，全部
    预幺半数据与相干性都继承自同一笛卡尔父结构。 *)

Section Cartesian.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}.

(** Canonical product exchange supplies an explicit symmetric structure.
    Importing this module selects no default structure on [C]. *)

(** 规范积交换给出显式对称结构；导入本模块不会为 [C] 选定默认结构。 *)

Program Definition CartesianSymmetricPremonoidal
  : SymmetricPremonoidalCat C
  :=
  {|SymmetricPremonoidalP := MonoidalP CartesianMonoidal
  ; premonoidal_symmetry X Y := ⟨π2, π1⟩
  ; premonoidal_symmetry_central X Y :=
      @monoidal_arrow_central C CartesianMonoidal _ _ _
  |}.
Next Obligation.
  rewrite product_comp_r, product_β1, product_β2. apply product_pair_η.
Defined.
Next Obligation.
  change (⟨π2, π1⟩ ∘ (f × @id Y) ≈
    (@id Y × f) ∘ ⟨π2, π1⟩).
  repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r]. reflexivity.
Defined.
Next Obligation.
  change ((@product_assoc C HP Y Z X).1 ∘
    (⟨π2, π1⟩ ∘ (@product_assoc C HP X Y Z).1) ≈
    (@id Y × ⟨π2, π1⟩) ∘
      ((@product_assoc C HP Y X Z).1 ∘ (⟨π2, π1⟩ × @id Z))).
  unfold product_assoc. cbn.
  repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r]. reflexivity.
Defined.
Next Obligation. apply product_β2. Defined.

End Cartesian.
