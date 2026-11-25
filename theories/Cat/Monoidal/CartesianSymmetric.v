From Cats Require Export
  Cat.Monoidal.Symmetric
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
Local Existing Instance CartHasMonoidal.

(** Canonical product exchange supplies an explicit symmetric structure.
    Importing this module selects no default structure on [C]. *)

(** 规范积交换给出显式对称结构；导入本模块不会为 [C] 选定默认结构。 *)

Program Definition CartHasTensorSym
  : HasTensorSym C
  :=
  {|tensor_sym X Y := ⟨π2, π1⟩
  ; tensor_sym_central X Y :=
      tensor_arrow_central (IM := HasMonoidal_interchange CartHasMonoidal) _
  |}.
Next Obligation.
  rewrite product_comp_r, product_β1, product_β2. apply product_pair_η.
Qed.
Next Obligation.
  change (⟨π2, π1⟩ ∘ (f × id[Y]) ≈
    (id[Y] × f) ∘ ⟨π2, π1⟩).
  repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r]. reflexivity.
Qed.
(** The cartesian exchange and product associator satisfy the hexagon. *)

(** 笛卡尔交换与积结合子满足六边形。 *)

Program Definition CartIsSymHexagon
  : @IsSymHexagon C _ CartHasTensorSym _
  :=
  {|tensor_sym_hexagon := _|}.
Next Obligation.
  change ((@product_assoc C HP Y Z X).1 ∘
    (⟨π2, π1⟩ ∘ (@product_assoc C HP X Y Z).1) ≈
    (id[Y] × ⟨π2, π1⟩) ∘
      ((@product_assoc C HP Y X Z).1 ∘ (⟨π2, π1⟩ × id[Z]))).
  unfold product_assoc. cbn.
  repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r]. reflexivity.
Qed.
(** The cartesian exchange interchanges the two unitors. *)

(** 笛卡尔交换互换两个单位子。 *)

Program Definition CartIsSymUnit
  : @IsSymUnit C _ CartHasTensorSym _
  :=
  {|tensor_sym_unit := _|}.
Next Obligation. apply product_β2. Qed.

(** Finite products give a symmetric monoidal tensor with product swap. *)

(** 有限积给出对称幺半张量，其对称子交换两个积投影。 *)

Definition CartSymMonoidal
  : SymMonoidalCat
  := SymMonoidalCatOfMonoidalCat CartMonoidal
       CartHasTensorSym CartIsSymHexagon CartIsSymUnit.

(** Pack the exchange with the premonoidal view of the same finite products. *)

(** 将交换与同一份有限积的预幺半视图打包。 *)

Definition CartSymPremonoidal
  : SymPremonoidalCat
  := SymMonoidalCatToSymPremonoidalCat CartSymMonoidal.

End Cartesian.
