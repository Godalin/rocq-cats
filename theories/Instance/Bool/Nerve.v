From Cats Require Export
  Instance.Set.Simplicial.Monoid.
From Cats Require Import
  Instance.Bool.Action
  Instance.Bool.Group
  Instance.Set.Lift
  Instance.Set.Simplicial.Nerve.

Local Open Scope nat_scope.
Local Existing Instance BoolS_Monoid.

(** * A Nerve with Two Distinct Boolean Loops *)

(** * 具有两个不同布尔环路的 nerve *)

(** The xor monoid supplies an arrow-chain nerve with its original
    specified equality, in the smallest value universes. *)

(** 异或幺半群在最小值宇宙中给出箭头链 nerve，保留原来的指定相等。 *)

Definition BoolNerve
  : Functor (Δ^op) SetCat@{Set Set _ _ _ _ _}
  := Nₘ(BoolS).

(** The identity one-simplex. *)

(** 恒等一维单形。 *)

Definition bool_nerve_id
  : BoolNerve 1
  := false ∷S []S.

(** The nonidentity one-simplex records the nontrivial group loop. *)

(** 非恒等一维单形记录群的非平凡环路。 *)

Definition bool_nerve_loop
  : BoolNerve 1
  := true ∷S []S.

(** The original distinction between loops is preserved. *)

(** 原来的环路区别得到保留。 *)

Lemma bool_nerve_loop_not_id
  : ¬ (bool_nerve_loop ≈S bool_nerve_id).
Proof. intros H. specialize (H fin_first). discriminate H. Qed.

(** Two successive nontrivial loops form a two-simplex. *)

(** 连续两个非平凡环路构成一个二维单形。 *)

Definition bool_nerve_double_loop
  : BoolNerve 2
  := true ∷S true ∷S []S.

(** The middle face expresses that the nontrivial loop is its own inverse. *)

(** 中间面表达非平凡环路自逆。 *)

Lemma bool_nerve_double_loop_face
  : d[BoolNerve; 1; fin_next fin_first] bool_nerve_double_loop ≈S
      bool_nerve_id.
Proof. intros [[] | []]. reflexivity. Defined.

(** The general diagram comparison specializes to the boolean groupoid. *)

(** 一般图式比较实例化到布尔群胚。 *)

Definition BoolNerveComparison
  : (LiftF ∘F BoolNerve : Functor (Δ^op) SetCat@{Set Set _ _ _ _ _}) ⇒
      N≅(BoolGroupoid)
  := MonoidDiagramN.

(** The diagram comparison identifies the two distinct one-simplices.
    This locates the loss of distinction in the comparison, not in BoolNerve. *)

(** 图式比较将两个不同的一维单形送到相等的像，从而将区别的丢失定位在比较
    映射处；BoolNerve 自身保留这个区别。 *)

Lemma bool_nerve_comparison_identifies_loops
  : BoolNerveComparison 1 {|lower := bool_nerve_loop
                           |} ≈S
      BoolNerveComparison 1 {|lower := bool_nerve_id
                             |}.
Proof.
  apply (snd (nerve_groupoid_eq_iff (HC := BoolGroupoid_IsGroupoid) _ _)).
  apply iso_refl.
Defined.
