From Cats Require Export
  Instance.Set.Simplicial.MonoidVertex.
From Cats Require Import
  Instance.Bool.Action
  Instance.Bool.Group
  Instance.Set.Lift
  Instance.Set.Simplicial.Kan
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

(** The general vertex nerve also retains the distinction between boolean
    loops, using identity transport on its singleton object set. *)

(** 一般顶点 nerve 在单元素对象集合上使用恒等运输，同样保留布尔环路的区别。 *)

Definition BoolVertexNerve
  : Functor (Δ^op) SetCat@{Set Set _ _ _ _ _}
  := Nᵥ(MonoidObjectsF BoolS).

(** The vertex nerve of the xor group has chosen fillers in every
    positive dimension, while retaining its distinct loops. Enable this
    structure explicitly. *)

(** 异或群的顶点 nerve 在全部正维具有选定填充，并保留不同环路；须显式启用此结构。 *)

Definition BoolVertexNerve_HasKanFillers
  : HasKanFillers BoolVertexNerve
  := vertex_groupoid_HasKanFillers (MonoidObjectsF BoolS)
      (HC := VertexCat_IsGroupoid (MonoidObjectsF BoolS)
        (HC := BoolGroupoid_IsGroupoid)).

(** Every compatible boolean-nerve boundary above dimension two has a
    unique filler, while the one-dimensional loops remain distinct. *)

(** 布尔 nerve 中每个高于二维的相容边界具有唯一填充，一维环路仍保持区别。 *)

Definition BoolVertexNerve_IsCoskeletal
  : BoolVertexNerve ⦂ Cosk[2]
  := vertex_groupoid_IsCoskeletal (MonoidObjectsF BoolS)
      (HC := VertexCat_IsGroupoid (MonoidObjectsF BoolS)
        (HC := BoolGroupoid_IsGroupoid)).

(** The tuple interpretation is a map into the general construction. *)

(** 元组解释给出进入一般构造的映射。 *)

Definition BoolVertexComparison
  : (LiftF ∘F BoolNerve : Functor (Δ^op) SetCat@{Set Set _ _ _ _ _}) ⇒
      BoolVertexNerve
  := MonoidVertexN.

(** The two loops stay unequal before forgetting the specified vertex
    comparison. This follows from the general reflection theorem. *)

(** 忘却指定顶点比较之前，两条环路保持不等；此结论直接来自一般反映定理。 *)

Lemma bool_vertex_loop_not_id
  : ¬ (BoolVertexComparison 1 {|lower := bool_nerve_loop
                              |} ≈S
      BoolVertexComparison 1 {|lower := bool_nerve_id
                              |}).
Proof.
  intros H. apply bool_nerve_loop_not_id.
  exact (monoid_vertex_reflects bool_nerve_loop bool_nerve_id H).
Qed.
