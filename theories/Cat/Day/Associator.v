From Cats Require Import
  Cat.Core
  Cat.Isomorphism
  Cat.Functor.Core
  Cat.Natural
  Cat.Binoidal.Bifunctor
  Instance.Set.Core.
From Cats Require Export
  Cat.Day.Iterated.

(** * Associating Day Convolution *)

(** * Day 卷积的结合 *)

(** A supplied natural associativity isomorphism for a binary functor
    induces one for the selected convolutions. This construction does not
    assume a unit, symmetry or strength, and does not yet prove triangle
    or pentagon coherence. Existence stays with the four indicated choices. *)

(** 给定二元函子的自然结合同构，可导出选定卷积的自然结合同构。本构造不要求
    单位、对称或强度，尚不证明三角形或五边形相干性；存在性仅为指定的四个选择。 *)

(** ** Comparing the Ternary Universal Operations

    Fix the two inner convolutions and the two outer bracketings. Transport
    their natural ternary generators across the base associator and extend
    them by the preceding universal correspondences. *)

(** ** 比较三元泛操作

    固定两个内层卷积及两个外层括号。将其自然三元生成元沿基结合子运输，
    再由前述泛对应延拓。 *)

Section Associator.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C).
Context (A : TensorLeftF T ≅N TensorRightF T).
Context (F G H : Fct C (SetCat@{u p _ _ _ _ _}))
    `{HFG : !HasDay C T F G} `{HGH : !HasDay C T G H}
    `{HL : !HasDay C T (DayF T F G) H}
    `{HR : !HasDay C T F (DayF T G H)}.

(** The inverse base associator turns a right generator into a left weight. *)

(** 基结合子的逆将右生成元转为左权重。 *)

Definition DayAssociatorOperationN
  : DayTripleValuesF F G H ⇒
      (DayF T F (DayF T G H) ∘F TensorLeftF T)
  := (DayF T F (DayF T G H) ∘Nl NatIso_inv A.1 A.2)
      ∘Nv DayTripleRightGenN T F G H.

(** Extend the transported operation through the left nested convolution. *)

(** 将运输后的操作延拓过左嵌套卷积。 *)

Definition DayAssociatorN
  : DayF T (DayF T F G) H ⇒ DayF T F (DayF T G H)
  := DayTripleLeftExtendN T DayAssociatorOperationN.

(** Transport left generators in the other direction using the base map. *)

(** 用基正向映射沿另一方向运输左生成元。 *)

Definition DayAssociatorInvOperationN
  : DayTripleValuesF F G H ⇒
      (DayF T (DayF T F G) H ∘F TensorRightF T)
  := (DayF T (DayF T F G) H ∘Nl A.1) ∘Nv DayTripleLeftGenN T F G H.

(** The reverse map is another transparent universal extension. *)

(** 反向映射仍是透明的泛延拓。 *)

Definition DayAssociatorInvN
  : DayF T F (DayF T G H) ⇒ DayF T (DayF T F G) H
  := DayTripleRightExtendN T DayAssociatorInvOperationN.

(** Associating an identity triple changes just its weight by the base inverse. *)

(** 对恒等三重值结合，只会用基逆改变其权重。 *)

Lemma day_associator_gen (q : @Ob ((C ×C C) ×C C))
    (xyz : DayTripleValuesF F G H q)
  : DayAssociatorN (TensorLeftF T q) (DayTripleLeftGenN T F G H q xyz)
    ≈S fmap (DayF T F (DayF T G H)) ((A.2 q).1)
      (DayTripleRightGenN T F G H q xyz).
Proof.
  exact (day_triple_left_extend_gen T DayAssociatorOperationN q xyz).
Defined.

(** The reverse computation uses the forward base associator. *)

(** 反向计算使用正向基结合子。 *)

Lemma day_associator_inv_gen (q : @Ob ((C ×C C) ×C C))
    (xyz : DayTripleValuesF F G H q)
  : DayAssociatorInvN (TensorRightF T q) (DayTripleRightGenN T F G H q xyz)
    ≈S fmap (DayF T (DayF T F G) H) (A.1 q)
      (DayTripleLeftGenN T F G H q xyz).
Proof.
  exact (day_triple_right_extend_gen T DayAssociatorInvOperationN q xyz).
Defined.

(** Both nested universal properties reduce the left inverse law to the base law. *)

(** 两层泛性质将左逆律归约到基逆律。 *)

Lemma day_associator_inv_l
  : (DayAssociatorInvN ∘Nv DayAssociatorN) ≈N idN.
Proof.
  apply (day_triple_left_nat_ext T F G H). intros q xyz.
  transitivity (DayAssociatorInvN (TensorLeftF T q)
    (fmap (DayF T F (DayF T G H)) ((A.2 q).1)
      (DayTripleRightGenN T F G H q xyz))).
  - exact (@func_proper _ _ (DayAssociatorInvN (TensorLeftF T q))
      _ _ (day_associator_gen q xyz)).
  - transitivity (fmap (DayF T (DayF T F G) H) ((A.2 q).1)
      (DayAssociatorInvN (TensorRightF T q)
        (DayTripleRightGenN T F G H q xyz))).
    + exact (nt_naturality DayAssociatorInvN ((A.2 q).1)
        (DayTripleRightGenN T F G H q xyz)).
    + transitivity (fmap (DayF T (DayF T F G) H) ((A.2 q).1)
        (fmap (DayF T (DayF T F G) H) (A.1 q)
          (DayTripleLeftGenN T F G H q xyz))).
      * exact (@func_proper _ _ (fmap (DayF T (DayF T F G) H) ((A.2 q).1))
          _ _ (day_associator_inv_gen q xyz)).
      * transitivity (fmap (DayF T (DayF T F G) H)
          ((A.2 q).1 ∘ A.1 q) (DayTripleLeftGenN T F G H q xyz)).
        -- symmetry. apply (@functor_comp C SetCat (DayF T (DayF T F G) H)).
        -- transitivity (fmap (DayF T (DayF T F G) H) id
             (DayTripleLeftGenN T F G H q xyz)).
           ++ exact (@functor_fmap_proper C SetCat (DayF T (DayF T F G) H)
                _ _ _ _ (fst (A.2 q).2) (DayTripleLeftGenN T F G H q xyz)).
           ++ apply (@functor_id C SetCat (DayF T (DayF T F G) H)).
Defined.

(** The right inverse follows from the other base inverse equation. *)

(** 右逆来自另一条基逆方程。 *)

Lemma day_associator_inv_r
  : (DayAssociatorN ∘Nv DayAssociatorInvN) ≈N idN.
Proof.
  apply (day_triple_right_nat_ext T F G H). intros q xyz.
  transitivity (DayAssociatorN (TensorRightF T q)
    (fmap (DayF T (DayF T F G) H) (A.1 q)
      (DayTripleLeftGenN T F G H q xyz))).
  - exact (@func_proper _ _ (DayAssociatorN (TensorRightF T q))
      _ _ (day_associator_inv_gen q xyz)).
  - transitivity (fmap (DayF T F (DayF T G H)) (A.1 q)
      (DayAssociatorN (TensorLeftF T q)
        (DayTripleLeftGenN T F G H q xyz))).
    + exact (nt_naturality DayAssociatorN (A.1 q)
        (DayTripleLeftGenN T F G H q xyz)).
    + transitivity (fmap (DayF T F (DayF T G H)) (A.1 q)
        (fmap (DayF T F (DayF T G H)) ((A.2 q).1)
          (DayTripleRightGenN T F G H q xyz))).
      * exact (@func_proper _ _ (fmap (DayF T F (DayF T G H)) (A.1 q))
          _ _ (day_associator_gen q xyz)).
      * transitivity (fmap (DayF T F (DayF T G H))
          (A.1 q ∘ (A.2 q).1) (DayTripleRightGenN T F G H q xyz)).
        -- symmetry. apply (@functor_comp C SetCat (DayF T F (DayF T G H))).
        -- transitivity (fmap (DayF T F (DayF T G H)) id
             (DayTripleRightGenN T F G H q xyz)).
           ++ exact (@functor_fmap_proper C SetCat (DayF T F (DayF T G H))
                _ _ _ _ (snd (A.2 q).2) (DayTripleRightGenN T F G H q xyz)).
           ++ apply (@functor_id C SetCat (DayF T F (DayF T G H))).
Defined.

(** The pointwise left inverse keeps its value abstract before a concrete
    client supplies a large representative. *)

(** 逐点左逆先保持值抽象，再由具体客户端代入较大的代表。 *)

Lemma day_associator_inv_l_at (Z : @Ob C)
    (v : DayF T (DayF T F G) H Z)
  : DayAssociatorInvN Z (DayAssociatorN Z v) ≈S v.
Proof. exact (day_associator_inv_l Z v). Defined.

(** The pointwise right inverse exposes the same computational boundary. *)

(** 逐点右逆暴露相同的计算边界。 *)

Lemma day_associator_inv_r_at (Z : @Ob C)
    (v : DayF T F (DayF T G H) Z)
  : DayAssociatorN Z (DayAssociatorInvN Z v) ≈S v.
Proof. exact (day_associator_inv_r Z v). Defined.

(** The supplied four coend families therefore give a natural associativity
    isomorphism. Coherence is a separate condition and theorem. *)

(** 因此，给定的四族 coend 给出自然结合同构；相干性是另外的条件与定理。 *)

Definition DayAssociator
  : DayF T (DayF T F G) H ≅N DayF T F (DayF T G H).
Proof.
  exists DayAssociatorN. intros Z. exists (DayAssociatorInvN Z).
  split; [exact (day_associator_inv_l Z) | exact (day_associator_inv_r Z)].
Defined.

End Associator.

(** ** Naturality in All Three Input Functors

    Keep the binary functor and its natural associator fixed, selecting
    only the four convolutions at each endpoint. Joint distinction of
    triples reduces the input square to binary Day map naturality. *)

(** ** 关于三个输入函子的自然性

    固定二元函子及其自然结合子，只在两个端点各选择四个卷积。三重生成元的
    联合区分性将输入方块归约到二元 Day 映射自然性。 *)

Section AssociatorInputs.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C).
Context (A : TensorLeftF T ≅N TensorRightF T).
Context {F G H F' G' H' : Fct C (SetCat@{u p _ _ _ _ _})}
    `{HFG : !HasDay C T F G} `{HGH : !HasDay C T G H}
    `{HL : !HasDay C T (DayF T F G) H}
    `{HR : !HasDay C T F (DayF T G H)}
    `{HFG' : !HasDay C T F' G'} `{HGH' : !HasDay C T G' H'}
    `{HL' : !HasDay C T (DayF T F' G') H'}
    `{HR' : !HasDay C T F' (DayF T G' H')}.
Context (α : F ⇒ F') (β : G ⇒ G') (γ : H ⇒ H').

(** Associating commutes with changing each input naturally. *)

(** 结合与每个输入的自然改变交换。 *)

Lemma day_associator_natural
  : (DayAssociatorN T A F' G' H' ∘Nv DayTripleLeftMapN T α β γ) ≈N
      (DayTripleRightMapN T α β γ ∘Nv DayAssociatorN T A F G H).
Proof.
  apply (day_triple_left_nat_ext T F G H).
  intros [[a b] d] [[x y] z].
  pose proof (@day_triple_left_map_gen C T F G H F' G' H' α β γ
    HFG HFG' HL HL' a b d x y z) as HmapL.
  pose proof (@day_triple_right_map_gen C T F G H F' G' H' α β γ
    HGH HGH' HR HR' a b d x y z) as HmapR.
  transitivity (DayAssociatorN T A F' G' H' (T (T (a,b),d))
    (DayTripleLeftGenN T F' G' H' ((a,b),d)
      ((α a x,β b y),γ d z))).
  - exact (@func_proper _ _ (DayAssociatorN T A F' G' H' (T (T (a,b),d)))
      (DayTripleLeftMapN T α β γ (T (T (a,b),d))
        (DayTripleLeftGenN T F G H ((a,b),d) ((x,y),z)))
      (DayTripleLeftGenN T F' G' H' ((a,b),d) ((α a x,β b y),γ d z)) HmapL).
  - transitivity (fmap (DayF T F' (DayF T G' H')) ((A.2 ((a,b),d)).1)
      (DayTripleRightGenN T F' G' H' ((a,b),d)
        ((α a x,β b y),γ d z))).
    + exact (day_associator_gen T A F' G' H' ((a,b),d)
        ((α a x,β b y),γ d z)).
    + transitivity (fmap (DayF T F' (DayF T G' H')) ((A.2 ((a,b),d)).1)
        (DayTripleRightMapN T α β γ (T (a,T (b,d)))
          (DayTripleRightGenN T F G H ((a,b),d) ((x,y),z)))).
      * apply (@func_proper _ _
          (fmap (DayF T F' (DayF T G' H')) ((A.2 ((a,b),d)).1))).
        symmetry. exact HmapR.
      * transitivity (DayTripleRightMapN T α β γ (T (T (a,b),d))
          (fmap (DayF T F (DayF T G H)) ((A.2 ((a,b),d)).1)
            (DayTripleRightGenN T F G H ((a,b),d) ((x,y),z)))).
        -- symmetry. exact (nt_naturality (DayTripleRightMapN T α β γ)
             ((A.2 ((a,b),d)).1)
             (DayTripleRightGenN T F G H ((a,b),d) ((x,y),z))).
        -- exact (@func_proper _ _
             (DayTripleRightMapN T α β γ (T (T (a,b),d)))
             (fmap (DayF T F (DayF T G H)) ((A.2 ((a,b),d)).1)
               (DayTripleRightGenN T F G H ((a,b),d) ((x,y),z)))
             (DayAssociatorN T A F G H (T (T (a,b),d))
               (DayTripleLeftGenN T F G H ((a,b),d) ((x,y),z)))
             (symmetry (day_associator_gen T A F G H ((a,b),d) ((x,y),z)))).
Defined.

(** The inverse input square reuses the general inverse-square theorem. *)

(** 逆的输入方块复用一般逆方块定理。 *)

Lemma day_associator_inv_natural
  : (DayAssociatorInvN T A F' G' H' ∘Nv DayTripleRightMapN T α β γ) ≈N
      (DayTripleLeftMapN T α β γ ∘Nv DayAssociatorInvN T A F G H).
Proof.
  intros Z.
  exact (@iso_square_inv SetCat _ _ _ _
    (DayAssociatorN T A F G H Z; (DayAssociator T A F G H).2 Z)
    (DayAssociatorN T A F' G' H' Z; (DayAssociator T A F' G' H').2 Z)
    (DayTripleLeftMapN T α β γ Z) (DayTripleRightMapN T α β γ Z)
    (day_associator_natural Z)).
Defined.

End AssociatorInputs.

(** ** Associativity on the Functor Category

    Uniform explicit convolution choices give the tensor bifunctor.
    Package input naturality and the transparent inverses as its natural
    associativity isomorphism; no coherence claim is added by this packaging. *)

(** ** 函子范畴上的结合性

    统一显式卷积选择给出张量双函子。将输入自然性和透明逆打包为其自然结合
    同构；这种打包本身不增加相干性结论。 *)

Section FunctorCategoryAssociator.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C).
Context (HD : ∀ F G : Fct C (SetCat@{u p _ _ _ _ _}), HasDay C T F G).
Context (A : TensorLeftF T ≅N TensorRightF T).

(** The family of associators is natural on the triple functor category. *)

(** 结合子族在三重函子范畴上自然。 *)

Program Definition DayAssociatorFctN
  : TensorLeftF (DayTensorF T HD) ⇒ TensorRightF (DayTensorF T HD)
  :=
  {|nt q := _
  |}.
Next Obligation.
  destruct q as [[F G] H].
  exact (@DayAssociatorN C T A F G H (HD F G) (HD G H)
    (HD (@DayF C T F G (HD F G)) H)
    (HD F (@DayF C T G H (HD G H)))).
Defined.
Next Obligation.
  destruct X as [[F G] H], Y as [[F' G'] H'], f as [[α β] γ].
  exact (@day_associator_natural C T A F G H F' G' H'
    (HD F G) (HD G H) (HD (@DayF C T F G (HD F G)) H)
    (HD F (@DayF C T G H (HD G H)))
    (HD F' G') (HD G' H') (HD (@DayF C T F' G' (HD F' G')) H')
    (HD F' (@DayF C T G' H' (HD G' H'))) α β γ).
Defined.

(** Componentwise inverses retain the computed universal extensions. *)

(** 分量逆保留计算得到的泛延拓。 *)

Definition DayAssociatorFct
  : TensorLeftF (DayTensorF T HD) ≅N TensorRightF (DayTensorF T HD).
Proof.
  exists DayAssociatorFctN. intros [[F G] H].
  exact (NatIso_is_iso _ (@DayAssociator C T A F G H (HD F G) (HD G H)
    (HD (@DayF C T F G (HD F G)) H)
    (HD F (@DayF C T G H (HD G H)))).2).
Defined.

End FunctorCategoryAssociator.
