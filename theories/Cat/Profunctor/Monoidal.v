From Cats Require Export
  Cat.Profunctor.Coherence.
From Cats Require Import
  Cat.Core
  Cat.Monoidal.Bifunctor
  Cat.Isomorphism
  Instance.Set.Core.

Local Open Scope prof_scope.

(** * The Monoidal Category of Endoprofunctors

    Keep ordinary composition order: the left tensor factor follows the
    right one. Its associator is the inverse of the existing ordered-value
    reassociation. All composition choices remain explicit input; this
    construction asserts no global coend existence or resizing principle. *)

(** * 自 Profunctor 的幺半范畴

    保留通常复合次序：左张量因子在右因子之后作用。结合子为已有有序值重结合
    的逆。全部复合选择仍为显式输入；本构造不声称全局 coend 存在或大小重设
    原理。 *)

(** ** Associativity in Composition Order

    Fix a category and a uniform family of chosen composites. No Hom-unit
    bounds are needed yet. Package the existing inverse input square as
    natural associativity, then reverse the accepted pentagon using generic
    functorial invertibility and uniqueness of inverses. *)

(** ** 复合次序中的结合性

    固定范畴和统一选定复合族，暂不需要 Hom 单位的大小界。将已有逆输入方块
    打包为自然结合性，再用一般函子保持可逆性和逆唯一性反转已验收的五边形。 *)

Section Associativity.
Universes u p.
Context {C : Cat}.
Context (HC : ∀ Q P : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _}),
    HasProfComp C C C Q P).
Local Existing Instance HC.

Let K
  : Cat
  := FctCat ((C^op) ×C C) (SetCat@{u p _ _ _ _ _}).
Let T
  : Fct (K ×C K) K
  := ProfCompF C C C HC.

(** Read reassociation on the exact objects selected by the tensor.
    Its outer choices use those same inner functors, including their laws. *)

(** 在张量实际选定的对象上读取重结合；外层选择使用同一内层函子及其定律。 *)

Let a (R Q P : @Ob K)
  : T (R,T (Q,P)) ≅N T (T (R,Q),P)
  := @ProfunctorAssociator C C C C R Q P
      (HC Q P) (HC R Q) (HC R (T (Q,P))) (HC (T (R,Q)) P).

(** The selected inverse reassociation is natural on triples. *)

(** 选定的逆重结合在三元组上自然。 *)

Program Definition ProfAssociatorFctN
  : TensorLeftF T ⇒ TensorRightF T
  :=
  {|nt q := _
  |}.
Next Obligation.
  destruct q as [[R Q] P]. exact ((a R Q P).1 ^-1N (a R Q P).2).
Defined.
Next Obligation.
  destruct X as [[R Q] P], Y as [[R' Q'] P'], f as [[γ β] α].
  exact (@profunctor_associator_inv_natural C C C C R R' Q Q' P P'
    (HC Q P) (HC R Q) (HC R (T (Q,P))) (HC (T (R,Q)) P)
    (HC Q' P') (HC R' Q') (HC R' (T (Q',P'))) (HC (T (R',Q')) P')
    α β γ).
Defined.

(** Keep the same chosen maps and their forward reassociation inverses. *)

(** 保留同一组选定映射，以及作为其逆的正向重结合。 *)

Definition ProfAssociatorFct
  : TensorLeftF T ≅N TensorRightF T.
Proof.
  exists ProfAssociatorFctN. intros [[R Q] P].
  exact (NatIso_is_iso _ (NatIso_inv_NatIso (a R Q P).1 (a R Q P).2)).
Defined.

(** Reverse the accepted pentagon on these exact tensor objects.
    Ordinary functoriality supplies both whiskered inverse witnesses. *)

(** 在这些实际张量对象上反转已验收五边形；普通函子性提供两个须化逆见证。 *)

Lemma prof_monoidal_pentagon (S R Q P : @Ob K)
  : (ProfAssociatorFctN ((S,R),T (Q,P)) ∘Nv
      ProfAssociatorFctN ((T (S,R),Q),P)) ≈N
    (fmap (π2F T S) (ProfAssociatorFctN ((R,Q),P)) ∘Nv
      (ProfAssociatorFctN ((S,T (R,Q)),P) ∘Nv
        fmap (π1F T P) (ProfAssociatorFctN ((S,R),Q)))).
Proof.
  pose (i := ((a S R (T (Q,P))).1;
    NatIso_is_iso (a S R (T (Q,P))).1 (a S R (T (Q,P))).2)).
  pose (j := ((a (T (S,R)) Q P).1;
    NatIso_is_iso (a (T (S,R)) Q P).1 (a (T (S,R)) Q P).2)).
  pose (k := (fmap (π2F T S) (a R Q P).1;
    functor_is_iso (π2F T S) (a R Q P).1
      (NatIso_is_iso (a R Q P).1 (a R Q P).2))).
  pose (l := ((a S (T (R,Q)) P).1;
    NatIso_is_iso (a S (T (R,Q)) P).1 (a S (T (R,Q)) P).2)).
  pose (m := (fmap (π1F T P) (a S R Q).1;
    functor_is_iso (π1F T P) (a S R Q).1
      (NatIso_is_iso (a S R Q).1 (a S R Q).2))).
  assert (H : @HomEq K _ _ (j.1 ∘ i.1) (m.1 ∘ (l.1 ∘ k.1))).
  { intros [X V] v.
    exact (@profunctor_pentagon C C C C C S R Q P
      (HC Q P) (HC R Q) (HC S R)
      (HC R (T (Q,P))) (HC (T (R,Q)) P)
      (HC S (T (R,Q))) (HC (T (S,R)) Q)
      (HC S (T (R,T (Q,P)))) (HC (T (S,R)) (T (Q,P)))
      (HC S (T (T (R,Q),P))) (HC (T (S,T (R,Q))) P)
      (HC (T (T (S,R),Q)) P) (X,V) v). }
  pose proof (@iso_pentagon_inv K _ _ _ _ _ i j k l m H) as E.
  intros [X V] v. exact (E (X,V) v).
Defined.

(** ** Hom Units and Monoidal Assembly

    The base Hom carrier and equality must now fit the independent value
    bounds. Keep its Hom profunctor as the unit and the supplied composite
    family as the tensor. The original unit inverses and accepted triangle
    determine all remaining structure; no new global model is installed. *)

(** ** Hom 单位与幺半装配

    基范畴的 Hom 载体和相等现在须分别容纳于独立值界。单位仍为其 Hom
    profunctor，张量仍使用给定复合族。原单位逆和已验收三角形确定其余结构，
    不安装新的全局模型。 *)

Section MonoidalAssembly.

Let I
  : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _})
  := HomProf C.

(** The original left unitors form a natural transformation on the
    endoprofunctor category by their existing input naturality. *)

(** 原左单位子由已有输入自然性组成自 profunctor 范畴上的自然变换。 *)

Program Definition ProfLeftUnitorFctN
  : π2F T I ⇒ IdF
  :=
  {|nt P := @ProfLeftUnitorN C C P (HC I P)
  |}.
Next Obligation.
  exact (@prof_left_unitor_natural C C X Y f (HC I X) (HC I Y)).
Defined.

(** Retain the original identity-insertion inverses at every profunctor. *)

(** 在每个 profunctor 处保留原恒等插入逆。 *)

Definition ProfLeftUnitorFct
  : π2F T I ≅N IdF.
Proof.
  exists ProfLeftUnitorFctN. intros P.
  exact (NatIso_is_iso _ (@ProfLeftUnitor C C P (HC I P)).2).
Defined.

(** The right unitors form the corresponding natural family. *)

(** 右单位子组成相应的自然族。 *)

Program Definition ProfRightUnitorFctN
  : π1F T I ⇒ IdF
  :=
  {|nt P := @ProfRightUnitorN C C P (HC P I)
  |}.
Next Obligation.
  exact (@prof_right_unitor_natural C C X Y f (HC X I) (HC Y I)).
Defined.

(** Its chosen inverses are again the original identity insertions. *)

(** 其选定逆仍为原恒等插入。 *)

Definition ProfRightUnitorFct
  : π1F T I ≅N IdF.
Proof.
  exists ProfRightUnitorFctN. intros P.
  exact (NatIso_is_iso _ (@ProfRightUnitor C C P (HC P I)).2).
Defined.

(** Moving the original associator across its triangle yields precisely
    the triangle for its selected inverse. The unitors are unchanged. *)

(** 将原结合子移过其三角形，恰好得到选定逆的三角形；单位子保持不变。 *)

Lemma prof_monoidal_triangle (Q P : @Ob K)
  : (fmap (π2F T Q) (ProfLeftUnitorFctN P) ∘Nv
      ProfAssociatorFctN ((Q,I),P)) ≈N
    fmap (π1F T P) (ProfRightUnitorFctN Q).
Proof.
  pose (i := ((a Q I P).1; NatIso_is_iso (a Q I P).1 (a Q I P).2)).
  assert (H : @HomEq K _ _
    (fmap (π1F T P) (ProfRightUnitorFctN Q) ∘ i.1)
    (fmap (π2F T Q) (ProfLeftUnitorFctN P))).
  { intros [X V] v.
    exact (@profunctor_triangle C C C Q P
      (HC I P) (HC Q I) (HC Q (T (I,P))) (HC (T (Q,I)) P)
      (HC Q P) (X,V) v). }
  pose proof (fst (@iso_move_r K _ _ _ i
    (fmap (π1F T P) (ProfRightUnitorFctN Q))
    (fmap (π2F T Q) (ProfLeftUnitorFctN P))) H) as E.
  symmetry. intros [X V] v. exact (E (X,V) v).
Defined.

(** Assemble the existing bifunctor, Hom unit and structural inverses.
    Interchange and separate naturality come from the generic constructor. *)

(** 装配已有双函子、Hom 单位和结构逆；交换律及分别自然性来自一般构造器。 *)

Definition ProfMonoidal
  : MonoidalCat K.
Proof.
  refine (BifunctorMonoidal T I (ProfAssociatorFct)
    ProfLeftUnitorFct ProfRightUnitorFct _ _).
  - intros S R Q P. exact (prof_monoidal_pentagon S R Q P).
  - intros Q P. exact (prof_monoidal_triangle Q P).
Defined.

(** The derived tensor map agrees with the original composite input map
    in natural equality, without equality of functor or law records. *)

(** 导出的张量映射在自然相等下等于原复合输入映射，不要求函子或定律记录相等。 *)

Lemma prof_monoidal_map
    {Q Q' P P' : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _})}
    (β : Q ⇒ Q') (α : P ⇒ P')
  : @tensor_map K ProfMonoidal Q Q' P P' β α ≈N
      @ProfCompMapN C C C Q Q' P P' (HC Q P) (HC Q' P') β α.
Proof. exact (@bifunctor_sequence K T Q Q' P P' β α). Defined.

(** Identity components compare the reconstructed tensor functor with
    the supplied composition bifunctor, keeping all selected coends. *)

(** 恒等分量比较重建张量函子与给定复合双函子，保留全部选定 coend。 *)

Definition ProfTensorIso
  : tensorF ProfMonoidal ≅N T.
Proof.
  unfold ProfMonoidal. exact (@bifunctor_monoidal_iso K T).
Defined.

End MonoidalAssembly.

End Associativity.
