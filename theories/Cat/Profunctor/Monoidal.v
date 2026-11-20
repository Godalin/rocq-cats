From Cats Require Export
  Cat.Profunctor.Coherence.
From Cats Require Import
  Cat.Core
  Cat.Monoidal.Bifct
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
Context `(HC : ∀ Q P : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _}),
    HasProfComp C C C Q P).

Let K
  : Cat
  := FctCat ((C^op) ×C C) (SetCat@{u p _ _ _ _ _}).

(** The tensor retains the chosen composites and their original input
    maps. All three functor laws are inherited from [ProfCompF]. *)

(** 张量保留选定复合及其原输入映射；三条函子律均继承自 [ProfCompF]。 *)

Program Definition ProfTensorF
  : Fct (K ×C K) K
  :=
  {|fobj (QP : @Ob (K ×C K)) := fst QP ∘Pr snd QP
  ; fmap QP QP' βα := ProfCompMapN (fst βα) (snd βα)
  ; isFct :=
      {|fmap_proper := @fmap_proper _ _ _ _ (isFct (ProfCompF C C C HC))
      ; fmap_id := @fmap_id _ _ _ _ (isFct (ProfCompF C C C HC))
      ; fmap_comp := @fmap_comp _ _ _ _ (isFct (ProfCompF C C C HC))
      |}
  |}.

(** The inverse reassociation is natural on triples of endoprofunctors. *)

(** 逆重结合在自 profunctor 三元组上自然。 *)

Program Definition ProfAssociatorFctN
  : Tensor3LF ProfTensorF ⇒ Tensor3RF ProfTensorF
  :=
  {|nt '((R,Q),P) := @ProfunctorAssociatorInvN C C C C R Q P
      (HC Q P) (HC R Q) (HC R (Q ∘Pr P)) (HC (R ∘Pr Q) P)
  |}.
Next Obligation.
  destruct X as [[R Q] P], Y as [[R' Q'] P'], f as [[γ β] α].
  exact (@profunctor_associator_inv_natural C C C C R R' Q Q' P P'
    (HC Q P) (HC R Q) (HC R (Q ∘Pr P)) (HC (R ∘Pr Q) P)
    (HC Q' P') (HC R' Q') (HC R' (Q' ∘Pr P')) (HC (R' ∘Pr Q') P')
    α β γ).
Qed.

(** Reversing the same object isomorphism supplies the forward
    reassociation as its computed inverse. *)

(** 反转同一个对象同构，以原正向重结合作为计算逆。 *)

Definition ProfAssociatorFct
  : Tensor3LF ProfTensorF ≅N Tensor3RF ProfTensorF.
Proof.
  exists ProfAssociatorFctN. intros [[R Q] P].
  pose (i := @ProfunctorAssociator C C C C R Q P
    (HC Q P) (HC R Q) (HC R (Q ∘Pr P)) (HC (R ∘Pr Q) P)).
  exact (nat_iso_is_iso (i.1 ^-1N i.2) (nat_inv_iso i.1 i.2)).
Defined.

Let ai (R Q P : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _}))
  : (R ∘Pr Q) ∘Pr P ⇒ R ∘Pr (Q ∘Pr P)
  := @ProfunctorAssociatorInvN C C C C R Q P
      (HC Q P) (HC R Q) (HC R (Q ∘Pr P)) (HC (R ∘Pr Q) P).

(** The monoidal pentagon is the inverse of the existing path equation.
    The two whiskered inverses come from ordinary functoriality. *)

(** 幺半五边形为已有路径方程的逆；两个须化后的逆来自普通函子性。 *)

Lemma prof_monoidal_pentagon
    (S R Q P : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _}))
  : (ai S R (Q ∘Pr P) ∘Nv ai (S ∘Pr R) Q P) ≈N
    (ProfCompMapN (IdN (F := S)) (ai R Q P) ∘Nv
      ((ai S (R ∘Pr Q) P) ∘Nv
        ProfCompMapN (ai S R Q) (IdN (F := P)))).
Proof.
  pose (i := @ProfunctorAssociator C C C C S R (Q ∘Pr P)
    (HC R (Q ∘Pr P)) (HC S R)
    (HC S (R ∘Pr (Q ∘Pr P))) (HC (S ∘Pr R) (Q ∘Pr P))).
  pose (j := @ProfunctorAssociator C C C C (S ∘Pr R) Q P
    (HC Q P) (HC (S ∘Pr R) Q)
    (HC (S ∘Pr R) (Q ∘Pr P)) (HC ((S ∘Pr R) ∘Pr Q) P)).
  pose (k0 := @ProfunctorAssociator C C C C R Q P
    (HC Q P) (HC R Q) (HC R (Q ∘Pr P)) (HC (R ∘Pr Q) P)).
  pose (l := @ProfunctorAssociator C C C C S (R ∘Pr Q) P
    (HC (R ∘Pr Q) P) (HC S (R ∘Pr Q))
    (HC S ((R ∘Pr Q) ∘Pr P)) (HC (S ∘Pr (R ∘Pr Q)) P)).
  pose (m0 := @ProfunctorAssociator C C C C S R Q
    (HC R Q) (HC S R) (HC S (R ∘Pr Q)) (HC (S ∘Pr R) Q)).
  pose (hs := λ XY, (@iso_refl SetCat (S XY)).2).
  pose (hp := λ XY, (@iso_refl SetCat (P XY)).2).
  pose (kN := ProfCompMapN (IdN (F := S)) k0.1).
  pose (mN := ProfCompMapN m0.1 (IdN (F := P))).
  pose (hk := prof_comp_map_iso (IdN (F := S)) k0.1 hs k0.2).
  pose (hm := prof_comp_map_iso m0.1 (IdN (F := P)) m0.2 hp).
  assert (Ek : ProfCompMapN ((IdN (F := S)) ^-1N hs)
      (k0.1 ^-1N k0.2) ≈N ProfCompMapN (IdN (F := S)) (ai R Q P)).
  { apply prof_comp_map_proper; intros [X V] v; reflexivity. }
  assert (Em : ProfCompMapN (m0.1 ^-1N m0.2)
      ((IdN (F := P)) ^-1N hp) ≈N
      ProfCompMapN (ai S R Q) (IdN (F := P))).
  { apply prof_comp_map_proper; intros [X V] v; reflexivity. }
  intros [X V] v.
  pose proof (@iso_pentagon_inv SetCat _ _ _ _ _
    (i.1 (X,V); i.2 (X,V)) (j.1 (X,V); j.2 (X,V))
    (kN (X,V); hk (X,V)) (l.1 (X,V); l.2 (X,V))
    (mN (X,V); hm (X,V))) as invert.
  assert (H : j.1 (X,V) ∘ i.1 (X,V) ≈
      mN (X,V) ∘ (l.1 (X,V) ∘ kN (X,V))).
  { intros w.
    exact (@profunctor_pentagon C C C C C S R Q P
      (HC Q P) (HC R Q) (HC S R)
      (HC R (Q ∘Pr P)) (HC (R ∘Pr Q) P)
      (HC S (R ∘Pr Q)) (HC (S ∘Pr R) Q)
      (HC S (R ∘Pr (Q ∘Pr P))) (HC (S ∘Pr R) (Q ∘Pr P))
      (HC S ((R ∘Pr Q) ∘Pr P)) (HC (S ∘Pr (R ∘Pr Q)) P)
      (HC ((S ∘Pr R) ∘Pr Q) P) (X,V) w). }
  pose proof (invert H) as Hinv.
  cbv beta iota zeta delta [ai i j l kN mN hk hm k0 m0
    ProfunctorAssociatorInvN ProfunctorAssociator InvN
    prof_comp_map_iso projT1 projT2 fst snd nt comp HomEq SetCat
    FunS FunEq carrier_equiv comp_resp func] in Hinv |- *.
  etransitivity; [exact (Hinv v) |].
  etransitivity.
  - apply func_proper. apply func_proper. exact (Em (X,V) v).
  - exact (Ek (X,V) ((ai S (R ∘Pr Q) P) (X,V)
      (ProfCompMapN (ai S R Q) (IdN (F := P)) (X,V) v))).

Defined.

End Associativity.

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
Universes u p.
Context {C : Cat}.
Context `(HC : ∀ Q P : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _}),
    HasProfComp C C C Q P).

Let K
  : Cat
  := FctCat ((C^op) ×C C) (SetCat@{u p _ _ _ _ _}).

(** Keep the same selected composites and input maps at the ambient
    levels of this assembly. The general composition bifunctor again
    supplies all functor laws; no additional coend is selected. *)

(** 在本次装配的环境层级保留同一选定复合及输入映射。一般复合双函子仍提供
    全部函子律，不再选择额外的 coend。 *)

Local Program Definition AssemblyTensorF
  : Fct (K ×C K) K
  :=
  {|fobj (QP : @Ob (K ×C K)) := fst QP ∘Pr snd QP
  ; fmap QP QP' βα := ProfCompMapN (fst βα) (snd βα)
  ; isFct :=
      {|fmap_proper := @fmap_proper _ _ _ _ (isFct (ProfCompF C C C HC))
      ; fmap_id := @fmap_id _ _ _ _ (isFct (ProfCompF C C C HC))
      ; fmap_comp := @fmap_comp _ _ _ _ (isFct (ProfCompF C C C HC))
      |}
  |}.

Let I
  : @Ob K
  := HomProf C.

(** The original left unitors form a natural transformation on the
    endoprofunctor category by their existing input naturality. *)

(** 原左单位子由已有输入自然性组成自 profunctor 范畴上的自然变换。 *)

Program Definition ProfLeftUnitorFctN
  : AtLF AssemblyTensorF I ⇒ IdF
  :=
  {|nt P := @ProfLeftUnitorN C C P (HC I P)
  |}.
Next Obligation.
  exact (@prof_left_unitor_natural C C X Y f (HC I X) (HC I Y)).
Qed.

(** Retain the original identity-insertion inverses at every profunctor. *)

(** 在每个 profunctor 处保留原恒等插入逆。 *)

Definition ProfLeftUnitorFct
  : AtLF AssemblyTensorF I ≅N IdF.
Proof.
  exists ProfLeftUnitorFctN. intros P.
  exact (nat_iso_is_iso _ (@ProfLeftUnitor C C P (HC I P)).2).
Defined.

(** The right unitors form the corresponding natural family. *)

(** 右单位子组成相应的自然族。 *)

Program Definition ProfRightUnitorFctN
  : AtRF AssemblyTensorF I ⇒ IdF
  :=
  {|nt P := @ProfRightUnitorN C C P (HC P I)
  |}.
Next Obligation.
  exact (@prof_right_unitor_natural C C X Y f (HC X I) (HC Y I)).
Qed.

(** Its chosen inverses are again the original identity insertions. *)

(** 其选定逆仍为原恒等插入。 *)

Definition ProfRightUnitorFct
  : AtRF AssemblyTensorF I ≅N IdF.
Proof.
  exists ProfRightUnitorFctN. intros P.
  exact (nat_iso_is_iso _ (@ProfRightUnitor C C P (HC P I)).2).
Defined.

(** Moving the original associator across its triangle yields precisely
    the triangle for its selected inverse. The unitors are unchanged. *)

(** 将原结合子移过其三角形，恰好得到选定逆的三角形；单位子保持不变。 *)

Lemma prof_monoidal_triangle
    (Q P : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _}))
  : (ProfCompMapN (IdN (F := Q)) (ProfLeftUnitorN P) ∘Nv
      ProfAssociatorFctN (C := C) HC ((Q,I),P)) ≈N
    ProfCompMapN (ProfRightUnitorN Q) (IdN (F := P)).
Proof.
  pose (i := @ProfunctorAssociator C C C C Q I P
    (HC I P) (HC Q I) (HC Q (I ∘Pr P)) (HC (Q ∘Pr I) P)).
  symmetry.
  exact (fst (@iso_move_r K _ _ _ (i.1; nat_iso_is_iso i.1 i.2)
    (ProfCompMapN (ProfRightUnitorN Q) (IdN (F := P)))
    (ProfCompMapN (IdN (F := Q)) (ProfLeftUnitorN P)))
    (@profunctor_triangle C C C Q P
      (HC I P) (HC Q I) (HC Q (I ∘Pr P)) (HC (Q ∘Pr I) P)
      (HC Q P))).
Defined.

(** Assemble the existing bifunctor, Hom unit and structural inverses.
    Interchange and separate naturality come from the generic constructor. *)

(** 装配已有双函子、Hom 单位和结构逆；交换律及分别自然性来自一般构造器。 *)

Definition ProfMonoidal
  : HasMonoidal K.
Proof.
  refine (BifctHasMonoidal AssemblyTensorF I (ProfAssociatorFct (C := C) HC)
    ProfLeftUnitorFct ProfRightUnitorFct _ _).
  - exact (prof_monoidal_pentagon (C := C) HC).
  - exact prof_monoidal_triangle.
Defined.

(** The derived tensor map agrees with the original composite input map
    in natural equality, without equality of functor or law records. *)

(** 导出的张量映射在自然相等下等于原复合输入映射，不要求函子或定律记录相等。 *)

Lemma prof_monoidal_map
    {Q Q' P P' : Fct ((C^op) ×C C) (SetCat@{u p _ _ _ _ _})}
    (β : Q ⇒ Q') (α : P ⇒ P')
  : tensor_map (IM := isMagmoidal ProfMonoidal)
      (X := Q) (X' := Q') (Y := P) (Y' := P') β α ≈N
      @ProfCompMapN C C C Q Q' P P' (HC Q P) (HC Q' P') β α.
Proof. exact (@bifct_sequence K AssemblyTensorF Q Q' P P' β α). Defined.

(** Identity components compare the reconstructed tensor functor with
    the original composition bifunctor. Its naturality is the preceding
    map comparison, rather than equality of functor law records. *)

(** 恒等分量比较重建张量函子与原复合双函子；其自然性来自前述映射比较，
    不要求函子定律记录相等。 *)

Program Definition ProfTensorN
  : tensorF (isMagmoidal ProfMonoidal) ⇒ ProfCompF C C C HC
  :=
  {|nt p := _
  |}.
Next Obligation. destruct p as [Q P]. exact IdN. Defined.
Next Obligation.
  destruct X as [Q P], Y as [Q' P'], f as [β α].
  intros [X V] v. exact (prof_monoidal_map β α (X,V) v).
Defined.

(** The comparison and its inverse compute to identity transformations
    on each selected composite, preserving every chosen coend. *)

(** 比较及其逆在每个选定复合上计算为恒等变换，保留全部选定 coend。 *)

Definition ProfTensorIso
  : tensorF (isMagmoidal ProfMonoidal) ≅N ProfCompF C C C HC.
Proof.
  exists ProfTensorN. intros [Q P].
  exists IdN. split; intros [X V] v; reflexivity.
Defined.

End MonoidalAssembly.
