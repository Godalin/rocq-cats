From Cats Require Export
  Cat.Profunctor.Iterated.
From Cats Require Import
  Cat.Core
  Cat.Profunctor.ComposeMap
  Cat.Isomorphism
  Instance.Set.Core
  Instance.Set.Product.

Local Open Scope prof_scope.

(** * Reassociation of Profunctor Composition

    Descend the same ordered triple through the other parenthesization.
    The two original coend mediators are inverse on whole coends by double
    generator distinction. Only the indicated choices are used; coherence
    and strength remain separate constructions. *)

(** * Profunctor 复合的重结合

    将同一个有序三元组沿另一种括号方式下降。由双重生成元区分律，两个原 coend
    中介在整个 coend 上互逆。只使用所指的选择，相干性和强度仍是另外的构造。 *)

(** ** Left-Associated Triple Insertion

    Choose the first inner composition family and just one outer coend.
    The two original injections balance at both intermediate indices. *)

(** ** 左结合三元插入

    选择第一个内层复合族和单个外层 coend；两个原注入在两个中间指标处均平衡。 *)

Section LeftInsertion.
Universes u p.
Context {C D E B : Cat}.
Context (R : Fct ((E^op) ×C B) (SetCat@{u p _ _ _ _ _})).
Context (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})).
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context `{HI : !HasProfComp C D E Q P}.
Context {X : @Ob C} {W : @Ob B}.
Context `{HO : !HasCoend SetCat
    (ProfCompKernel R (Q ∘Pr P) X W)}.

(** Insert the first pair, then pair its class with the last value. *)

(** 先插入第一对，再将其类与最后一个值配对。 *)

Program Definition ProfunctorTripleLeftInjection
  : ProfunctorTripleCowedge R Q P X W
      (coend[ProfCompKernel R (Q ∘Pr P) X W])
  :=
  {|triple_cowedge_leg Y Z :=
      {|func xyz := ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z
          (ιPr[Q; P; Y] (fst xyz),snd xyz)
      |}
  |}.
Next Obligation.
  intros [xy z] [xy' z'] [H K].
  apply func_proper. split; [apply func_proper; exact H | exact K].
Defined.
Next Obligation.
  apply func_proper. split; [| reflexivity].
  exact (prof_comp_gluing Q P h x y).
Defined.
Next Obligation.
  transitivity (ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z'
    (rmap[Q ∘Pr P; h] (ιPr[Q; P; Y] (x,y)),z)).
  - exact (prof_comp_cowedge_gluing R (Q ∘Pr P)
      ιcoend[ProfCompKernel R (Q ∘Pr P) X W] h
      (ιPr[Q; P; Y] (x,y)) z).
  - apply func_proper. split; [| reflexivity].
    exact (profunctor_comp_rmap_inject Q P h Y x y).
Defined.

End LeftInsertion.

(** ** Right-Associated Triple Insertion

    Choose the last inner composition family and one outer coend. Insert
    the last pair first. Its two balance laws reuse the same original
    cowedge equations, without another universal-property construction. *)

(** ** 右结合三元插入

    选择最后一个内层复合族和单个外层 coend，先插入最后一对。两个平衡律复用
    相同的原余楔方程，不另建泛性质构造。 *)

Section RightInsertion.
Universes u p.
Context {C D E B : Cat}.
Context (R : Fct ((E^op) ×C B) (SetCat@{u p _ _ _ _ _})).
Context (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})).
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context `{HI : !HasProfComp D E B R Q}.
Context {X : @Ob C} {W : @Ob B}.
Context `{HO : !HasCoend SetCat
    (ProfCompKernel (R ∘Pr Q) P X W)}.

(** Pair the first value with the class of the last pair. *)

(** 将第一个值与最后一对的类配对。 *)

Program Definition ProfunctorTripleRightInjection
  : ProfunctorTripleCowedge R Q P X W
      (coend[ProfCompKernel (R ∘Pr Q) P X W])
  :=
  {|triple_cowedge_leg Y Z :=
      {|func xyz := ιcoend[ProfCompKernel (R ∘Pr Q) P X W] Y
          (fst (fst xyz),ιPr[R; Q; Z] (snd (fst xyz),snd xyz))
      |}
  |}.
Next Obligation.
  intros [[x y] z] [[x' y'] z'] [[H K] L].
  apply func_proper. split; [exact H |].
  apply func_proper. exact (K,L).
Defined.
Next Obligation.
  transitivity (ιcoend[ProfCompKernel (R ∘Pr Q) P X W] Y
    (x,lmap[R ∘Pr Q; h] (ιPr[R; Q; Z] (y,z)))).
  - apply func_proper. split; [reflexivity |].
    symmetry. exact (profunctor_comp_lmap_inject R Q h Z y z).
  - exact (prof_comp_cowedge_gluing (R ∘Pr Q) P
      ιcoend[ProfCompKernel (R ∘Pr Q) P X W] h
      x (ιPr[R; Q; Z] (y,z))).
Defined.
Next Obligation.
  apply func_proper. split; [reflexivity |].
  exact (prof_comp_gluing R Q h y z).
Defined.

End RightInsertion.

(** ** Fixed-Endpoint Reassociation

    Keep the two inner composition families. At fixed outer objects only
    two individual outer coends are required. Descent gives both directions;
    their inverse equations compare every outgoing value by double generators. *)

(** ** 固定端点的重结合

    保持两个内层复合族。固定外部对象时，只要求两个单独的外层 coend。下降
    给出两个方向，互逆方程通过双重生成元比较全部出射值。 *)

Section FixedReassociation.
Universes u p.
Context {C D E B : Cat}.
Context (R : Fct ((E^op) ×C B) (SetCat@{u p _ _ _ _ _})).
Context (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})).
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context `{HPQ : !HasProfComp C D E Q P}.
Context `{HQR : !HasProfComp D E B R Q}.
Context {X : @Ob C} {W : @Ob B}.
Context `{HL : !HasCoend SetCat
    (ProfCompKernel R (Q ∘Pr P) X W)}.
Context `{HR : !HasCoend SetCat
    (ProfCompKernel (R ∘Pr Q) P X W)}.

(** Reassociate by descending the right-associated triple insertion. *)

(** 下降右结合三元插入，得到重结合映射。 *)

Definition profunctor_associator
  : coend[ProfCompKernel R (Q ∘Pr P) X W] →r
      coend[ProfCompKernel (R ∘Pr Q) P X W]
  := profunctor_triple_left_desc R Q P (ProfunctorTripleRightInjection R Q P).

(** Reverse the same construction by descending the left insertion. *)

(** 下降左插入，反向使用同一个构造。 *)

Definition profunctor_associator_inv
  : coend[ProfCompKernel (R ∘Pr Q) P X W] →r
      coend[ProfCompKernel R (Q ∘Pr P) X W]
  := profunctor_triple_right_desc R Q P (ProfunctorTripleLeftInjection R Q P).

(** Reassociation retains all three original values and their order. *)

(** 重结合保留全部三个原值及其顺序。 *)

Lemma profunctor_associator_β (Y : @Ob D) (Z : @Ob E)
    (x : P (X,Y)) (y : Q (Y,Z)) (z : R (Z,W))
  : profunctor_associator
      (ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z
        (ιPr[Q; P; Y] (x,y),z)) ≈S
      ιcoend[ProfCompKernel (R ∘Pr Q) P X W] Y
        (x,ιPr[R; Q; Z] (y,z)).
Proof.
  exact (profunctor_triple_left_β R Q P
    (ProfunctorTripleRightInjection R Q P) Y Z x y z).
Defined.

(** Reverse reassociation has the opposite original-generator equation. *)

(** 反向重结合满足方向相反的原生成元方程。 *)

Lemma profunctor_associator_inv_β (Y : @Ob D) (Z : @Ob E)
    (x : P (X,Y)) (y : Q (Y,Z)) (z : R (Z,W))
  : profunctor_associator_inv
      (ιcoend[ProfCompKernel (R ∘Pr Q) P X W] Y
        (x,ιPr[R; Q; Z] (y,z))) ≈S
      ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z
        (ιPr[Q; P; Y] (x,y),z).
Proof.
  exact (profunctor_triple_right_β R Q P
    (ProfunctorTripleLeftInjection R Q P) Y Z x y z).
Defined.

(** The reverse is a left inverse on the whole left-associated coend. *)

(** 反向映射在整个左结合 coend 上为左逆。 *)

Lemma profunctor_associator_inv_l
  : (profunctor_associator_inv ∘r profunctor_associator) ≈f id_resp.
Proof.
  apply (profunctor_triple_left_hom_ext R Q P). intros Y Z x y z.
  transitivity (profunctor_associator_inv
    (ιcoend[ProfCompKernel (R ∘Pr Q) P X W] Y
      (x,ιPr[R; Q; Z] (y,z)))).
  - exact (@func_proper _ _ profunctor_associator_inv _ _
      (profunctor_associator_β Y Z x y z)).
  - exact (profunctor_associator_inv_β Y Z x y z).
Defined.

(** The same double distinction proves the whole right-coend inverse law. *)

(** 同一个双重区分律证明整个右 coend 上的互逆律。 *)

Lemma profunctor_associator_inv_r
  : (profunctor_associator ∘r profunctor_associator_inv) ≈f id_resp.
Proof.
  apply (profunctor_triple_right_hom_ext R Q P). intros Y Z x y z.
  transitivity (profunctor_associator
    (ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z
      (ιPr[Q; P; Y] (x,y),z))).
  - exact (@func_proper _ _ profunctor_associator _ _
      (profunctor_associator_inv_β Y Z x y z)).
  - exact (profunctor_associator_β Y Z x y z).
Defined.

(** These specified inverse equations package the fixed-endpoint isomorphism. *)

(** 这些指定相等下的互逆方程打包固定端点同构。 *)

Definition ProfunctorAssociatorIso
  : coend[ProfCompKernel R (Q ∘Pr P) X W] ≅[SetCat]
      coend[ProfCompKernel (R ∘Pr Q) P X W].
Proof.
  exists profunctor_associator, profunctor_associator_inv.
  split; [exact profunctor_associator_inv_l | exact profunctor_associator_inv_r].
Defined.

End FixedReassociation.

(** ** Outer Boundaries of Triple Generators

    Families of outer coends now give the two composite profunctors. Their
    boundary maps act only on the first and last values of each triple;
    the intermediate indices and middle value remain unchanged. *)

(** ** 三元生成元的外部边界

    外层 coend 族现在给出两个复合 profunctor。其边界映射只作用于三元组的
    第一个和最后一个值，中间指标和中间值保持不变。 *)

Section TripleBoundaries.
Universes u p.
Context {C D E B : Cat}.
Context (R : Fct ((E^op) ×C B) (SetCat@{u p _ _ _ _ _})).
Context (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})).
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context `{HPQ : !HasProfComp C D E Q P}.
Context `{HQR : !HasProfComp D E B R Q}.
Context `{HL : !HasProfComp C E B R (Q ∘Pr P)}.
Context `{HR : !HasProfComp C D B (R ∘Pr Q) P}.

(** The left-associated boundary acts on the first and third factors. *)

(** 左结合边界作用于第一个与第三个因子。 *)

Lemma profunctor_triple_left_boundary
    {X X' : @Ob C} {W W' : @Ob B} (f : Hom X' X) (g : Hom W W')
    (Y : @Ob D) (Z : @Ob E)
    (x : P (X,Y)) (y : Q (Y,Z)) (z : R (Z,W))
  : dimap[R ∘Pr (Q ∘Pr P); f; g]
      (ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z
        (ιPr[Q; P; Y] (x,y),z)) ≈S
      ιcoend[ProfCompKernel R (Q ∘Pr P) X' W'] Z
        (ιPr[Q; P; Y] (lmap[P; f] x,y),rmap[R; g] z).
Proof.
  transitivity (ιcoend[ProfCompKernel R (Q ∘Pr P) X' W'] Z
    (lmap[Q ∘Pr P; f] (ιPr[Q; P; Y] (x,y)),rmap[R; g] z)).
  - exact (coend_map_β (ProfCompBoundaryN R (Q ∘Pr P) f g)
      Z (ιPr[Q; P; Y] (x,y),z)).
  - apply func_proper. split; [| reflexivity].
    exact (profunctor_comp_lmap_inject Q P f Y x y).
Defined.

(** The other parenthesization has the same two outer actions. *)

(** 另一种括号方式具有相同的两个外端作用。 *)

Lemma profunctor_triple_right_boundary
    {X X' : @Ob C} {W W' : @Ob B} (f : Hom X' X) (g : Hom W W')
    (Y : @Ob D) (Z : @Ob E)
    (x : P (X,Y)) (y : Q (Y,Z)) (z : R (Z,W))
  : dimap[(R ∘Pr Q) ∘Pr P; f; g]
      (ιcoend[ProfCompKernel (R ∘Pr Q) P X W] Y
        (x,ιPr[R; Q; Z] (y,z))) ≈S
      ιcoend[ProfCompKernel (R ∘Pr Q) P X' W'] Y
        (lmap[P; f] x,ιPr[R; Q; Z] (y,rmap[R; g] z)).
Proof.
  transitivity (ιcoend[ProfCompKernel (R ∘Pr Q) P X' W'] Y
    (lmap[P; f] x,rmap[R ∘Pr Q; g] (ιPr[R; Q; Z] (y,z)))).
  - exact (coend_map_β (ProfCompBoundaryN (R ∘Pr Q) P f g)
      Y (x,ιPr[R; Q; Z] (y,z))).
  - apply func_proper. split; [reflexivity |].
    exact (profunctor_comp_rmap_inject R Q g Z y z).
Defined.

(** Double-generator distinction makes reassociation natural in both outer
    objects, retaining the original mediators as its components. *)

(** 双重生成元区分律使重结合关于两个外部对象自然，并保留原中介作为分量。 *)

Program Definition ProfunctorAssociatorN
  : R ∘Pr (Q ∘Pr P) ⇒ (R ∘Pr Q) ∘Pr P
  :=
  {|nt '(X,W) := @profunctor_associator C D E B R Q P HPQ HQR X W
      (@hasProfCompCoend C E B R (Q ∘Pr P) HL X W)
      (@hasProfCompCoend C D B (R ∘Pr Q) P HR X W)
  |}.
Next Obligation.
  destruct X as [X W], Y as [X' W'], f as [f g].
  change ((@profunctor_associator C D E B R Q P HPQ HQR X' W'
    (@hasProfCompCoend C E B R (Q ∘Pr P) HL X' W')
    (@hasProfCompCoend C D B (R ∘Pr Q) P HR X' W') ∘r
    dimap[R ∘Pr (Q ∘Pr P); f; g]) ≈f
    (dimap[(R ∘Pr Q) ∘Pr P; f; g] ∘r
      @profunctor_associator C D E B R Q P HPQ HQR X W
        (@hasProfCompCoend C E B R (Q ∘Pr P) HL X W)
        (@hasProfCompCoend C D B (R ∘Pr Q) P HR X W))).
  apply (@profunctor_triple_left_hom_ext C D E B R Q P HPQ X W
    (@hasProfCompCoend C E B R (Q ∘Pr P) HL X W)
    (((R ∘Pr Q) ∘Pr P) (X',W'))).
  intros Y Z x y z.
  transitivity (@profunctor_associator C D E B R Q P HPQ HQR X' W'
    (@hasProfCompCoend C E B R (Q ∘Pr P) HL X' W')
    (@hasProfCompCoend C D B (R ∘Pr Q) P HR X' W')
    (ιcoend[ProfCompKernel R (Q ∘Pr P) X' W'] Z
      (ιPr[Q; P; Y] (lmap[P; f] x,y),rmap[R; g] z))).
  - exact (@func_proper _ _
      (@profunctor_associator C D E B R Q P HPQ HQR X' W'
        (@hasProfCompCoend C E B R (Q ∘Pr P) HL X' W')
        (@hasProfCompCoend C D B (R ∘Pr Q) P HR X' W')) _ _
      (profunctor_triple_left_boundary f g Y Z x y z)).
  - transitivity (ιcoend[ProfCompKernel (R ∘Pr Q) P X' W'] Y
      (lmap[P; f] x,ιPr[R; Q; Z] (y,rmap[R; g] z))).
    + exact (profunctor_associator_β R Q P Y Z
        (lmap[P; f] x) y (rmap[R; g] z)).
    + transitivity (dimap[(R ∘Pr Q) ∘Pr P; f; g]
        (ιcoend[ProfCompKernel (R ∘Pr Q) P X W] Y
          (x,ιPr[R; Q; Z] (y,z)))).
      * symmetry. exact (profunctor_triple_right_boundary f g Y Z x y z).
      * exact (@func_proper _ _ (dimap[(R ∘Pr Q) ∘Pr P; f; g]) _ _
          (symmetry (profunctor_associator_β R Q P Y Z x y z))).
Defined.

(** The two whole-coend inverse equations give the natural isomorphism;
    triangle and pentagon coherence are not part of this packaging. *)

(** 两个整个 coend 上的互逆方程给出自然同构；此打包不包含三角形和五边形相干性。 *)

Definition ProfunctorAssociator
  : R ∘Pr (Q ∘Pr P) ≅N (R ∘Pr Q) ∘Pr P.
Proof.
  exists ProfunctorAssociatorN. intros [X W].
  exists (@profunctor_associator_inv C D E B R Q P HPQ HQR X W
    (@hasProfCompCoend C E B R (Q ∘Pr P) HL X W)
    (@hasProfCompCoend C D B (R ∘Pr Q) P HR X W)).
  split; [exact (profunctor_associator_inv_l R Q P)
    | exact (profunctor_associator_inv_r R Q P)].
Defined.

(** The inverse natural transformation is computed by the general inverse
    construction from those same selected pointwise inverses. *)

(** 逆自然变换由一般逆构造从同一组选定逐点逆计算得到。 *)

Definition ProfunctorAssociatorInvN
  : (R ∘Pr Q) ∘Pr P ⇒ R ∘Pr (Q ∘Pr P)
  := let i := ProfunctorAssociator in i.1 ^-1N i.2.

End TripleBoundaries.

(** ** Naturality in the Three Input Profunctors

    Give the four choices at each endpoint. Transform each original value
    in order; the two nested coend maps commute with reassociation. Input
    transformations need not be invertible, including for the inverse square. *)

(** ** 关于三个输入 Profunctor 的自然性

    在每个端点给定四项选择，按原顺序变换每个值，两个嵌套 coend 映射与
    重结合交换。输入变换无须可逆，逆方块也不例外。 *)

Section InputNaturality.
Universes u p.
Context {C D E B : Cat}.
Context {R R' : Fct ((E^op) ×C B) (SetCat@{u p _ _ _ _ _})}.
Context {Q Q' : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})}.
Context {P P' : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})}.
Context `{HPQ : !HasProfComp C D E Q P}.
Context `{HQR : !HasProfComp D E B R Q}.
Context `{HL : !HasProfComp C E B R (Q ∘Pr P)}.
Context `{HR : !HasProfComp C D B (R ∘Pr Q) P}.
Context `{HPQ' : !HasProfComp C D E Q' P'}.
Context `{HQR' : !HasProfComp D E B R' Q'}.
Context `{HL' : !HasProfComp C E B R' (Q' ∘Pr P')}.
Context `{HR' : !HasProfComp C D B (R' ∘Pr Q') P'}.
Context (α : P ⇒ P') (β : Q ⇒ Q') (γ : R ⇒ R').

Let αPQ := @ProfCompMapN C D E Q Q' P P' HPQ HPQ' β α.
Let αQR := @ProfCompMapN D E B R R' Q Q' HQR HQR' γ β.
Let αL := @ProfCompMapN C E B R R' (Q ∘Pr P) (Q' ∘Pr P')
    HL HL' γ αPQ.
Let αR := @ProfCompMapN C D B (R ∘Pr Q) (R' ∘Pr Q') P P'
    HR HR' αQR α.
Let i := @ProfunctorAssociator C D E B R Q P HPQ HQR HL HR.
Let j := @ProfunctorAssociator C D E B R' Q' P' HPQ' HQR' HL' HR'.
Let a := i.1.
Let a' := j.1.

(** Nested left maps apply one transformation to each generating value. *)

(** 嵌套左映射将一个变换分别作用于每个生成值。 *)

Lemma profunctor_triple_left_input (X : @Ob C) (W : @Ob B)
    (Y : @Ob D) (Z : @Ob E)
    (x : P (X,Y)) (y : Q (Y,Z)) (z : R (Z,W))
  : αL (X,W)
      (ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z
        (ιPr[Q; P; Y] (x,y),z)) ≈S
      ιcoend[ProfCompKernel R' (Q' ∘Pr P') X W] Z
        (ιPr[Q'; P'; Y] (α (X,Y) x,β (Y,Z) y),γ (Z,W) z).
Proof.
  transitivity (ιcoend[ProfCompKernel R' (Q' ∘Pr P') X W] Z
    (αPQ (X,Z) (ιPr[Q; P; Y] (x,y)),γ (Z,W) z)).
  - exact (coend_map_β (ProfCompInputN γ αPQ X W)
      Z (ιPr[Q; P; Y] (x,y),z)).
  - apply func_proper. split; [| reflexivity].
    exact (coend_map_β (ProfCompInputN β α X Z) Y (x,y)).
Defined.

(** The right-associated maps have the same three value transformations. *)

(** 右结合映射具有相同的三个值变换。 *)

Lemma profunctor_triple_right_input (X : @Ob C) (W : @Ob B)
    (Y : @Ob D) (Z : @Ob E)
    (x : P (X,Y)) (y : Q (Y,Z)) (z : R (Z,W))
  : αR (X,W)
      (ιcoend[ProfCompKernel (R ∘Pr Q) P X W] Y
        (x,ιPr[R; Q; Z] (y,z))) ≈S
      ιcoend[ProfCompKernel (R' ∘Pr Q') P' X W] Y
        (α (X,Y) x,ιPr[R'; Q'; Z] (β (Y,Z) y,γ (Z,W) z)).
Proof.
  transitivity (ιcoend[ProfCompKernel (R' ∘Pr Q') P' X W] Y
    (α (X,Y) x,αQR (Y,W) (ιPr[R; Q; Z] (y,z)))).
  - exact (coend_map_β (ProfCompInputN αQR α X W)
      Y (x,ιPr[R; Q; Z] (y,z))).
  - apply func_proper. split; [reflexivity |].
    exact (coend_map_β (ProfCompInputN γ β Y W) Z (y,z)).
Defined.

(** Reassociation is compatible with all three input transformations. *)

(** 重结合与三个输入变换均相容。 *)

Lemma profunctor_associator_natural
  : (a' ∘Nv αL) ≈N (αR ∘Nv a).
Proof.
  intros [X W].
  change ((a' (X,W) ∘r αL (X,W)) ≈f (αR (X,W) ∘r a (X,W))).
  apply (@profunctor_triple_left_hom_ext C D E B R Q P HPQ X W
    (@hasProfCompCoend C E B R (Q ∘Pr P) HL X W)
    (((R' ∘Pr Q') ∘Pr P') (X,W))).
  intros Y Z x y z.
  transitivity (a' (X,W)
    (ιcoend[ProfCompKernel R' (Q' ∘Pr P') X W] Z
      (ιPr[Q'; P'; Y] (α (X,Y) x,β (Y,Z) y),γ (Z,W) z))).
  - exact (@func_proper _ _ (a' (X,W)) _ _
      (profunctor_triple_left_input X W Y Z x y z)).
  - transitivity (ιcoend[ProfCompKernel (R' ∘Pr Q') P' X W] Y
      (α (X,Y) x,ιPr[R'; Q'; Z] (β (Y,Z) y,γ (Z,W) z))).
    + exact (profunctor_associator_β R' Q' P' Y Z
        (α (X,Y) x) (β (Y,Z) y) (γ (Z,W) z)).
    + transitivity (αR (X,W)
        (ιcoend[ProfCompKernel (R ∘Pr Q) P X W] Y
          (x,ιPr[R; Q; Z] (y,z)))).
      * symmetry. exact (profunctor_triple_right_input X W Y Z x y z).
      * exact (@func_proper _ _ (αR (X,W)) _ _
          (symmetry (profunctor_associator_β R Q P Y Z x y z))).
Defined.

(** Invert only the vertical associators in this square. Neither the input
    transformations nor their induced composite maps need inverses. *)

(** 只反转此方块的竖直结合子；输入变换及其诱导的复合映射均不需要逆。 *)

Lemma profunctor_associator_inv_natural
  : ((j.1 ^-1N j.2) ∘Nv αR) ≈N (αL ∘Nv (i.1 ^-1N i.2)).
Proof.
  exact (@iso_square_inv (FctCat ((C^op) ×C B) SetCat) _ _ _ _
    (a; nat_iso_is_iso a i.2) (a'; nat_iso_is_iso a' j.2)
    αL αR profunctor_associator_natural).
Defined.

End InputNaturality.
