From Cats Require Export
  Cat.Profunctor.Associator
  Cat.Profunctor.LeftUnit
  Cat.Profunctor.RightUnit.
From Cats Require Import
  Cat.Core
  Instance.Set.Core
  Instance.Set.Product.

Local Open Scope prof_scope.

(** * Coherence of Profunctor Composition

    Reassociation keeps the ordered values of a composite. Generator
    distinction therefore reduces its coherence equations to the original
    coend gluing law or to the same fourfold insertion. Every composition
    choice remains explicit; no global existence model is selected. *)

(** * Profunctor 复合的相干性

    重结合保留复合中的有序值，故生成元区分将其相干方程归约到原 coend 粘合律，
    或同一个四重插入。每个复合选择仍为显式参数，不选择全局存在模型。 *)

(** ** The Hom Triangle

    Fix two composable profunctors and exactly the five composition
    families in the triangle. Only the middle category's Hom carrier and
    equality levels must fit the corresponding value bounds. Applying its
    represented arrow on either side gives the same glued generator. *)

(** ** Hom 三角形

    固定两个可复合的 profunctor 及三角形中恰好五个复合族。只需中间范畴的
    Hom 载体及相等层级分别容纳于对应值界；在任一侧应用其所表示的箭头，
    给出粘合后相同的生成元。 *)

Section Triangle.
Universes u p.
Context {C D E : Cat}.
Context (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})).
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context `{HP : !HasProfComp C D D (HomProf D) P}.
Context `{HQ : !HasProfComp D D E Q (HomProf D)}.
Context `{HL : !HasProfComp C D E Q (HomProf D ∘Pr P)}.
Context `{HR : !HasProfComp C D E (Q ∘Pr HomProf D) P}.
Context `{HPQ : !HasProfComp C D E Q P}.

Let a := @ProfunctorAssociatorN C D D E Q (HomProf D) P
  HP HQ HL HR.
Let ρ := @ProfRightUnitorN D E Q HQ.
Let λP := @ProfLeftUnitorN C D P HP.
Let left_route := @ProfCompMapN C D E
  (Q ∘Pr HomProf D) Q P P HR HPQ ρ (IdN (F := P)).
Let right_route := @ProfCompMapN C D E
  Q Q (HomProf D ∘Pr P) P HL HPQ (IdN (F := Q)) λP.

(** The two ways of eliminating the middle Hom agree as transformations
    on the complete composites, not only on native representatives. *)

(** 消去中间 Hom 的两种方式在完整复合上的自然变换意义下相同，不仅限于
    原生代表。 *)

Lemma profunctor_triangle
  : (left_route ∘Nv a) ≈N right_route.
Proof.
  intros [X W].
  change ((left_route
    (X,W) ∘r a (X,W)) ≈f
    right_route (X,W)).
  apply (@profunctor_triple_left_hom_ext C D D E Q (HomProf D) P
    HP X W (@hasProfCompCoend C D E Q
      (HomProf D ∘Pr P) HL X W) ((Q ∘Pr P) (X,W))).
  intros Y Z x [h] y.
  transitivity (ιcoend[ProfCompKernel Q P X W] Y
    (x,lmap[Q; h] y)).
  - transitivity (left_route (X,W)
      (ιcoend[ProfCompKernel (Q ∘Pr HomProf D) P X W] Y
        (x,ιPr[Q; HomProf D; Z] ({|lower := h|},y)))).
    + exact (@func_proper _ _ (left_route (X,W)) _ _
        (profunctor_associator_β
          Q (HomProf D) P Y Z x {|lower := h|} y)).
    + transitivity (ιcoend[ProfCompKernel Q P X W] Y
        (x,ρ (Y,W)
          (ιPr[Q; HomProf D; Z] ({|lower := h|},y)))).
      * exact (@prof_comp_map_inject C D E
          (Q ∘Pr HomProf D) Q P P HR HPQ ρ (IdN (F := P)) X Y W x
          (ιPr[Q; HomProf D; Z] ({|lower := h|},y))).
      * apply func_proper. split; [reflexivity |].
        exact (prof_right_unit_β Q Y W Z h y).
  - transitivity (ιcoend[ProfCompKernel Q P X W] Z
      (rmap[P; h] x,y)).
    + exact (prof_comp_gluing Q P h x y).
    + symmetry.
      transitivity (ιcoend[ProfCompKernel Q P X W] Z
        (λP (X,Z)
          (ιPr[HomProf D; P; Y] (x,{|lower := h|})),y)).
      * exact (@prof_comp_map_inject C D E Q Q
          (HomProf D ∘Pr P) P HL HPQ (IdN (F := Q)) λP X Z W
          (ιPr[HomProf D; P; Y] (x,{|lower := h|})) y).
      * apply func_proper. split; [| reflexivity].
        exact (prof_left_unit_β P X Z Y x h).
Defined.

End Triangle.

(** ** Fourfold Generator Distinction

    Choose the first pair and triple composition families, then just one
    outer coend. The existing triple distinction followed by one ordinary
    coend distinction tests every outgoing map on ordered quadruples.
    No other parenthesization or Hom size bound is used. *)

(** ** 四重生成元区分

    选择前两段及前三段的复合族，再只选择单个外层 coend。已有三元区分之后
    接一次普通 coend 区分，即可在有序四元组上检验全部出射映射；不使用其他
    括号方式或 Hom 大小界。 *)

Section QuadDistinction.
Universes u p.
Context {C D E B A : Cat}.
Context (S : Fct ((B^op) ×C A) (SetCat@{u p _ _ _ _ _})).
Context (R : Fct ((E^op) ×C B) (SetCat@{u p _ _ _ _ _})).
Context (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})).
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context `{HPQ : !HasProfComp C D E Q P}.
Context `{HPQR : !HasProfComp C E B R (Q ∘Pr P)}.
Context {X : @Ob C} {V : @Ob A}.
Context `{HO : !HasCoend SetCat
    (ProfCompKernel S (R ∘Pr (Q ∘Pr P)) X V)}.

(** Three successive original injections jointly distinguish maps on the
    whole four-stage composite, with the last two values held as parameters. *)

(** 连续三个原注入联合区分整个四段复合上的映射，后两个值保持为参数。 *)

Lemma profunctor_quad_left_hom_ext {T : SetC@{u p}}
    (f g : coend[ProfCompKernel S (R ∘Pr (Q ∘Pr P)) X V] →r T)
    (H : ∀ (Y : @Ob D) (Z : @Ob E) (W : @Ob B)
      (x : P (X,Y)) (y : Q (Y,Z)) (z : R (Z,W)) (w : S (W,V)),
      f (ιcoend[ProfCompKernel S (R ∘Pr (Q ∘Pr P)) X V] W
        (ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z
          (ιPr[Q; P; Y] (x,y),z),w)) ≈S
      g (ιcoend[ProfCompKernel S (R ∘Pr (Q ∘Pr P)) X V] W
        (ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z
          (ιPr[Q; P; Y] (x,y),z),w)))
  : f ≈f g.
Proof.
  apply (@profunctor_triple_left_hom_ext C E B A S R (Q ∘Pr P)
    HPQR X V HO T f g).
  intros Z W xy z w.
  unshelve epose (fz := ({|func v :=
    f (ιcoend[ProfCompKernel S (R ∘Pr (Q ∘Pr P)) X V] W
      (ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z (v,z),w))|}
    : (Q ∘Pr P) (X,Z) →r T)).
  { intros v v' Hv. apply func_proper. apply func_proper.
    split; [| reflexivity]. apply func_proper. exact (Hv,reflexivity z). }
  unshelve epose (gz := ({|func v :=
    g (ιcoend[ProfCompKernel S (R ∘Pr (Q ∘Pr P)) X V] W
      (ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z (v,z),w))|}
    : (Q ∘Pr P) (X,Z) →r T)).
  { intros v v' Hv. apply func_proper. apply func_proper.
    split; [| reflexivity]. apply func_proper. exact (Hv,reflexivity z). }
  refine (@coend_hom_ext D SetCat (ProfCompKernel Q P X Z)
    (@hasProfCompCoend C D E Q P HPQ X Z) T fz gz _ xy).
  intros Y [x y]. exact (H Y Z W x y z w).
Defined.

End QuadDistinction.

(** ** The Pentagon

    Fix four composable profunctors and the twelve composition families
    in the five parenthesizations: three pairs, four triples and five
    quadruples. Both paths send the same ordered values to the completely
    right-associated insertion. No Hom unit or index size bound is needed. *)

(** ** 五边形

    固定四个可复合 profunctor 及五种括号方式中的十二个复合族：三个二段、
    四个三段和五个四段复合。两路将相同的有序值送到完全右结合的插入，
    不需要 Hom 单位或指标大小界。 *)

Section Pentagon.
Universes u p.
Context {C D E B A : Cat}.
Context (S : Fct ((B^op) ×C A) (SetCat@{u p _ _ _ _ _})).
Context (R : Fct ((E^op) ×C B) (SetCat@{u p _ _ _ _ _})).
Context (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})).
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context `{HPQ : !HasProfComp C D E Q P}.
Context `{HQR : !HasProfComp D E B R Q}.
Context `{HRS : !HasProfComp E B A S R}.
Context `{HPQR : !HasProfComp C E B R (Q ∘Pr P)}.
Context `{HRQP : !HasProfComp C D B (R ∘Pr Q) P}.
Context `{HSRQ : !HasProfComp D B A S (R ∘Pr Q)}.
Context `{HRSQ : !HasProfComp D E A (S ∘Pr R) Q}.
Context `{H0 : !HasProfComp C B A S (R ∘Pr (Q ∘Pr P))}.
Context `{H1 : !HasProfComp C E A (S ∘Pr R) (Q ∘Pr P)}.
Context `{H2 : !HasProfComp C B A S ((R ∘Pr Q) ∘Pr P)}.
Context `{H3 : !HasProfComp C D A (S ∘Pr (R ∘Pr Q)) P}.
Context `{H4 : !HasProfComp C D A ((S ∘Pr R) ∘Pr Q) P}.

Let short_first
  : S ∘Pr (R ∘Pr (Q ∘Pr P)) ⇒ (S ∘Pr R) ∘Pr (Q ∘Pr P)
  := @ProfunctorAssociatorN C E B A S R (Q ∘Pr P)
    HPQR HRS H0 H1.
Let short_last
  : (S ∘Pr R) ∘Pr (Q ∘Pr P) ⇒ ((S ∘Pr R) ∘Pr Q) ∘Pr P
  := @ProfunctorAssociatorN C D E A (S ∘Pr R) Q P
    HPQ HRSQ H1 H4.
Let inner_first
  : R ∘Pr (Q ∘Pr P) ⇒ (R ∘Pr Q) ∘Pr P
  := @ProfunctorAssociatorN C D E B R Q P
    HPQ HQR HPQR HRQP.
Let inner_last
  : S ∘Pr (R ∘Pr Q) ⇒ (S ∘Pr R) ∘Pr Q
  := @ProfunctorAssociatorN D E B A S R Q
    HQR HRS HSRQ HRSQ.
Let long_first
  : S ∘Pr (R ∘Pr (Q ∘Pr P)) ⇒ S ∘Pr ((R ∘Pr Q) ∘Pr P)
  := @ProfCompMapN C B A S S
    (R ∘Pr (Q ∘Pr P)) ((R ∘Pr Q) ∘Pr P) H0 H2
    (IdN (F := S)) inner_first.
Let long_middle
  : S ∘Pr ((R ∘Pr Q) ∘Pr P) ⇒ (S ∘Pr (R ∘Pr Q)) ∘Pr P
  := @ProfunctorAssociatorN C D B A S (R ∘Pr Q) P
    HRQP HSRQ H2 H3.
Let long_last
  : (S ∘Pr (R ∘Pr Q)) ∘Pr P ⇒ ((S ∘Pr R) ∘Pr Q) ∘Pr P
  := @ProfCompMapN C D A
    (S ∘Pr (R ∘Pr Q)) ((S ∘Pr R) ∘Pr Q) P P H3 H4
    inner_last (IdN (F := P)).

(** Two reassociations preserve all four values and their original order. *)

(** 两次重结合保留四个值及其原有顺序。 *)

Lemma profunctor_pentagon_short_β (X : @Ob C) (V : @Ob A)
    (Y : @Ob D) (Z : @Ob E) (W : @Ob B)
    (x : P (X,Y)) (y : Q (Y,Z)) (z : R (Z,W)) (w : S (W,V))
  : short_last (X,V) (short_first (X,V)
      (ιcoend[ProfCompKernel S (R ∘Pr (Q ∘Pr P)) X V] W
        (ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z
          (ιPr[Q; P; Y] (x,y),z),w))) ≈S
    ιcoend[ProfCompKernel ((S ∘Pr R) ∘Pr Q) P X V] Y
      (x,ιcoend[ProfCompKernel (S ∘Pr R) Q Y V] Z
        (y,ιPr[S; R; W] (z,w))).
Proof.
  transitivity (short_last (X,V)
    (ιcoend[ProfCompKernel (S ∘Pr R) (Q ∘Pr P) X V] Z
      (ιPr[Q; P; Y] (x,y),ιPr[S; R; W] (z,w)))).
  - exact (@func_proper _ _ (short_last (X,V)) _ _
      (@profunctor_associator_β C E B A S R (Q ∘Pr P)
        HPQR HRS X V
        (@hasProfCompCoend C B A S (R ∘Pr (Q ∘Pr P)) H0 X V)
        (@hasProfCompCoend C E A (S ∘Pr R) (Q ∘Pr P) H1 X V)
        Z W
        (ιPr[Q; P; Y] (x,y)) z w)).
  - exact (@profunctor_associator_β C D E A (S ∘Pr R) Q P
      HPQ HRSQ X V
      (@hasProfCompCoend C E A (S ∘Pr R) (Q ∘Pr P) H1 X V)
      (@hasProfCompCoend C D A ((S ∘Pr R) ∘Pr Q) P H4 X V)
      Y Z x y
      (ιPr[S; R; W] (z,w))).
Defined.

(** The three-edge path, including both input maps, has the same value. *)

(** 包含两个输入映射的三边路径具有相同的值。 *)

Lemma profunctor_pentagon_long_β (X : @Ob C) (V : @Ob A)
    (Y : @Ob D) (Z : @Ob E) (W : @Ob B)
    (x : P (X,Y)) (y : Q (Y,Z)) (z : R (Z,W)) (w : S (W,V))
  : long_last (X,V) (long_middle (X,V) (long_first (X,V)
      (ιcoend[ProfCompKernel S (R ∘Pr (Q ∘Pr P)) X V] W
        (ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z
          (ιPr[Q; P; Y] (x,y),z),w)))) ≈S
    ιcoend[ProfCompKernel ((S ∘Pr R) ∘Pr Q) P X V] Y
      (x,ιcoend[ProfCompKernel (S ∘Pr R) Q Y V] Z
        (y,ιPr[S; R; W] (z,w))).
Proof.
  assert (Hfirst : long_first (X,V)
    (ιcoend[ProfCompKernel S (R ∘Pr (Q ∘Pr P)) X V] W
      (ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z
        (ιPr[Q; P; Y] (x,y),z),w)) ≈S
    ιcoend[ProfCompKernel S ((R ∘Pr Q) ∘Pr P) X V] W
      (ιcoend[ProfCompKernel (R ∘Pr Q) P X W] Y
        (x,ιPr[R; Q; Z] (y,z)),w)).
  { transitivity
      (ιcoend[ProfCompKernel S ((R ∘Pr Q) ∘Pr P) X V] W
        (inner_first (X,W)
          (ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z
            (ιPr[Q; P; Y] (x,y),z)),w)).
    - exact (@prof_comp_map_inject C B A S S
        (R ∘Pr (Q ∘Pr P)) ((R ∘Pr Q) ∘Pr P) H0 H2
        (IdN (F := S)) inner_first
        X W V
        (ιcoend[ProfCompKernel R (Q ∘Pr P) X W] Z
          (ιPr[Q; P; Y] (x,y),z)) w).
    - apply func_proper. split; [| reflexivity].
      exact (@profunctor_associator_β C D E B R Q P HPQ HQR X W
        (@hasProfCompCoend C E B R (Q ∘Pr P) HPQR X W)
        (@hasProfCompCoend C D B (R ∘Pr Q) P HRQP X W)
        Y Z x y z). }
  transitivity (long_last (X,V)
    (ιcoend[ProfCompKernel (S ∘Pr (R ∘Pr Q)) P X V] Y
      (x,ιPr[S; R ∘Pr Q; W] (ιPr[R; Q; Z] (y,z),w)))).
  - apply (@func_proper _ _ (long_last (X,V))).
    transitivity (long_middle (X,V)
      (ιcoend[ProfCompKernel S ((R ∘Pr Q) ∘Pr P) X V] W
        (ιcoend[ProfCompKernel (R ∘Pr Q) P X W] Y
          (x,ιPr[R; Q; Z] (y,z)),w))).
    + exact (@func_proper _ _ (long_middle (X,V)) _ _ Hfirst).
    + exact (@profunctor_associator_β C D B A S (R ∘Pr Q) P
        HRQP HSRQ X V
        (@hasProfCompCoend C B A S ((R ∘Pr Q) ∘Pr P) H2 X V)
        (@hasProfCompCoend C D A (S ∘Pr (R ∘Pr Q)) P H3 X V)
        Y W x
        (ιPr[R; Q; Z] (y,z)) w).
  - transitivity
      (ιcoend[ProfCompKernel ((S ∘Pr R) ∘Pr Q) P X V] Y
        (x,inner_last (Y,V)
          (ιPr[S; R ∘Pr Q; W] (ιPr[R; Q; Z] (y,z),w)))).
    + exact (@prof_comp_map_inject C D A
        (S ∘Pr (R ∘Pr Q)) ((S ∘Pr R) ∘Pr Q) P P H3 H4
        inner_last (IdN (F := P))
        X Y V x (ιPr[S; R ∘Pr Q; W] (ιPr[R; Q; Z] (y,z),w))).
    + apply func_proper. split; [reflexivity |].
      exact (@profunctor_associator_β D E B A S R Q
        HQR HRS Y V
        (@hasProfCompCoend D B A S (R ∘Pr Q) HSRQ Y V)
        (@hasProfCompCoend D E A (S ∘Pr R) Q HRSQ Y V)
        Z W y z w).
Defined.

(** Fourfold distinction upgrades the common generator computation to
    equality of the complete natural transformations around the pentagon. *)

(** 四重区分将共同的生成元计算提升为五边形两路完整自然变换的相等。 *)

Lemma profunctor_pentagon
  : (short_last ∘Nv short_first) ≈N
    (long_last ∘Nv (long_middle ∘Nv long_first)).
Proof.
  intros [X V].
  change ((short_last (X,V) ∘r short_first (X,V)) ≈f
    (long_last (X,V) ∘r (long_middle (X,V) ∘r long_first (X,V)))).
  apply (@profunctor_quad_left_hom_ext C D E B A S R Q P
    HPQ HPQR X V
    (@hasProfCompCoend C B A S (R ∘Pr (Q ∘Pr P)) H0 X V)
    ((((S ∘Pr R) ∘Pr Q) ∘Pr P) (X,V))).
  intros Y Z W x y z w.
  transitivity
    (ιcoend[ProfCompKernel ((S ∘Pr R) ∘Pr Q) P X V] Y
      (x,ιcoend[ProfCompKernel (S ∘Pr R) Q Y V] Z
        (y,ιPr[S; R; W] (z,w)))).
  - exact (profunctor_pentagon_short_β X V Y Z W x y z w).
  - symmetry. exact (profunctor_pentagon_long_β X V Y Z W x y z w).
Defined.

End Pentagon.
