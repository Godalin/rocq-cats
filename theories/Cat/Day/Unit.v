From Cats Require Import
  Cat.Core
  Cat.Isomorphism
  Cat.Functor.Core
  Cat.Functor.Product
  Cat.Natural
  Instance.Set.Core
  Instance.Set.Hom
  Instance.Set.Lift
  Instance.Set.Product.
From Cats Require Export
  Cat.Day.Universal.

(** * Representable Units for Day Convolution *)

(** * Day 卷积的可表单位 *)

(** A proposed unit object gives a covariant representable, raised to the
    same ambient carrier and equality levels as the input functors. The
    following constructions need only a binary functor and its indicated
    natural unit isomorphism, without associativity or strength. *)

(** 候选单位对象给出协变可表函子，提升到与输入函子相同的环境载体及相等
    层级。以下构造只需二元函子及指定的自然单位同构，不需要结合性或强度。 *)

Definition DayUnitF@{u p +} {C : Cat} (I : @Ob C)
  : Fct C (SetCat@{u p _ _ _ _ _})
  := LiftF ∘F Hom(I,-).

(** ** Inserting a Representable Arrow on the Left

    Fix a binary functor with a natural left unit isomorphism. Its inverse
    allows an arrow from the unit to act on the first tensor coordinate. *)

(** ** 在左侧插入可表箭头

    固定具有自然左单位同构的二元函子；其逆允许从单位出发的箭头作用于
    第一个张量坐标。 *)

Section LeftArrows.
Context {C : Cat} (T : Fct (C ×C C) C) {I : @Ob C}.
Context (L : π2F T I ≅N IdF).

(** Introduce the left unit, then apply the representable arrow. *)

(** 先引入左单位，再作用可表箭头。 *)

Definition day_left_arrow {X : @Ob C} (Y : @Ob C) (j : Hom I X)
  : Hom Y (T (X,Y))
  := fmap T (X := (I,Y)) (Y := (X,Y)) (j,id) ∘ (L.2 Y).1.

(** The insertion preserves the specified equality of arrows. *)

(** 插入保持箭头的指定相等。 *)

Global Instance day_left_arrow_proper {X : @Ob C} (Y : @Ob C)
  : Proper (@HomEq C I X ==> @HomEq C Y (T (X,Y)))
      (day_left_arrow Y).
Proof.
  intros j k H. unfold day_left_arrow.
  apply comp_proper; [| reflexivity].
  apply functor_fmap_proper. split; [exact H | reflexivity].
Defined.

(** Changing either coordinate commutes with the insertion. *)

(** 改变任一坐标都与插入交换。 *)

Lemma day_left_arrow_natural {X X' Y Y' : @Ob C}
    (f : Hom X X') (g : Hom Y Y') (j : Hom I X)
  : day_left_arrow Y' (f ∘ j) ∘ g ≈
      fmap T (X := (X,Y)) (Y := (X',Y')) (f,g) ∘ day_left_arrow Y j.
Proof.
  pose proof (nt_naturality (NatIso_inv L.1 L.2) g) as Hinv.
  change ((L.2 Y').1 ∘ g ≈
    fmap T (X := (I,Y)) (Y := (I,Y')) (id,g) ∘ (L.2 Y).1) in Hinv.
  unfold day_left_arrow. rewrite comp_assoc.
  rewrite Hinv.
  rewrite <- !comp_assoc, <- !functor_comp.
  apply comp_proper; [| reflexivity].
  apply functor_fmap_proper. split; cbn; carw.
Defined.

(** The identity representable arrow leaves just the inverse unitor. *)

(** 可表恒等箭头只留下单位子的逆。 *)

Lemma day_left_arrow_id (Y : @Ob C)
  : day_left_arrow Y (@id I) ≈ (L.2 Y).1.
Proof. unfold day_left_arrow. rewrite functor_id, comp_id_l. reflexivity. Defined.

(** Eliminating an inserted identity unit recovers the value arrow. *)

(** 消去插入的恒等单位恢复值箭头。 *)

Lemma day_left_arrow_unit (Y : @Ob C)
  : L.1 Y ∘ day_left_arrow Y (@id I) ≈ id.
Proof. rewrite day_left_arrow_id. exact (snd (L.2 Y).2). Defined.

(** Reinserting a unit after elimination recovers the tensor action. *)

(** 消去后重新插入单位恢复张量作用。 *)

Lemma day_left_arrow_cancel {X : @Ob C} (Y : @Ob C) (j : Hom I X)
  : day_left_arrow Y j ∘ L.1 Y ≈
      fmap T (X := (I,Y)) (Y := (X,Y)) (j,id).
Proof.
  unfold day_left_arrow. rewrite comp_assoc, (fst (L.2 Y).2), comp_id_r.
  reflexivity.
Defined.

End LeftArrows.

(** ** Inserting a Representable Arrow on the Right

    The right construction uses the supplied natural right unit isomorphism
    of the same binary functor. No symmetry is assumed. *)

(** ** 在右侧插入可表箭头

    右侧构造使用同一二元函子的指定自然右单位同构，不假定对称性。 *)

Section RightArrows.
Context {C : Cat} (T : Fct (C ×C C) C) {I : @Ob C}.
Context (R : π1F T I ≅N IdF).

(** Introduce the right unit before applying its representable arrow. *)

(** 先引入右单位，再作用其可表箭头。 *)

Definition day_right_arrow (X : @Ob C) {Y : @Ob C} (j : Hom I Y)
  : Hom X (T (X,Y))
  := fmap T (X := (X,I)) (Y := (X,Y)) (id,j) ∘ (R.2 X).1.

(** Right insertion also preserves arrow equality. *)

(** 右侧插入也保持箭头相等。 *)

Global Instance day_right_arrow_proper (X : @Ob C) {Y : @Ob C}
  : Proper (@HomEq C I Y ==> @HomEq C X (T (X,Y)))
      (day_right_arrow X).
Proof.
  intros j k H. unfold day_right_arrow.
  apply comp_proper; [| reflexivity].
  apply functor_fmap_proper. split; [reflexivity | exact H].
Defined.

(** Naturality uses the inverse right unitor and the bifunctor laws. *)

(** 自然性使用右单位子的逆及双函子定律。 *)

Lemma day_right_arrow_natural {X X' Y Y' : @Ob C}
    (f : Hom X X') (g : Hom Y Y') (j : Hom I Y)
  : day_right_arrow X' (g ∘ j) ∘ f ≈
      fmap T (X := (X,Y)) (Y := (X',Y')) (f,g) ∘ day_right_arrow X j.
Proof.
  pose proof (nt_naturality (NatIso_inv R.1 R.2) f) as Hinv.
  change ((R.2 X').1 ∘ f ≈
    fmap T (X := (X,I)) (Y := (X',I)) (f,id) ∘ (R.2 X).1) in Hinv.
  unfold day_right_arrow. rewrite comp_assoc.
  rewrite Hinv.
  rewrite <- !comp_assoc, <- !functor_comp.
  apply comp_proper; [| reflexivity].
  apply functor_fmap_proper. split; cbn; carw.
Defined.

(** An identity right insertion is the inverse unitor. *)

(** 右侧恒等插入就是单位子的逆。 *)

Lemma day_right_arrow_id (X : @Ob C)
  : day_right_arrow X (@id I) ≈ (R.2 X).1.
Proof. unfold day_right_arrow. rewrite functor_id, comp_id_l. reflexivity. Defined.

(** Eliminating the right identity unit gives the identity. *)

(** 消去右侧恒等单位得到恒等映射。 *)

Lemma day_right_arrow_unit (X : @Ob C)
  : R.1 X ∘ day_right_arrow X (@id I) ≈ id.
Proof. rewrite day_right_arrow_id. exact (snd (R.2 X).2). Defined.

(** Right insertion cancels its initial unitor. *)

(** 右侧插入消去其起始单位子。 *)

Lemma day_right_arrow_cancel (X : @Ob C) {Y : @Ob C} (j : Hom I Y)
  : day_right_arrow X j ∘ R.1 X ≈
      fmap T (X := (X,I)) (Y := (X,Y)) (id,j).
Proof.
  unfold day_right_arrow. rewrite comp_assoc, (fst (R.2 X).2), comp_id_r.
  reflexivity.
Defined.

End RightArrows.

(** ** The Left Unit Operation

    Fix the ambient setoid levels and a functor [F]. A representable arrow
    and an [F] value determine an [F] value at the binary result. *)

(** ** 左单位操作

    固定环境广集层级和函子 [F]，可表箭头与 [F] 值确定二元结果处的 [F] 值。 *)

Section LeftOperation.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C) {I : @Ob C}.
Context (L : π2F T I ≅N IdF).
Context (F : Fct C (SetCat@{u p _ _ _ _ _})).

(** The left operation is natural before any coend is selected. *)

(** 选择 coend 之前，左侧操作已经具有自然性。 *)

Program Definition DayLeftOperationN
  : DayValuesF (DayUnitF I) F ⇒ (F ∘F T)
  :=
  {|nt q := _
  |}.
Next Obligation.
  destruct q as [X Y].
  unshelve notypeclasses refine
    {|func (w : DayValuesF (DayUnitF I) F (X,Y)) :=
        fmap F (day_left_arrow T L Y (lower (fst w))) (snd w)
    |}.
  intros [j x] [k y] [Hj Hx].
  transitivity (fmap F (day_left_arrow T L Y (lower k)) x).
  - exact (@functor_fmap_proper C SetCat F _ _ _ _
      (@day_left_arrow_proper C T I L X Y _ _ (lower Hj)) x).
  - exact (@func_proper _ _ (fmap F (day_left_arrow T L Y (lower k)))
      x y Hx).
Defined.
Next Obligation.
  destruct X as [a b], Y as [a' b'], f as [f g]. intros [j y].
  change (fmap F (day_left_arrow T L b' (f ∘ lower j)) (fmap F g y)
    ≈S fmap F (fmap T (X := (a,b)) (Y := (a',b')) (f,g))
      (fmap F (day_left_arrow T L b (lower j)) y)).
  transitivity (fmap F (day_left_arrow T L b' (f ∘ lower j) ∘ g) y).
  - symmetry. exact (@functor_comp C SetCat F _ _ _
      (day_left_arrow T L b' (f ∘ lower j)) g y).
  - transitivity (fmap F (fmap T (X := (a,b)) (Y := (a',b')) (f,g)
        ∘ day_left_arrow T L b (lower j)) y).
    + exact (@functor_fmap_proper C SetCat F _ _ _ _
        (day_left_arrow_natural T L f g (lower j)) y).
    + exact (@functor_comp C SetCat F _ _ _
        (fmap T (X := (a,b)) (Y := (a',b')) (f,g))
        (day_left_arrow T L b (lower j)) y).
Defined.

End LeftOperation.

(** ** The Right Unit Operation

    The same functor can consume a representable arrow on its right. Only
    the corresponding right unit isomorphism is used. *)

(** ** 右单位操作

    同一函子也可在右侧使用可表箭头，此处只使用对应的右单位同构。 *)

Section RightOperation.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C) {I : @Ob C}.
Context (R : π1F T I ≅N IdF).
Context (F : Fct C (SetCat@{u p _ _ _ _ _})).

(** Right insertion gives the natural operation for the other unitor. *)

(** 右侧插入给出另一单位子所需的自然操作。 *)

Program Definition DayRightOperationN
  : DayValuesF F (DayUnitF I) ⇒ (F ∘F T)
  :=
  {|nt q := _
  |}.
Next Obligation.
  destruct q as [X Y].
  unshelve notypeclasses refine
    {|func (w : DayValuesF F (DayUnitF I) (X,Y)) :=
        fmap F (day_right_arrow T R X (lower (snd w))) (fst w)
    |}.
  intros [x j] [y k] [Hx Hj].
  transitivity (fmap F (day_right_arrow T R X (lower k)) x).
  - exact (@functor_fmap_proper C SetCat F _ _ _ _
      (@day_right_arrow_proper C T I R X Y _ _ (lower Hj)) x).
  - exact (@func_proper _ _ (fmap F (day_right_arrow T R X (lower k)))
      x y Hx).
Defined.
Next Obligation.
  destruct X as [a b], Y as [a' b'], f as [f g]. intros [x j].
  change (fmap F (day_right_arrow T R a' (g ∘ lower j)) (fmap F f x)
    ≈S fmap F (fmap T (X := (a,b)) (Y := (a',b')) (f,g))
      (fmap F (day_right_arrow T R a (lower j)) x)).
  transitivity (fmap F (day_right_arrow T R a' (g ∘ lower j) ∘ f) x).
  - symmetry. exact (@functor_comp C SetCat F _ _ _
      (day_right_arrow T R a' (g ∘ lower j)) f x).
  - transitivity (fmap F (fmap T (X := (a,b)) (Y := (a',b')) (f,g)
        ∘ day_right_arrow T R a (lower j)) x).
    + exact (@functor_fmap_proper C SetCat F _ _ _ _
        (day_right_arrow_natural T R f g (lower j)) x).
    + exact (@functor_comp C SetCat F _ _ _
        (fmap T (X := (a,b)) (Y := (a',b')) (f,g))
        (day_right_arrow T R a (lower j)) x).
Defined.

End RightOperation.

(** ** The Chosen Left Unitor

    Assume just the coends for the representable unit and [F]. Extend the
    natural operation using the existing Day universal property, and give
    its inverse explicitly on generators. *)

(** ** 选定的左单位子

    只假定可表单位与 [F] 所需的 coend。用已有 Day 泛性质延拓自然操作，并在
    生成元上显式给出其逆。 *)

Section LeftUnitor.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C) {I : @Ob C}.
Context (L : π2F T I ≅N IdF).
Context (F : Fct C (SetCat@{u p _ _ _ _ _})).
Context `{HD : !HasDay C T (DayUnitF I) F}.

(** Evaluate a left-unit convolution by the natural Day extension. *)

(** 通过自然 Day 延拓求值左单位卷积。 *)

Definition DayLeftUnitorN
  : DayF T (DayUnitF I) F ⇒ F
  := DayExtendN T (DayLeftOperationN T L F).

(** Pair a value with the identity representative at the unit. *)

(** 将值与单位处的恒等代表配对。 *)

Program Definition day_left_seed (Z : @Ob C)
  : F Z →r DayValuesF (DayUnitF I) F (I,Z)
  :=
  {|func x := ({|lower := @id I|}, x)
  |}.
Next Obligation.
  intros x y H. split; [exact {|lower := reflexivity (@id I)|} | exact H].
Defined.

(** Reinsert the identity representative with the original left unitor
    as weight. No inverse choice is made by universal uniqueness. *)

(** 以原左单位子为权重重新插入恒等代表，不通过泛唯一性另作逆的选择。 *)

Definition day_left_unitor_inv (Z : @Ob C)
  : F Z →r DayF T (DayUnitF I) F Z
  := day_inject T (DayUnitF I) F (I,Z) (L.1 Z) ∘r day_left_seed Z.

(** The unitor applies the composite of the result weight and insertion. *)

(** 单位子作用结果权重与插入的复合。 *)

Lemma day_left_unitor_β {X Y Z : @Ob C} (h : Hom (T (X,Y)) Z)
    (j : Hom I X) (y : F Y)
  : DayLeftUnitorN Z
      (day_inject T (DayUnitF I) F (X,Y) h ({|lower := j|}, y)) ≈S
      fmap F (h ∘ day_left_arrow T L Y j) y.
Proof.
  transitivity (fmap F h (fmap F (day_left_arrow T L Y j) y)).
  - exact (day_extend_β T (DayLeftOperationN T L F)
      (X,Y) h ({|lower := j|}, y)).
  - symmetry. exact (@functor_comp C SetCat F _ _ _
      h (day_left_arrow T L Y j) y).
Defined.

(** Moving a value arrow into the weight uses the original unitor's
    naturality and the coend gluing equation. *)

(** 将值箭头移入权重使用原单位子的自然性及 coend 粘合方程。 *)

Lemma day_left_unitor_inv_map {Y Z : @Ob C} (f : Hom Y Z) (y : F Y)
  : day_left_unitor_inv Z (fmap F f y) ≈S
      day_inject T (DayUnitF I) F (I,Y) (f ∘ L.1 Y)
        ({|lower := @id I|}, y).
Proof.
  transitivity (day_inject T (DayUnitF I) F (I,Z) (L.1 Z)
    (fmap (DayValuesF (DayUnitF I) F) (X := (I,Y)) (Y := (I,Z))
      (id,f) ({|lower := @id I|}, y))).
  - apply (@func_proper _ _
      (day_inject T (DayUnitF I) F (I,Z) (L.1 Z))).
    split; [| reflexivity]. refine {|lower := _|}.
    symmetry. apply comp_id_l.
  - transitivity (day_inject T (DayUnitF I) F (I,Y)
      (L.1 Z ∘ fmap T (X := (I,Y)) (Y := (I,Z)) (id,f))
        ({|lower := @id I|}, y)).
    + symmetry. exact (day_inject_gluing T (DayUnitF I) F
        (p := (I,Y)) (q := (I,Z)) (id,f) (L.1 Z)
          ({|lower := @id I|}, y)).
    + exact (@day_inject_proper C T (DayUnitF I) F HD (I,Y) Z _ _
        (nt_naturality L.1 f) ({|lower := @id I|}, y)).
Defined.

(** Inserting and then evaluating leaves the value unchanged. *)

(** 插入后求值保持值不变。 *)

Lemma day_left_unitor_inv_r (Z : @Ob C)
  : (DayLeftUnitorN Z ∘r day_left_unitor_inv Z) ≈f id_resp.
Proof.
  intros x.
  transitivity (fmap F (L.1 Z ∘ day_left_arrow T L Z (@id I)) x).
  - exact (day_left_unitor_β (L.1 Z) (@id I) x).
  - transitivity (fmap F (@id Z) x).
    + exact (@functor_fmap_proper C SetCat F _ _ _ _
        (day_left_arrow_unit T L Z) x).
    + exact (@functor_id C SetCat F Z x).
Defined.

(** Evaluating and reinserting a generator recovers it by two gluing
    equations, without identifying representatives or equality witnesses. *)

(** 求值并重新插入生成元后，由两次粘合方程恢复它，不等同代表或相等见证。 *)

Lemma day_left_unitor_inv_l (Z : @Ob C)
  : (day_left_unitor_inv Z ∘r DayLeftUnitorN Z) ≈f id_resp.
Proof.
  apply (day_hom_ext T (DayUnitF I) F).
  intros [X Y] h [[j] y].
  transitivity (day_left_unitor_inv Z
    (fmap F (h ∘ day_left_arrow T L Y j) y)).
  - exact (@func_proper _ _ (day_left_unitor_inv Z) _ _
      (day_left_unitor_β h j y)).
  - transitivity (day_inject T (DayUnitF I) F (I,Y)
      ((h ∘ day_left_arrow T L Y j) ∘ L.1 Y)
        ({|lower := @id I|}, y)).
    + exact (day_left_unitor_inv_map (h ∘ day_left_arrow T L Y j) y).
    + transitivity (day_inject T (DayUnitF I) F (I,Y)
        (h ∘ fmap T (X := (I,Y)) (Y := (X,Y)) (j,id))
          ({|lower := @id I|}, y)).
      * assert (Hw : (h ∘ day_left_arrow T L Y j) ∘ L.1 Y ≈
          h ∘ fmap T (X := (I,Y)) (Y := (X,Y)) (j,id)).
        { rewrite comp_assoc, day_left_arrow_cancel. reflexivity. }
        exact (@day_inject_proper C T (DayUnitF I) F HD (I,Y) Z
          _ _ Hw ({|lower := @id I|}, y)).
      * transitivity (day_inject T (DayUnitF I) F (X,Y) h
          (fmap (DayValuesF (DayUnitF I) F) (X := (I,Y)) (Y := (X,Y))
            (j,id) ({|lower := @id I|}, y))).
        -- exact (day_inject_gluing T (DayUnitF I) F
            (p := (I,Y)) (q := (X,Y)) (j,id) h
              ({|lower := @id I|}, y)).
        -- apply (@func_proper _ _
            (day_inject T (DayUnitF I) F (X,Y) h)).
           split.
           ++ refine {|lower := _|}. apply comp_id_r.
           ++ exact (@functor_id C SetCat F Y y).
Defined.

(** The computed inverse proves the natural left unitor invertible. *)

(** 计算得到的逆证明自然左单位子可逆。 *)

Definition DayLeftUnitor
  : DayF T (DayUnitF I) F ≅N F.
Proof.
  exists DayLeftUnitorN. intros Z. exists (day_left_unitor_inv Z).
  split; [exact (day_left_unitor_inv_l Z) | exact (day_left_unitor_inv_r Z)].
Defined.

End LeftUnitor.

(** ** The Chosen Right Unitor

    Assume only the coends for [F] and the representable unit. Reuse the
    same Day extension and gluing laws for the right-coordinate operation. *)

(** ** 选定的右单位子

    只假定 [F] 与可表单位所需的 coend，对右坐标操作复用同一 Day 延拓和粘合定律。 *)

Section RightUnitor.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C) {I : @Ob C}.
Context (R : π1F T I ≅N IdF).
Context (F : Fct C (SetCat@{u p _ _ _ _ _})).
Context `{HD : !HasDay C T F (DayUnitF I)}.

(** Evaluate the right-unit convolution by the existing natural extension. *)

(** 通过已有自然延拓求值右单位卷积。 *)

Definition DayRightUnitorN
  : DayF T F (DayUnitF I) ⇒ F
  := DayExtendN T (DayRightOperationN T R F).

(** Pair a value with the identity representative on the right. *)

(** 将值与右侧恒等代表配对。 *)

Program Definition day_right_seed (Z : @Ob C)
  : F Z →r DayValuesF F (DayUnitF I) (Z,I)
  :=
  {|func x := (x, {|lower := @id I|})
  |}.
Next Obligation.
  intros x y H. split; [exact H | exact {|lower := reflexivity (@id I)|}].
Defined.

(** Insert the identity on the right with the original right unitor weight. *)

(** 在右侧插入恒等代表，以原右单位子为权重。 *)

Definition day_right_unitor_inv (Z : @Ob C)
  : F Z →r DayF T F (DayUnitF I) Z
  := day_inject T F (DayUnitF I) (Z,I) (R.1 Z) ∘r day_right_seed Z.

(** Evaluate each generator through the right insertion. *)

(** 经过右侧插入求值每个生成元。 *)

Lemma day_right_unitor_β {X Y Z : @Ob C} (h : Hom (T (X,Y)) Z)
    (x : F X) (j : Hom I Y)
  : DayRightUnitorN Z
      (day_inject T F (DayUnitF I) (X,Y) h (x, {|lower := j|})) ≈S
      fmap F (h ∘ day_right_arrow T R X j) x.
Proof.
  transitivity (fmap F h (fmap F (day_right_arrow T R X j) x)).
  - exact (day_extend_β T (DayRightOperationN T R F)
      (X,Y) h (x, {|lower := j|})).
  - symmetry. exact (@functor_comp C SetCat F _ _ _
      h (day_right_arrow T R X j) x).
Defined.

(** Move a value arrow into the right-unit weight by gluing. *)

(** 通过粘合将值箭头移入右单位权重。 *)

Lemma day_right_unitor_inv_map {X Z : @Ob C} (f : Hom X Z) (x : F X)
  : day_right_unitor_inv Z (fmap F f x) ≈S
      day_inject T F (DayUnitF I) (X,I) (f ∘ R.1 X)
        (x, {|lower := @id I|}).
Proof.
  transitivity (day_inject T F (DayUnitF I) (Z,I) (R.1 Z)
    (fmap (DayValuesF F (DayUnitF I)) (X := (X,I)) (Y := (Z,I))
      (f,id) (x, {|lower := @id I|}))).
  - apply (@func_proper _ _
      (day_inject T F (DayUnitF I) (Z,I) (R.1 Z))).
    split; [reflexivity |]. refine {|lower := _|}.
    symmetry. apply comp_id_l.
  - transitivity (day_inject T F (DayUnitF I) (X,I)
      (R.1 Z ∘ fmap T (X := (X,I)) (Y := (Z,I)) (f,id))
        (x, {|lower := @id I|})).
    + symmetry. exact (day_inject_gluing T F (DayUnitF I)
        (p := (X,I)) (q := (Z,I)) (f,id) (R.1 Z)
          (x, {|lower := @id I|})).
    + exact (@day_inject_proper C T F (DayUnitF I) HD (X,I) Z _ _
        (nt_naturality R.1 f) (x, {|lower := @id I|})).
Defined.

(** Inserting and evaluating on the right recovers the value. *)

(** 在右侧插入并求值恢复值。 *)

Lemma day_right_unitor_inv_r (Z : @Ob C)
  : (DayRightUnitorN Z ∘r day_right_unitor_inv Z) ≈f id_resp.
Proof.
  intros x.
  transitivity (fmap F (R.1 Z ∘ day_right_arrow T R Z (@id I)) x).
  - exact (day_right_unitor_β (R.1 Z) x (@id I)).
  - transitivity (fmap F (@id Z) x).
    + exact (@functor_fmap_proper C SetCat F _ _ _ _
        (day_right_arrow_unit T R Z) x).
    + exact (@functor_id C SetCat F Z x).
Defined.

(** The other right inverse law follows from weighted generators and gluing. *)

(** 另一条右逆律由加权生成元及粘合得到。 *)

Lemma day_right_unitor_inv_l (Z : @Ob C)
  : (day_right_unitor_inv Z ∘r DayRightUnitorN Z) ≈f id_resp.
Proof.
  apply (day_hom_ext T F (DayUnitF I)).
  intros [X Y] h [x [j]].
  transitivity (day_right_unitor_inv Z
    (fmap F (h ∘ day_right_arrow T R X j) x)).
  - exact (@func_proper _ _ (day_right_unitor_inv Z) _ _
      (day_right_unitor_β h x j)).
  - transitivity (day_inject T F (DayUnitF I) (X,I)
      ((h ∘ day_right_arrow T R X j) ∘ R.1 X)
        (x, {|lower := @id I|})).
    + exact (day_right_unitor_inv_map (h ∘ day_right_arrow T R X j) x).
    + transitivity (day_inject T F (DayUnitF I) (X,I)
        (h ∘ fmap T (X := (X,I)) (Y := (X,Y)) (id,j))
          (x, {|lower := @id I|})).
      * assert (Hw : (h ∘ day_right_arrow T R X j) ∘ R.1 X ≈
          h ∘ fmap T (X := (X,I)) (Y := (X,Y)) (id,j)).
        { rewrite comp_assoc, day_right_arrow_cancel. reflexivity. }
        exact (@day_inject_proper C T F (DayUnitF I) HD (X,I) Z
          _ _ Hw (x, {|lower := @id I|})).
      * transitivity (day_inject T F (DayUnitF I) (X,Y) h
          (fmap (DayValuesF F (DayUnitF I)) (X := (X,I)) (Y := (X,Y))
            (id,j) (x, {|lower := @id I|}))).
        -- exact (day_inject_gluing T F (DayUnitF I)
            (p := (X,I)) (q := (X,Y)) (id,j) h
              (x, {|lower := @id I|})).
        -- apply (@func_proper _ _
            (day_inject T F (DayUnitF I) (X,Y) h)).
           split.
           ++ exact (@functor_id C SetCat F X x).
           ++ refine {|lower := _|}. apply comp_id_r.
Defined.

(** Package the computed right inverse as a natural isomorphism. *)

(** 将计算得到的右逆打包为自然同构。 *)

Definition DayRightUnitor
  : DayF T F (DayUnitF I) ≅N F.
Proof.
  exists DayRightUnitorN. intros Z. exists (day_right_unitor_inv Z).
  split; [exact (day_right_unitor_inv_l Z) | exact (day_right_unitor_inv_r Z)].
Defined.

End RightUnitor.

(** ** Naturality in the Input Functor

    Keep the binary functor and its chosen unit maps fixed. Only the
    convolutions at the two input functors are required for these squares. *)

(** ** 关于输入函子的自然性

    保持二元函子及其选定单位映射不变；这些方块只需两个输入函子处的卷积。 *)

Section InputNaturality.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C) {I : @Ob C}.
Context {F G : Fct C (SetCat@{u p _ _ _ _ _})}.

(** The left unitor commutes with a natural transformation of its input. *)

(** 左单位子与输入的自然变换交换。 *)

Lemma day_left_unitor_natural (L : π2F T I ≅N IdF)
    `{HF : !HasDay C T (DayUnitF I) F}
    `{HG : !HasDay C T (DayUnitF I) G} (α : F ⇒ G)
  : (DayLeftUnitorN T L G ∘Nv DayMapN T idN α) ≈N
      (α ∘Nv DayLeftUnitorN T L F).
Proof.
  intros Z. apply (day_hom_ext T (DayUnitF I) F).
  intros [X Y] h [[j] y].
  change (DayLeftUnitorN T L G Z
      (DayMapN T idN α Z
        (day_inject T (DayUnitF I) F (X,Y) h ({|lower := j|}, y))) ≈S
    α Z (DayLeftUnitorN T L F Z
      (day_inject T (DayUnitF I) F (X,Y) h ({|lower := j|}, y)))).
  rewrite day_map_inject.
  change (DayLeftUnitorN T L G Z
      (day_inject T (DayUnitF I) G (X,Y) h ({|lower := j|}, α Y y)) ≈S
    α Z (DayLeftUnitorN T L F Z
      (day_inject T (DayUnitF I) F (X,Y) h ({|lower := j|}, y)))).
  rewrite !day_left_unitor_β.
  symmetry. exact (nt_naturality α (h ∘ day_left_arrow T L Y j) y).
Defined.

(** Inverse left-unit naturality is the general inverse-square theorem. *)

(** 左单位逆的自然性就是一般的逆方块定理。 *)

Lemma day_left_unitor_inv_natural (L : π2F T I ≅N IdF)
    `{HF : !HasDay C T (DayUnitF I) F}
    `{HG : !HasDay C T (DayUnitF I) G} (α : F ⇒ G) (Z : @Ob C)
  : (day_left_unitor_inv T L G Z ∘r α Z) ≈f
      (DayMapN T idN α Z ∘r day_left_unitor_inv T L F Z).
Proof.
  exact (@iso_square_inv SetCat _ _ _ _
    (DayLeftUnitorN T L F Z; (DayLeftUnitor T L F).2 Z)
    (DayLeftUnitorN T L G Z; (DayLeftUnitor T L G).2 Z)
    (DayMapN T idN α Z) (α Z) (day_left_unitor_natural L α Z)).
Defined.

(** The right unitor has the corresponding input-naturality square. *)

(** 右单位子具有对应的输入自然性方块。 *)

Lemma day_right_unitor_natural (R : π1F T I ≅N IdF)
    `{HF : !HasDay C T F (DayUnitF I)}
    `{HG : !HasDay C T G (DayUnitF I)} (α : F ⇒ G)
  : (DayRightUnitorN T R G ∘Nv DayMapN T α idN) ≈N
      (α ∘Nv DayRightUnitorN T R F).
Proof.
  intros Z. apply (day_hom_ext T F (DayUnitF I)).
  intros [X Y] h [x [j]].
  change (DayRightUnitorN T R G Z
      (DayMapN T α idN Z
        (day_inject T F (DayUnitF I) (X,Y) h (x, {|lower := j|}))) ≈S
    α Z (DayRightUnitorN T R F Z
      (day_inject T F (DayUnitF I) (X,Y) h (x, {|lower := j|})))).
  rewrite day_map_inject.
  change (DayRightUnitorN T R G Z
      (day_inject T G (DayUnitF I) (X,Y) h (α X x, {|lower := j|})) ≈S
    α Z (DayRightUnitorN T R F Z
      (day_inject T F (DayUnitF I) (X,Y) h (x, {|lower := j|})))).
  rewrite !day_right_unitor_β.
  symmetry. exact (nt_naturality α (h ∘ day_right_arrow T R X j) x).
Defined.

(** Inverse right-unit naturality reuses the same general square theorem. *)

(** 右单位逆的自然性复用同一个一般方块定理。 *)

Lemma day_right_unitor_inv_natural (R : π1F T I ≅N IdF)
    `{HF : !HasDay C T F (DayUnitF I)}
    `{HG : !HasDay C T G (DayUnitF I)} (α : F ⇒ G) (Z : @Ob C)
  : (day_right_unitor_inv T R G Z ∘r α Z) ≈f
      (DayMapN T α idN Z ∘r day_right_unitor_inv T R F Z).
Proof.
  exact (@iso_square_inv SetCat _ _ _ _
    (DayRightUnitorN T R F Z; (DayRightUnitor T R F).2 Z)
    (DayRightUnitorN T R G Z; (DayRightUnitor T R G).2 Z)
    (DayMapN T α idN Z) (α Z) (day_right_unitor_natural R α Z)).
Defined.

End InputNaturality.

(** ** Unit Isomorphisms on the Functor Category

    A uniform explicit family of convolution choices gives the already
    constructed [DayTensorF]. Package the preceding input-natural maps as
    its left and right unit isomorphisms, ready for later monoidal assembly. *)

(** ** 函子范畴上的单位同构

    统一显式卷积选择族给出已有的 [DayTensorF]。将前述关于输入自然的映射打包
    为它的左右单位同构，以供后续幺半装配使用。 *)

Section FunctorCategoryUnits.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C) {I : @Ob C}.
Context (HD : ∀ F G : Fct C (SetCat@{u p _ _ _ _ _}), HasDay C T F G).

(** The family of left unitors is itself a natural transformation. *)

(** 左单位子族本身组成自然变换。 *)

Program Definition DayLeftUnitorFctN (L : π2F T I ≅N IdF)
  : π2F (DayTensorF T HD) (DayUnitF I) ⇒ IdF
  :=
  {|nt F := @DayLeftUnitorN C T I L F (HD (DayUnitF I) F)
  |}.
Next Obligation.
  exact (@day_left_unitor_natural C T I X Y L
    (HD (DayUnitF I) X) (HD (DayUnitF I) Y) f).
Defined.

(** Component inverses turn that family into a functor-category isomorphism. *)

(** 分量逆将该族提升为函子范畴上的自然同构。 *)

Definition DayLeftUnitorFct (L : π2F T I ≅N IdF)
  : π2F (DayTensorF T HD) (DayUnitF I) ≅N IdF.
Proof.
  exists (DayLeftUnitorFctN L). intros F.
  exact (NatIso_is_iso _ (@DayLeftUnitor C T I L F
    (HD (DayUnitF I) F)).2).
Defined.

(** The right unitors also form a natural transformation on the functors. *)

(** 右单位子也组成函子上的自然变换。 *)

Program Definition DayRightUnitorFctN (R : π1F T I ≅N IdF)
  : π1F (DayTensorF T HD) (DayUnitF I) ⇒ IdF
  :=
  {|nt F := @DayRightUnitorN C T I R F (HD F (DayUnitF I))
  |}.
Next Obligation.
  exact (@day_right_unitor_natural C T I X Y R
    (HD X (DayUnitF I)) (HD Y (DayUnitF I)) f).
Defined.

(** Retain the computed inverse at every functor. *)

(** 在每个函子处保留计算得到的逆。 *)

Definition DayRightUnitorFct (R : π1F T I ≅N IdF)
  : π1F (DayTensorF T HD) (DayUnitF I) ≅N IdF.
Proof.
  exists (DayRightUnitorFctN R). intros F.
  exact (NatIso_is_iso _ (@DayRightUnitor C T I R F
    (HD F (DayUnitF I))).2).
Defined.

End FunctorCategoryUnits.
