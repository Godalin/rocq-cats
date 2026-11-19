From Cats Require Export Cat.Gluing.Cartesian.
From Cats Require Import
  Cat.Core
  Cat.Product.Core
  Cat.Product.Transport
  Cat.Exponential.Core
  Cat.Exponential.Functor
  Cat.Functor.ExponentialComparison
  Cat.Pullback.

(** * Gluing Exponentials from Particular Pullbacks

    The base of an exponential is the base exponential. Its left object
    is a pullback comparing result postcomposition with transported base
    evaluation. Only these particular pullbacks are needed; neither
    terminal nor exponential preservation by the gluing functor is used.

    For [X = (U,A,u)] and [Y = (V,B,v)], compare the cospan
    [V ^ U → F B ^ U ← F (B ^ A)]. The first arrow postcomposes by [v];
    the second transports base evaluation and restricts inputs along [u].
    A pullback [E] with legs [p,q] gives [(E, B ^ A, q)]. Evaluation on
    its left side is [eval ∘ (p × id)]; on its base it is base evaluation. *)

(** * 从特定拉回构造粘合指数

    指数的基对象为基指数。其左对象是一个拉回，比较结果后合成与运输后的基
    求值。只需要这些特定拉回，不使用粘合函子的终对象或指数保持性。

    对 [X = (U,A,u)]、[Y = (V,B,v)]，比较余跨度
    [V ^ U → F B ^ U ← F (B ^ A)]。第一箭头与 [v] 后合成，第二箭头运输
    基求值并沿 [u] 限制输入。具有锥腿 [p,q] 的拉回 [E] 给出
    [(E, B ^ A, q)]；左求值为 [eval ∘ (p × id)]，基求值则为原基求值。 *)

(** ** Products and the Two Comparison Arrows

    Fix products and exponentials in both categories and preservation of
    the base product cones. No terminal choice is made. Express the glued
    product arrow through the integrated inverse comparison, then define
    the cospan whose pullback will represent the exponential. *)

(** ** 积与两个比较箭头

    固定两侧积和指数及基积锥的保持性，不选择终对象。先用已集成的逆比较
    表达粘合积的结构箭头，再定义表示指数所需拉回的余跨度。 *)

Section GluingExp.
Context {C D : Cat} (F : Fct C D).
Context `{PC : !HasProduct C} `{EC : !HasExponential PC}
    `{PD : !HasProduct D} `{ED : !HasExponential PD}.
Context (preserves : ∀ A B : @Ob C,
    is_product (F A) (F B) (F ((A × B)%ob)) (fmap F π1) (fmap F π2)).
Let PG
  : HasProduct (Gluing F)
  := Gluing_HasProduct F preserves.
Local Existing Instance PG.

(** The image product receives the two structure arrows componentwise. *)

(** 两个结构箭头逐分量给出指向像积的映射。 *)

Lemma gluing_product_arrow (X Y : @Ob (Gluing F))
  : comma_arrow ((X × Y)%ob) ≈
      preserved_product_inv F preserves
        (comma_right_ob X) (comma_right_ob Y) ∘
      (comma_arrow X × comma_arrow Y).
Proof.
  apply (product_cone_ext (preserves _ _)).
  - transitivity (comma_arrow X ∘
      @Cats.Cat.Product.Core.π1 D PD (comma_left_ob X) (comma_left_ob Y)).
    + exact (comma_comm (@Cats.Cat.Product.Core.π1 _ PG X Y)).
    + symmetry.
      transitivity ((fmap F π1 ∘ preserved_product_inv F preserves
        (comma_right_ob X) (comma_right_ob Y)) ∘
        (comma_arrow X × comma_arrow Y)).
      * symmetry. apply comp_assoc.
      * rewrite (fst (preserved_product_inv_β F preserves _ _)).
        rewrite cross_η, product_β1. reflexivity.
  - transitivity (comma_arrow Y ∘
      @Cats.Cat.Product.Core.π2 D PD (comma_left_ob X) (comma_left_ob Y)).
    + exact (comma_comm (@Cats.Cat.Product.Core.π2 _ PG X Y)).
    + symmetry.
      transitivity ((fmap F π2 ∘ preserved_product_inv F preserves
        (comma_right_ob X) (comma_right_ob Y)) ∘
        (comma_arrow X × comma_arrow Y)).
      * symmetry. apply comp_assoc.
      * rewrite (snd (preserved_product_inv_β F preserves _ _)).
        rewrite cross_η, product_β2. reflexivity.
Qed.

(** Pairing projects to the original target mediator up to hom equality.
    Abstract universal-property witnesses need not reduce natively. *)

(** 配对按 Hom 相等投影到原目标中介；抽象泛性质见证不必原生归约。 *)

Lemma gluing_pair_left {U V W : @Ob (Gluing F)}
    (f : (@Hom (Gluing F)) W U) (g : (@Hom (Gluing F)) W V)
  : comma_left ⟨f, g⟩ ≈ ⟨comma_left f, comma_left g⟩.
Proof.
  pose proof (preserved_pair (GluingLeftF F)
    (gluing_left_product F preserves) f g) as H.
  change (comma_left ⟨f, g⟩ ≈ ⟨π1, π2⟩ ∘
    ⟨comma_left f, comma_left g⟩) in H.
  rewrite product_pair_η, comp_id_l in H. exact H.
Qed.

(** The base pairing likewise uses its inherited universal mediator. *)

(** 基配对同样使用继承的泛中介。 *)

Lemma gluing_pair_right {U V W : @Ob (Gluing F)}
    (f : (@Hom (Gluing F)) W U) (g : (@Hom (Gluing F)) W V)
  : comma_right ⟨f, g⟩ ≈ ⟨comma_right f, comma_right g⟩.
Proof.
  pose proof (preserved_pair (GluingRightF F)
    (gluing_right_product F preserves) f g) as H.
  change (comma_right ⟨f, g⟩ ≈ ⟨π1, π2⟩ ∘
    ⟨comma_right f, comma_right g⟩) in H.
  rewrite product_pair_η, comp_id_l in H. exact H.
Qed.

(** The left component of a product map uses the chosen target products. *)

(** 积映射的左分量使用选定目标积。 *)

Lemma gluing_cross_left {U V U' V' : @Ob (Gluing F)}
    (f : (@Hom (Gluing F)) U U') (g : (@Hom (Gluing F)) V V')
  : comma_left (f × g) ≈ comma_left f × comma_left g.
Proof.
  transitivity ⟨comma_left f ∘ π1, comma_left g ∘ π2⟩.
  - transitivity (comma_left ⟨f ∘ π1, g ∘ π2⟩).
    + exact (fst (cross_η f g)).
    + exact (gluing_pair_left (f ∘ π1) (g ∘ π2)).
  - symmetry. apply cross_η.
Qed.

(** The right component uses exactly the inherited base products. *)

(** 右分量恰好使用继承的基积。 *)

Lemma gluing_cross_right {U V U' V' : @Ob (Gluing F)}
    (f : (@Hom (Gluing F)) U U') (g : (@Hom (Gluing F)) V V')
  : comma_right (f × g) ≈ comma_right f × comma_right g.
Proof.
  transitivity ⟨comma_right f ∘ π1, comma_right g ∘ π2⟩.
  - transitivity (comma_right ⟨f ∘ π1, g ∘ π2⟩).
    + exact (snd (cross_η f g)).
    + exact (gluing_pair_right (f ∘ π1) (g ∘ π2)).
  - symmetry. apply cross_η.
Qed.

(** Postcompose functions by the result structure arrow. *)

(** 将函数与结果结构箭头后合成。 *)

Definition gluing_exp_result (X Y : @Ob (Gluing F))
  : Hom (comma_left_ob Y ^ comma_left_ob X)
      (F (comma_right_ob Y) ^ comma_left_ob X)
  := exp_map (comma_arrow Y).

(** Transport base functions and restrict their inputs along the structure
    arrow of the argument. The comparison need not be invertible. *)

(** 运输基函数，并沿参数的结构箭头限制输入；比较无需可逆。 *)

Definition gluing_exp_base (X Y : @Ob (Gluing F))
  : Hom (F ((comma_right_ob Y ^ comma_right_ob X)%ob))
      (F (comma_right_ob Y) ^ comma_left_ob X)
  := (id ^ comma_arrow X) ∘ exp_cmp F preserves
      (comma_right_ob X) (comma_right_ob Y).

(** Uncurrying the base comparison computes transported evaluation. *)

(** 基比较的反柯里化计算出运输后的求值。 *)

Lemma gluing_exp_base_eval (X Y : @Ob (Gluing F))
  : uncurry (gluing_exp_base X Y) ≈
      fmap F eval ∘ preserved_product_inv F preserves
        ((comma_right_ob Y ^ comma_right_ob X)%ob) (comma_right_ob X) ∘
      (id × comma_arrow X).
Proof.
  unfold gluing_exp_base.
  rewrite exp_uncurry_dimap, comp_id_l.
  unfold uncurry at 1. rewrite exp_cmp_eval. reflexivity.
Qed.

(** ** A Supplied Pullback Represents the Exponential

    Fix two glued objects and one candidate pullback of the comparison
    cospan. The base exponential and its second projection give the glued
    object. Its first projection supplies evaluation in the left category. *)

(** ** 指定拉回表示指数

    固定两个粘合对象及比较余跨度的一个候选拉回。基指数与第二投影组成粘合
    对象，第一投影则给出左侧范畴中的求值。 *)

Context (X Y : @Ob (Gluing F)).
Context (E : @Ob D)
    (p : Hom E (comma_left_ob Y ^ comma_left_ob X))
    (q : Hom E (F ((comma_right_ob Y ^ comma_right_ob X)%ob))).
Context (pullback : is_pullback (gluing_exp_result X Y)
    (gluing_exp_base X Y) E p q).

(** The supplied pullback is the left object, without a second choice. *)

(** 指定拉回就是左对象，不另作选择。 *)

Program Definition GluingExp
  : @Ob (Gluing F)
  :=
  {|comma_left_ob := E
  ; comma_right_ob := (comma_right_ob Y ^ comma_right_ob X)%ob
  ; comma_arrow := q
  |}.

(** The pullback equation makes the two evaluations a commuting square. *)

(** 拉回方程使两个求值组成交换方形。 *)

Program Definition gluing_eval
  : (@Hom (Gluing F)) ((GluingExp × X)%ob) Y
  :=
  {|comma_left := eval ∘ (p × id)
  ; comma_right := eval
  |}.
Next Obligation.
  change (fmap F eval ∘ comma_arrow ((GluingExp × X)%ob) ≈
    comma_arrow Y ∘ (eval ∘ (p × id))).
  rewrite gluing_product_arrow.
  assert (H : uncurry (gluing_exp_result X Y ∘ p) ≈
      uncurry (gluing_exp_base X Y ∘ q)).
  { apply exp_uncurry_proper. exact (fst pullback). }
  unfold gluing_exp_result in H.
  rewrite exp_uncurry_comp_l, exp_uncurry_comp_r,
    gluing_exp_base_eval in H.
  unfold uncurry in H.
  rewrite !comp_assoc, <- cross_comp, comp_id_l, comp_id_r in H.
  symmetry. exact H.
Defined.

(** The transpose of a square gives a cone over the comparison cospan. *)

(** 方形的转置给出比较余跨度上的锥。 *)

Lemma gluing_curry_square {Z : @Ob (Gluing F)}
    (f : (@Hom (Gluing F)) ((Z × X)%ob) Y)
  : gluing_exp_result X Y ∘ (ƛ (comma_left f)) ≈
      gluing_exp_base X Y ∘
        (fmap F (ƛ (comma_right f)) ∘ comma_arrow Z).
Proof.
  unfold gluing_exp_base.
  rewrite (comp_assoc (id ^ comma_arrow X)).
  rewrite <- (comp_assoc (exp_cmp F preserves
    (comma_right_ob X) (comma_right_ob Y))).
  rewrite exp_cmp_curry.
  apply exp_ext. unfold gluing_exp_result.
  rewrite exp_uncurry_comp_l, exp_β,
    exp_uncurry_dimap, comp_id_l,
    exp_uncurry_comp_r, exp_β.
  rewrite !comp_assoc, <- cross_comp, comp_id_l, comp_id_r.
  rewrite <- (gluing_product_arrow Z X).
  symmetry. exact (comma_comm f).
Qed.

(** Select the left transpose using the supplied pullback mediator. *)

(** 用指定拉回中介选择左侧转置。 *)

Definition gluing_curry_left {Z : @Ob (Gluing F)}
    (f : (@Hom (Gluing F)) ((Z × X)%ob) Y)
  : Hom (comma_left_ob Z) E
  := (snd pullback (comma_left_ob Z) (ƛ (comma_left f))
      (fmap F (ƛ (comma_right f)) ∘ comma_arrow Z)
      (gluing_curry_square f)).1.

(** Its two projections retain the candidate pullback's full uniqueness. *)

(** 两个投影保留候选拉回的完整唯一性。 *)

Lemma gluing_curry_left_unique {Z : @Ob (Gluing F)}
    (f : (@Hom (Gluing F)) ((Z × X)%ob) Y)
  : is_unique (λ h, p ∘ h ≈ ƛ (comma_left f) ∧
      q ∘ h ≈ fmap F (ƛ (comma_right f)) ∘ comma_arrow Z)
      (gluing_curry_left f).
Proof.
  exact (snd pullback (comma_left_ob Z) (ƛ (comma_left f))
    (fmap F (ƛ (comma_right f)) ∘ comma_arrow Z)
    (gluing_curry_square f)).2.
Qed.

(** Pair the pullback mediator with the original base transpose. *)

(** 将拉回中介与原基转置配对。 *)

Program Definition gluing_curry {Z : @Ob (Gluing F)}
    (f : (@Hom (Gluing F)) ((Z × X)%ob) Y)
  : (@Hom (Gluing F)) Z GluingExp
  :=
  {|comma_left := gluing_curry_left f
  ; comma_right := ƛ (comma_right f)
  |}.
Next Obligation.
  symmetry. exact (snd (this (gluing_curry_left_unique f))).
Defined.

(** Evaluation after transposition recovers both components of the square. *)

(** 转置后求值恢复方形的两个分量。 *)

Lemma gluing_exp_β {Z : @Ob (Gluing F)}
    (f : (@Hom (Gluing F)) ((Z × X)%ob) Y)
  : gluing_eval ∘ (gluing_curry f × id) ≈ f.
Proof.
  split.
  - change (comma_left gluing_eval ∘
      comma_left (gluing_curry f × id) ≈ comma_left f).
    rewrite gluing_cross_left.
    change ((eval ∘ (p × id)) ∘ (gluing_curry_left f × id) ≈ comma_left f).
    rewrite comp_assoc, <- cross_comp, comp_id_l.
    change (uncurry (p ∘ gluing_curry_left f) ≈ comma_left f).
    rewrite (fst (this (gluing_curry_left_unique f))).
    apply exp_β.
  - change (comma_right gluing_eval ∘
      comma_right (gluing_curry f × id) ≈ comma_right f).
    rewrite gluing_cross_right. apply exp_β.
Qed.

(** A square with the same evaluation has the same base transpose and
    the same two pullback projections, hence is the selected transpose. *)

(** 具有相同求值的方形具有相同基转置及两个拉回投影，因此等于选定转置。 *)

Lemma gluing_exp_unique {Z : @Ob (Gluing F)}
    (f : (@Hom (Gluing F)) ((Z × X)%ob) Y)
    (k : (@Hom (Gluing F)) Z GluingExp)
    (H : gluing_eval ∘ (k × id) ≈ f)
  : k ≈ gluing_curry f.
Proof.
  assert (right : comma_right k ≈ ƛ (comma_right f)).
  { apply exp_curry_unique.
    transitivity (comma_right gluing_eval ∘
      comma_right (k × (@Cats.Cat.Core.id (Gluing F) X))).
    - rewrite gluing_cross_right. reflexivity.
    - exact (snd H). }
  assert (left : p ∘ comma_left k ≈ ƛ (comma_left f)).
  { apply exp_curry_unique.
    transitivity (comma_left gluing_eval ∘
      comma_left (k × (@Cats.Cat.Core.id (Gluing F) X))).
    - rewrite gluing_cross_left.
      change (eval ∘ ((p ∘ comma_left k) × id) ≈
        (eval ∘ (p × id)) ∘ (comma_left k × id)).
      rewrite comp_assoc, <- cross_comp, comp_id_l. reflexivity.
    - exact (fst H). }
  split.
  - apply (gluing_curry_left_unique f). split.
    + exact left.
    + rewrite <- right. symmetry. exact (comma_comm k).
  - exact right.
Qed.

(** The candidate transpose respects hom equality without comparing any
    commuting-square or pullback witnesses. *)

(** 候选转置保持 Hom 相等，无须比较交换方形或拉回的见证。 *)

Global Instance gluing_curry_proper {Z : @Ob (Gluing F)}
  : Proper (≈[Z × X, Y] ==> ≈[Z, GluingExp])
      (@gluing_curry Z).
Proof.
  intros f g H. apply gluing_exp_unique.
  rewrite gluing_exp_β. exact H.
Qed.

(** The supplied pullback proves the full candidate exponential property.
    The mediator is transparent and no equality of square proofs is used. *)

(** 指定拉回给出完整候选指数泛性质。中介透明，且不使用方形证明的相等。 *)

Definition gluing_exp_universal
  : @is_exp (Gluing F) PG X Y GluingExp gluing_eval.
Proof.
  intros Z f. exists (gluing_curry f).
  refine {|this := _
         ; that := _
         |}.
  - exact (gluing_exp_β f).
  - intros k H. exact (gluing_exp_unique f k H).
Defined.

End GluingExp.
