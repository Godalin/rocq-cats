From Cats Require Export
  Cat.Applicative.Morphism
  Cat.Monoidal.Natural.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Monoid.
From Cats.Set Require Import
  Constant.

Local Open Scope monoidal_scope.
Local Open Scope applicative_scope.
Local Existing Instance SetCat_HasTerminal.
Local Existing Instance SetCat_HasProduct.

(** * Pure Values from Native Setoid Lax Functors *)

(** * 从原生广集 Lax 函子恢复纯值 *)

(** ** A Functor and a Terminal Value

    Fix a native setoid endofunctor with independent carrier and equality
    universes. A value at the singleton determines a natural pure map by
    functor action on constant maps. No lax structure or coend is needed. *)

(** ** 函子与终对象处的值

    固定原生广集自函子，载体与相等宇宙独立。单元素广集处的一个值，通过函子
    对常值映射的作用决定自然纯值映射；不要求 lax 结构或 coend。 *)

Section Pure.
Universes u p.
Context (F : Fct (SetCat@{u p _ _ _ _ _})
    (SetCat@{u p _ _ _ _ _})) (e : F UnitS).

(** Map the chosen terminal value along the constant with the supplied value. *)

(** 沿取所给值的常值映射，映射选定终值。 *)

Program Definition set_pure_map (X : SetC@{u p})
  : X →r F X
  :=
  {|func x := fmap F (const_resp UnitS x) e
  |}.
Next Obligation.
  intros x y E. apply (@fmap_proper _ _ _ _ (@isFct SetCat SetCat F) _ _).
  intros []. exact E.
Defined.

(** Functor composition gives naturality in the ordinary value type. *)

(** 函子复合律给出关于通常值类型的自然性。 *)

Program Definition SetPureN
  : (@IdF (SetCat@{u p _ _ _ _ _})) ⇒ F
  :=
  {|nt X := set_pure_map X
  |}.
Next Obligation.
  intros x. change (fmap F (const_resp UnitS (f x)) e ≈S
    fmap F f (fmap F (const_resp UnitS x) e)).
  transitivity (fmap F (f ∘r const_resp UnitS x) e).
  - apply (@fmap_proper _ _ _ _ (@isFct SetCat SetCat F) _ _).
    intros []. reflexivity.
  - exact (@fmap_comp _ _ _ _ (@isFct SetCat SetCat F) _ _ _ _ _ e).
Qed.

(** At the singleton, the chosen value is recovered in specified equality. *)

(** 在单元素广集处，按指定相等恢复选定值。 *)

Lemma set_pure_unit
  : SetPureN UnitS ≈ const_resp UnitS e.
Proof.
  intros []. change (fmap F (@const_resp UnitS UnitS tt) e ≈S e).
  transitivity (fmap F (@Cat.Core.id SetCat UnitS) e).
  - apply (@fmap_proper _ _ _ _ (@isFct SetCat SetCat F) _ _).
    intros []. reflexivity.
  - exact (@fmap_id _ _ _ _ (@isFct SetCat SetCat F) UnitS e).
Defined.

(** Naturality at constants determines every supplied pure transformation
    from its singleton value; no equality of transformation records is used. *)

(** 常值处的自然性由单元素值决定任意所给纯值变换；不比较变换记录相等。 *)

Lemma set_pure_unique (η : (@IdF SetCat) ⇒ F)
    (Hη : η UnitS tt ≈S e)
  : η ≈N SetPureN.
Proof.
  intros X x. transitivity (fmap F (const_resp UnitS x) (η UnitS tt)).
  - exact (nat_naturality η (const_resp UnitS x) tt).
  - change (fmap F (const_resp UnitS x) (η UnitS tt) ≈S
      fmap F (const_resp UnitS x) e).
    apply func_proper. exact Hη.
Defined.

End Pure.

(** ** Lax Structure Supplies Lawful Applicative Pure

    Fix a cartesian lax endofunctor of the same native setoid category.
    Its unit supplies the singleton value. Tensorator naturality and its
    left unit law suffice for pure pairing; all lax data are retained. *)

(** ** Lax 结构给出满足 Applicative 定律的纯值

    固定同一原生广集范畴上的笛卡尔 lax 自函子。其单位提供单元素值。张量子
    自然性及左单位律足以证明纯值配对；全部 lax 数据原样保留。 *)

Section Lax.
Universes u p.
Let SM
  : HasMonoidal (SetCat@{u p _ _ _ _ _})
  := SetCartMonoidal.
Context (L : LaxMonoidalFct SM SM).

(** The lax unit determines pure values without selecting a strength. *)

(** Lax 单位决定纯值，无须另选强度。 *)

Definition SetLaxPureN
  : (@IdF (SetCat@{u p _ _ _ _ _})) ⇒ L
  := SetPureN L (lax_unit L tt).

(** The recovered terminal component is the original lax unit map. *)

(** 恢复所得终分量是原 lax 单位映射。 *)

Lemma set_lax_pure_unit
  : SetLaxPureN UnitS ≈ lax_unit L.
Proof. intros []. exact (set_pure_unit L (lax_unit L tt) tt). Defined.

(** The original tensorator combines recovered pure values into their pair.
    Only its naturality and the original left unit equation are used. *)

(** 原张量子将恢复所得两个纯值组合为其配对，只使用其自然性及原左单位方程。 *)

Lemma set_lax_pure_product (X Y : SetC@{u p})
  : SetLaxPureN (X ×S Y) ≈
      lax_tensorN L (X,Y) ∘ (SetLaxPureN X × SetLaxPureN Y).
Proof.
  intros [x y].
  change (fmap L (const_resp UnitS (x,y)) (lax_unit L tt) ≈S
    lax_tensorN L (X,Y)
      (fmap L (const_resp UnitS x) (lax_unit L tt),
       fmap L (const_resp UnitS y) (lax_unit L tt))).
  pose proof (lax_unit_l L UnitS (tt,lax_unit L tt)) as Hu.
  change (fmap L (π2 : UnitS ×S UnitS →r UnitS)
    (lax_tensorN L (UnitS,UnitS) (lax_unit L tt,lax_unit L tt)) ≈S
      lax_unit L tt) in Hu.
  transitivity (fmap L (const_resp UnitS (x,y))
    (fmap L (π2 : UnitS ×S UnitS →r UnitS)
      (lax_tensorN L (UnitS,UnitS) (lax_unit L tt,lax_unit L tt)))).
  - apply func_proper. symmetry. exact Hu.
  - transitivity (fmap L (const_resp UnitS x × const_resp UnitS y)
      (lax_tensorN L (UnitS,UnitS) (lax_unit L tt,lax_unit L tt))).
    + transitivity (fmap L (const_resp UnitS (x,y) ∘r
        (π2 : UnitS ×S UnitS →r UnitS))
        (lax_tensorN L (UnitS,UnitS) (lax_unit L tt,lax_unit L tt))).
      * symmetry. exact (@fmap_comp _ _ _ _ (@isFct SetCat SetCat L) _ _ _ _ _ _).
      * apply (@fmap_proper _ _ _ _ (@isFct SetCat SetCat L) _ _).
        intros [[] []]. split; reflexivity.
    + symmetry.
      pose proof (lax_tensor_natural L (const_resp UnitS x)
        (const_resp UnitS y)) as H.
      unfold SM, SetCartMonoidal in H.
      rewrite !cartesian_tensor_map in H.
      exact (H (lax_unit L tt,lax_unit L tt)).
Defined.

(** Explicitly choose the native Applicative. The parent is exactly [L];
    import introduces no global selection or alternative coercion path. *)

(** 显式选择原生 Applicative，父结构恰为 [L]；导入不添加全局选择或强制转换路径。 *)

Program Definition SetLaxA
  : Applicative (SetCat@{u p _ _ _ _ _})
      SetCat_HasTerminal SetCat_HasProduct
  :=
  {|ApplicativeToLaxMonoidalFct := L
  ; applicative_pure := SetLaxPureN
  ; applicative_pure_unit := set_lax_pure_unit
  ; applicative_pure_product := set_lax_pure_product
  |}.

End Lax.

(** ** Preservation and Recovery

    On native setoids, naturality and preservation of the lax unit imply
    preservation of canonical pure values. Compare the existing Type-valued
    preservation predicates and recover any supplied Applicative pure. *)

(** ** 保持性与恢复

    在原生广集上，自然性与 lax 单位保持性推出规范纯值保持性。比较已有 Type
    值保持性谓词，并恢复任意所给 Applicative 的纯值。 *)

Section Preservation.
Universes u p.
Let SC
  : Cat
  := SetCat@{u p _ _ _ _ _}.
Let SM
  : HasMonoidal SC
  := SetCartMonoidal.

(** Unit preservation already determines pure preservation pointwise. *)

(** 单位保持性已经逐点决定纯值保持性。 *)

Lemma set_lax_hom_pure (L K : LaxMonoidalFct SM SM) (α : L ⇒ K)
    (Hu : α UnitS ∘ lax_unit L ≈ lax_unit K)
  : ∀ X, α X ∘ pure[SetLaxA L] X ≈ pure[SetLaxA K] X.
Proof.
  intros X x.
  change (α X (fmap L (const_resp UnitS x) (lax_unit L tt)) ≈S
    fmap K (const_resp UnitS x) (lax_unit K tt)).
  transitivity (fmap K (const_resp UnitS x) (α UnitS (lax_unit L tt))).
  - exact (nat_naturality α (const_resp UnitS x) (lax_unit L tt)).
  - apply func_proper. exact (Hu tt).
Defined.

(** Existing Applicative and monoidal preservation laws coincide for these
    explicit native lifts. Tensor actions are compared by their product law. *)

(** 对这些显式原生提升，已有 Applicative 与幺半保持律等价；张量作用经积映射律比较。 *)

Lemma set_lax_applicative_hom (L K : LaxMonoidalFct SM SM) (α : L ⇒ K)
  : is_applicative_hom (SetLaxA L) (SetLaxA K) α ↔
      is_lax_monoidal_hom L K α.
Proof.
  split.
  - intros H. split.
    + exact (applicative_hom_unit (SetLaxA L) (SetLaxA K) α H).
    + intros X Y.
      transitivity (lax_tensorN K (X,Y) ∘
        (@cross SC SetCat_HasProduct _ _ _ _ (α X) (α Y))).
      * exact (snd H X Y).
      * apply comp_proper; [reflexivity|]. symmetry.
        exact (@cartesian_tensor_map SC SetCat_HasTerminal
          SetCat_HasProduct _ _ _ _ (α X) (α Y)).
  - intros [Hu Ht]. split.
    + exact (set_lax_hom_pure L K α Hu).
    + intros X Y.
      transitivity (lax_tensorN K (X,Y) ∘
        (tensor_map (IM := HasMonoidal_interchange SM) (α X) (α Y))).
      * exact (Ht X Y).
      * apply comp_proper; [reflexivity|].
        exact (@cartesian_tensor_map SC SetCat_HasTerminal
          SetCat_HasProduct _ _ _ _ (α X) (α Y)).
Defined.

(** A supplied Applicative's pure agrees naturally with the canonical pure
    of its exact inherited lax parent. Only its terminal pure law is needed. *)

(** 所给 Applicative 的纯值与其相同继承 lax 父结构的规范纯值自然相等，
    这里只需终纯值定律。 *)

Lemma set_applicative_pure_roundtrip
    (A : Applicative SC SetCat_HasTerminal SetCat_HasProduct)
  : pure[A] ≈N pure[SetLaxA A].
Proof.
  exact (set_pure_unique A (lax_unit A tt) (pure[A])
    (applicative_pure_unit A tt)).
Defined.

(** For any supplied native Applicatives, pure preservation adds no further
    restriction to monoidal transformations of their inherited lax parents. *)

(** 对任意所给原生 Applicative，纯值保持性不会对继承 lax 父结构的幺半变换
    增加额外限制。 *)

Lemma set_applicative_hom_lax
    (A B : Applicative SC SetCat_HasTerminal SetCat_HasProduct)
    (α : A ⇒ B)
  : is_applicative_hom A B α ↔ is_lax_monoidal_hom A B α.
Proof.
  split.
  - intros H. apply (fst (set_lax_applicative_hom A B α)). split.
    + intros X x.
      transitivity (α X (pure[A] X x)).
      * apply (@func_proper _ _ (α X)). symmetry.
        exact (set_applicative_pure_roundtrip A X x).
      * transitivity (pure[B] X x).
        -- exact (fst H X x).
        -- exact (set_applicative_pure_roundtrip B X x).
    + exact (snd H).
  - intros H. pose proof (snd (set_lax_applicative_hom A B α) H) as K.
    split.
    + intros X x.
      transitivity (α X (pure[SetLaxA A] X x)).
      * apply (@func_proper _ _ (α X)).
        exact (set_applicative_pure_roundtrip A X x).
      * transitivity (pure[SetLaxA B] X x).
        -- exact (fst K X x).
        -- symmetry. exact (set_applicative_pure_roundtrip B X x).
    + exact (snd K).
Defined.

(** Identity components preserve the recovered and original operations. *)

(** 恒等分量保持恢复所得及原有运算。 *)

Lemma set_applicative_roundtrip_hom
    (A : Applicative SC SetCat_HasTerminal SetCat_HasProduct)
  : is_applicative_hom (SetLaxA A) A IdN.
Proof.
  split.
  - intros X x. symmetry. exact (set_applicative_pure_roundtrip A X x).
  - intros X Y [x y]. reflexivity.
Defined.

(** Reuse general chosen-inverse preservation for the reverse identity. *)

(** 反向恒等比较复用一般的指定逆保持性。 *)

Lemma set_applicative_roundtrip_inv_hom
    (A : Applicative SC SetCat_HasTerminal SetCat_HasProduct)
  : is_applicative_hom A (SetLaxA A) IdN.
Proof.
  exact (applicative_hom_inverse (SetLaxA A) A IdN
    (set_applicative_roundtrip_hom A) (nat_id_iso A)).
Defined.

End Preservation.
