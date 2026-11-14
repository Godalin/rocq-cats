From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Functor.Product
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.Lift.

(** * Coherent Kripke Function Values

    The worlds form an arbitrary category [C]. For presheaves [F] and [G],
    a function value at [X] accepts an arrow [Y → X] and an argument in
    [F Y], returning a result in [G Y]. It must respect both input equalities
    and commute with further reindexing. An arbitrary family of functions
    over future worlds would not supply this coherence.

    These are the componentwise data of a map from the product of the
    representable at [X] and [F] into [G]. We keep the application view
    explicit so world hom equality and value equality may have different
    sizes. Equality of function values only compares results pointwise;
    it never compares stored preservation or coherence witnesses.

    Function carriers must be large enough to store their laws. Pointwise
    equality need only quantify worlds, world arrows and arguments, followed
    by equality in [G]. These are different bounds, not an equality of the
    two universes. No function extensionality or proof irrelevance is used. *)

(** * 相容的 Kripke 函数值

    世界组成任意范畴 [C]。给定预层 [F]、[G]，在 [X] 处的函数值接受箭头
    [Y → X] 以及 [F Y] 中的实参，返回 [G Y] 中的结果。它须保持两种输入
    相等，并与进一步重索引交换。任意未来世界上的函数族本身不提供这种相容性。

    这些正是从 [X] 处可表预层与 [F] 的积到 [G] 的映射的逐分量数据。
    这里显式保留应用视图，使世界 Hom 相等与值相等具有不同大小。函数值的
    相等仅逐点比较结果，从不比较所保存的保持律或相容律见证。

    函数载体须足以保存定律；逐点相等只须量化世界、世界箭头与实参，再使用
    [G] 中的相等。这是不同的界限，不是两个宇宙相等。不使用函数外延性或
    证明无关性。 *)

Section KripkeFunctions.
Context {C : Cat} (F G : Fct (C^op) SetCat).

(** Application, respectfulness and reindexing coherence form one value.
    The unique function coercion exposes future-world application. *)

(** 应用、保相等性质与重索引相容律组成一个值；唯一的函数强制转换暴露未来
    世界中的应用。 *)

Record KripkeFunction (X : @Ob C)
  :=
  { kripke_apply :> ∀ Y : @Ob C, Hom Y X → F Y → G Y
  ; kripke_apply_proper Y
    :: Proper (HomEq ==> [≈S] ==> [≈S]) (kripke_apply Y)
  ; kripke_naturality
      : ∀ (Y Z : @Ob C) (f : Hom Y X) (g : Hom Z Y) (x : F Y),
        fmap G g (kripke_apply Y f x) ≈S
          kripke_apply Z (f ∘ g) (fmap F g x)
  }.

(** Equality observes every future application, without comparing laws. *)

(** 相等观察每个未来应用，不比较定律。 *)

Definition KripkeFunctionEq {X : @Ob C} (k h : KripkeFunction X)
  : Type
  := ∀ Y (f : Hom Y X) (x : F Y), k Y f x ≈S h Y f x.

(** Pointwise equality inherits the codomain equivalence laws. *)

(** 逐点相等继承余域的等价律。 *)

Global Instance KripkeFunctionEq_Equivalence {X : @Ob C}
  : Equivalence (@KripkeFunctionEq X).
Proof.
  split.
  - intros k Y f x. reflexivity.
  - intros k h p Y f x. symmetry. apply p.
  - intros k h j p q Y f x. transitivity (h Y f x); [apply p | apply q].
Defined.

(** The function-value setoid retains all computational fields. *)

(** 函数值广集保留全部计算字段。 *)

Program Definition KripkeFunctionS (X : @Ob C)
  : SetC
  :=
  {|carrier := KripkeFunction X
  ; carrier_equiv := KripkeFunctionEq
  |}.

(** Restrict a function value along a world arrow by precomposing the
    supplied future arrow. The action on arguments is already at that
    future world, so no arbitrary transport is required. *)

(** 沿世界箭头限制函数值：将所给未来箭头预合成。实参本就在该未来世界中，
    因而无须任意运输。 *)

Program Definition kripke_reindex {X Y : @Ob C} (f : Hom Y X)
    (k : KripkeFunction X)
  : KripkeFunction Y
  :=
  {|kripke_apply Z g x := k Z (f ∘ g) x
  |}.
Next Obligation.
  intros g h p x y q. apply kripke_apply_proper; [now rewrite p | exact q].
Defined.
Next Obligation.
  etransitivity.
  - apply kripke_naturality.
  - apply kripke_apply_proper; [apply comp_assoc | reflexivity].
Defined.

(** Restriction respects both the world arrow and the function value. *)

(** 限制同时保持世界箭头与函数值的相等。 *)

Global Instance kripke_reindex_proper {X Y : @Ob C}
  : Proper (HomEq ==> KripkeFunctionEq ==> KripkeFunctionEq)
      (@kripke_reindex X Y).
Proof.
  intros f g p k h q Z a x. cbn.
  transitivity (h Z (f ∘ a) x).
  - apply q.
  - apply kripke_apply_proper; [now rewrite p | reflexivity].
Defined.

(** Restriction as a respectful setoid map. *)

(** 作为广集保相等映射的限制。 *)

Program Definition kripke_reindex_resp {X Y : @Ob C} (f : Hom Y X)
  : KripkeFunctionS X →r KripkeFunctionS Y
  :=
  {|func := kripke_reindex f
  |}.

(** Coherent function values form a presheaf on the same worlds. *)

(** 相容函数值在同一世界范畴上组成预层。 *)

Program Definition KripkeFunctionF
  : Fct (C^op) SetCat
  :=
  {|F0 := KripkeFunctionS
  ; F1 _ _ f := kripke_reindex_resp f
  |}.
Next Obligation.
  intros f g p k. apply kripke_reindex_proper; [exact p | reflexivity].
Defined.
Next Obligation.
  intros k Y f x. cbn. apply kripke_apply_proper;
    [apply comp_id_l | reflexivity].
Defined.
Next Obligation.
  intros k W h x. cbn. apply kripke_apply_proper;
    [apply comp_assoc | reflexivity].
Defined.

(** Apply a function value in its current world by supplying the identity.
    Future-world application can equivalently restrict first, then apply. *)

(** 传入恒等箭头，在当前世界应用函数值；未来世界应用也可先限制再应用。 *)

Definition kripke_eval {X : @Ob C} (k : KripkeFunction X) (x : F X)
  : G X
  := k X id x.

(** Application respects function-value equality and argument equality. *)

(** 应用保持函数值相等与实参相等。 *)

Global Instance kripke_eval_proper {X : @Ob C}
  : Proper (KripkeFunctionEq ==> [≈S] ==> [≈S]) (@kripke_eval X).
Proof.
  intros k h p x y q. unfold kripke_eval.
  transitivity (h X id x).
  - apply p.
  - apply kripke_apply_proper; [reflexivity | exact q].
Defined.

(** Application commutes with reindexing both function and argument. *)

(** 应用与函数和实参的同时重索引交换。 *)

Lemma kripke_eval_reindex {X Y : @Ob C} (f : Hom Y X)
    (k : KripkeFunction X) (x : F X)
  : fmap G f (kripke_eval k x) ≈S
      kripke_eval (kripke_reindex f k) (fmap F f x).
Proof.
  unfold kripke_eval. cbn.
  transitivity (k Y (id ∘ f) (fmap F f x)).
  - apply kripke_naturality.
  - apply kripke_apply_proper; [rewrite comp_id_l, comp_id_r; reflexivity
      | reflexivity].
Defined.

End KripkeFunctions.

Arguments kripke_apply {_ _ _ _} _ _ _ _.

Notation "G '^K' F" := (KripkeFunctionF F G)
  (at level 30, right associativity) : cat_scope.

(** ** Currying across Explicit Size Bounds

    Fix a world category [C] and presheaves [F], [G] and [H]. Construct
    currying and uncurrying, then prove their beta/eta and universal laws.
    Pointwise products use the chosen setoid product. The function presheaf
    may live in larger value universes because it stores preservation laws.
    The source of a curried map is therefore explicitly lifted into that
    larger set category. This does not resize anything downward. *)

(** ** 跨显式大小界限的柯里化

    固定世界范畴 [C] 与预层 [F]、[G]、[H]，构造柯里化和反柯里化，并证明
    β、η 及泛性质定律。逐点积使用选定的广集积。函数预层保存保持律，因而
    可能位于更大的值宇宙；
    柯里化映射的源显式提升到该较大的集合范畴中，不向下重设任何大小。 *)

Section KripkeCurrying.
Context {C : Cat} (F G H : Fct (C^op) SetCat).
Local Existing Instance SetCat_HasProduct.

(** A map on pairs produces a coherent function at every parameter value.
    Future parameters are obtained by reindexing that fixed value. *)

(** 配对上的映射在每个参数值处产生相容函数；未来参数通过重索引该固定值获得。 *)

Program Definition kripke_curry_at
    (α : PointwiseProductF H F ⇒ G) (X : @Ob C) (h : H X)
  : KripkeFunction F G X
  :=
  {|kripke_apply Y f x := α Y (fmap H f h, x)
  |}.
Next Obligation.
  intros f g p x y q. apply func_proper. split.
  - exact (@functor_fmap_proper (C^op) SetCat H X Y f g p h).
  - exact q.
Defined.
Next Obligation.
  transitivity (α Z (fmap H g (fmap H f h), fmap F g x)).
  - symmetry. exact (nt_naturality α g (fmap H f h, x)).
  - apply func_proper. split.
    + symmetry. exact (functor_comp _ _ H g f h).
    + reflexivity.
Defined.

(** Currying preserves pointwise equality of the parameter. *)

(** 柯里化保持参数的逐点相等。 *)

Global Instance kripke_curry_at_proper
    (α : PointwiseProductF H F ⇒ G) (X : @Ob C)
  : Proper ([≈S] ==> KripkeFunctionEq F G) (kripke_curry_at α X).
Proof.
  intros h j p Y f x. cbn. apply func_proper. split.
  - apply func_proper. exact p.
  - reflexivity.
Defined.

(** Reindexing a curried function agrees with reindexing its parameter. *)

(** 重索引柯里化函数，与重索引其参数相同。 *)

Lemma kripke_curry_at_reindex (α : PointwiseProductF H F ⇒ G)
    {X Y : @Ob C} (f : Hom Y X) (h : H X)
  : KripkeFunctionEq F G
      (kripke_reindex F G f (kripke_curry_at α X h))
      (kripke_curry_at α Y (fmap H f h)).
Proof.
  intros Z g x. cbn. apply func_proper. split.
  - exact (functor_comp _ _ H g f h).
  - reflexivity.
Defined.

(** The curried natural transformation explicitly lifts its parameter
    presheaf to the function presheaf's ambient value universes. *)

(** 柯里化自然变换显式将参数预层提升到函数预层所在的值宇宙。 *)

Program Definition KripkeCurryN (α : PointwiseProductF H F ⇒ G)
  : LiftF ∘F H ⇒ G ^K F
  :=
  {|nt X :=
     {|func h := kripke_curry_at α X (lower h)
     |}
  |}.
Next Obligation.
  intros [h] [j] [p]. apply kripke_curry_at_proper. exact p.
Defined.
Next Obligation.
  intros [h]. symmetry. apply kripke_curry_at_reindex.
Defined.

(** Uncurrying applies the function at the identity of the current world.
    Its result is in the original, unlifted codomain presheaf. *)

(** 反柯里化在当前世界的恒等箭头处应用函数，结果位于原先未提升的余域预层中。 *)

Program Definition KripkeUncurryN
    (β : LiftF ∘F H ⇒ G ^K F)
  : PointwiseProductF H F ⇒ G
  :=
  {|nt X :=
     {|func p := kripke_eval F G
         (β X {|lower := fst p
               |}) (snd p)
     |}
  |}.
Next Obligation.
  intros [h x] [j y] [p q]. apply kripke_eval_proper.
  - exact (@func_proper _ _ (β X)
      {|lower := h
      |} {|lower := j
          |} {|lower := p
              |}).
  - exact q.
Defined.
Next Obligation.
  intros [h x]. symmetry.
  transitivity (kripke_eval F G
      (kripke_reindex F G f (β X {|lower := h
                                |})) (fmap F f x)).
  - apply kripke_eval_reindex.
  - apply kripke_eval_proper; [| reflexivity].
    symmetry. exact (nt_naturality β f {|lower := h
                                      |}).
Defined.

(** Evaluation after currying recovers the original transformation. *)

(** 柯里化后再求值恢复原自然变换。 *)

Lemma kripke_curry_β (α : PointwiseProductF H F ⇒ G)
  : KripkeUncurryN (KripkeCurryN α) ≈N α.
Proof.
  intros X [h x]. cbn. apply func_proper. split.
  - exact (functor_id _ _ H h).
  - reflexivity.
Defined.

(** A coherent function family is recovered from its current-world
    evaluations, up to pointwise equality of natural transformations. *)

(** 从当前世界中的求值可以恢复相容函数族，恢复按自然变换的逐点相等成立。 *)

Lemma kripke_curry_η (β : LiftF ∘F H ⇒ G ^K F)
  : KripkeCurryN (KripkeUncurryN β) ≈N β.
Proof.
  intros X [h] Y f x. cbn.
  transitivity (β X {|lower := h
                    |} Y (f ∘ id) x).
  - exact (nt_naturality β f {|lower := h
                            |} Y id x).
  - apply kripke_apply_proper; [apply comp_id_r | reflexivity].
Defined.

(** Currying preserves pointwise equality of the uncurried map. *)

(** 柯里化保持未柯里化映射的逐点相等。 *)

Global Instance KripkeCurryN_proper
  : Proper (NatEq ==> NatEq) KripkeCurryN.
Proof. intros α β p X [h] Y f x. apply p. Defined.

(** Uncurrying preserves pointwise equality of coherent function families. *)

(** 反柯里化保持相容函数族的逐点相等。 *)

Global Instance KripkeUncurryN_proper
  : Proper (NatEq ==> NatEq) KripkeUncurryN.
Proof. intros α β p X [h x]. apply p. Defined.

(** A transpose is uniquely determined by its uncurried map. *)

(** 转置由其未柯里化映射唯一确定。 *)

Lemma kripke_curry_unique (α : PointwiseProductF H F ⇒ G)
    (β : LiftF ∘F H ⇒ G ^K F)
    (p : KripkeUncurryN β ≈N α)
  : β ≈N KripkeCurryN α.
Proof.
  transitivity (KripkeCurryN (KripkeUncurryN β)).
  - symmetry. apply kripke_curry_η.
  - apply KripkeCurryN_proper. exact p.
Defined.

(** The full size-aware transposition property retains a chosen mediator,
    its evaluation equation and uniqueness, all without selecting global
    exponential structures on an arbitrary fixed-size presheaf category. *)

(** 完整的大小敏感转置性质保留选定中介、求值方程及唯一性，并不在任意固定
    大小的预层范畴中全局选定指数结构。 *)

Definition kripke_curry_universal (α : PointwiseProductF H F ⇒ G)
  : ∃ β : LiftF ∘F H ⇒ G ^K F,
      is_unique (λ β, KripkeUncurryN β ≈N α) β.
Proof.
  exists (KripkeCurryN α).
  refine {|this := _
         ; that := _
         |}.
  - apply kripke_curry_β.
  - intros β p. apply kripke_curry_unique. exact p.
Defined.

End KripkeCurrying.
