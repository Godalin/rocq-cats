From Cats Require Export
  Cat.Monoidal.Monoidal
  Cat.Induced.

Local Open Scope monoidal_scope.
Local Open Scope ob_scope.

(** * Computation with Monoidal Contexts

    A pure-arrow functor sends values into a computation category. The
    additional action carries an ordinary left tensor context through a
    computation. Its laws express functoriality, naturality and monoidal
    coherence, without products, symmetry or interchange of two effects.
    Cartesian specialization supplies the familiar Haskell Arrow operations.
    This is distinct from the category whose objects are arrows. *)

(** * 带幺半上下文的计算

    纯箭头函子将值送入计算范畴，新增作用让计算携带左侧通常张量上下文。
    定律表达函子性、自然性及幺半相干，不要求积、对称性或两个效应的交换律。
    笛卡尔特化提供熟悉的 Haskell Arrow 运算。这不同于以箭头为对象的范畴。 *)

(** Choose the left context action on a fixed pure functor. Pure lifting
    uses the functor's own identity and composition laws. *)

(** 在固定的纯函子上选取左上下文作用。纯提升使用函子自身的恒等与复合定律。 *)

Minks.Mixin HasArrow {C K : Cat}
    `{MC : !HasMonoidal C} (F : Fct C K)
  :=
  (** Carry a left context through the computation, without running an
      additional effect in that context. *)

  (** 将左上下文穿过计算，不在此上下文中运行额外效应。 *)

  { arrow_context {X Y : C} (Z : C)
      (f : Hom (F X) (F Y))
    : Hom (F (Z ⊗ X)) (F (Z ⊗ Y))

  (** The action preserves specified computation equality. *)

  (** 此作用保持指定计算相等。 *)

  ; arrow_context_proper {X Y : C} (Z : C)
    :: Proper (HomEq ==> HomEq) (@arrow_context X Y Z)

  (** Extending a pure arrow is the pure tensor map. *)

  (** 扩展纯箭头就是纯张量映射。 *)

  ; arrow_context_arr {X Y : C} (Z : C) (f : Hom X Y)
    : arrow_context Z (fmap F f) ≈ fmap F (id ⊗ f)

  (** Extending a sequence preserves its execution order. *)

  (** 扩展顺序组合，保持执行次序。 *)

  ; arrow_context_comp {X Y W : C} (Z : C)
      (g : Hom (F Y) (F W))
      (f : Hom (F X) (F Y))
    : arrow_context Z (g ∘ f) ≈ arrow_context Z g ∘ arrow_context Z f

  (** Ordinary substitution in the context commutes with a computation. *)

  (** 上下文中的通常代入与计算交换。 *)

  ; arrow_context_natural {X Y Z W : C}
      (f : Hom (F X) (F Y)) (h : Hom Z W)
    : fmap F (h ⊗ id) ∘ arrow_context Z f
      ≈ arrow_context W f ∘ fmap F (h ⊗ id)

  (** A unit context can be removed by the pure left unitor. *)

  (** 单位上下文可以用纯左单位子移去。 *)

  ; arrow_context_unit {X Y : C}
      (f : Hom (F X) (F Y))
    : fmap F λ[Y] ∘ arrow_context 𝐈 f
      ≈ f ∘ fmap F λ[X]

  (** Successive ordinary contexts agree with their tensor after pure
      reassociation. No two effectful computations are exchanged. *)

  (** 逐次通常上下文经纯括号重排后与其张量一致，不交换两个带效应计算。 *)

  ; arrow_context_assoc {X Y Z W : C}
      (f : Hom (F X) (F Y))
    : fmap F α[Z; W; Y] ∘ arrow_context (Z ⊗ W) f
      ≈ arrow_context Z (arrow_context W f) ∘ fmap F α[Z; W; X]
  }.

Arguments arrow_context {_ _ _} _ {_ _ _} _ _.
Arguments arrow_context_proper {_ _ _} _ {_ _ _} _.
Arguments arrow_context_arr {_ _ _} _ {_ _ _} _ _.
Arguments arrow_context_comp {_ _ _} _ {_ _ _ _} _ _ _.
Arguments arrow_context_natural {_ _ _} _ {_ _ _ _ _} _ _.
Arguments arrow_context_unit {_ _ _} _ {_ _ _} _.
Arguments arrow_context_assoc {_ _ _} _ {_ _ _ _ _} _.

(** Bundle the pure functor with its context action. *)

(** 将纯函子及其上下文作用打包为计算 Arrow。 *)

Minks.Struct Arrow (C K : Cat) `{MC : !HasMonoidal C}
  extends Fct C K
  with  hasArrow as hasArrow
        : HasArrow [C, K, MC, carrier].

Arguments MakeArrow {_ _ _} _ _.
Arguments ArrowToFct {_ _ _} _.
Arguments hasArrow {_ _ _} _.

Declare Scope computation_scope.
Delimit Scope computation_scope with computation.
Notation "'arr[' A ';' f ']'" := (fmap A f)
  (at level 0, format "arr[ A ;  f ]")
  : computation_scope.
Notation "'context[' A ';' Z ';' f ']'"
  := (@arrow_context _ _ _ _ (hasArrow A) _ _ Z f)
  (at level 0, format "context[ A ;  Z ;  f ]")
  : computation_scope.
Local Open Scope computation_scope.

(** ** The Induced Computation Category

    Fix a computational Arrow over a named monoidal category. Reindex its
    computations by value objects and derive pure and fixed-context functors. *)

(** ** 诱导计算范畴

    固定具名幺半范畴上的计算 Arrow，按值对象重索引计算，并导出纯态射及固定上下文函子。 *)

Section Derived.
Context {C K : Cat} `{MC : !HasMonoidal C} (A : @Arrow C K MC).

(** Reindex the existing computation category by the pure object map. *)

(** 沿纯对象映射重索引已有计算范畴。 *)

Definition ComputationCat
  : Cat
  := InducedCat C A.

(** Pure identity is computation identity. *)

(** 纯恒等就是计算恒等。 *)

Lemma arrow_arr_id (X : C)
  : arr[A; id[X]] ≈ id.
Proof. apply fmap_id. Qed.

(** Pure lifting preserves ordinary composition. *)

(** 纯提升保持通常复合。 *)

Lemma arrow_arr_comp {X Y Z : C}
    (g : Hom Y Z) (f : Hom X Y)
  : arr[A; g ∘ f] ≈ arr[A; g] ∘ arr[A; f].
Proof. apply fmap_comp. Qed.

(** Fixed-context extension is a functor on computations. *)

(** 固定上下文扩展是计算上的函子。 *)

Program Definition ContextF (Z : C)
  : Fct ComputationCat ComputationCat
  :=
  {|fobj X := Z ⊗ X
  ; fmap X Y f := context[A; Z; f]
  ; isFct :=
    {|fmap_proper X Y := arrow_context_proper A Z
    ; fmap_id := _
    ; fmap_comp := _
    |}
  |}.
Next Obligation.
  change (context[A; Z; id[A X]] ≈ id).
  rewrite <- (arrow_arr_id X), arrow_context_arr,
    tensor_map_id, fmap_id. reflexivity.
Qed.
Next Obligation.
  exact (arrow_context_comp A Z f g).
Qed.

End Derived.
