From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Adjunction
  Cat.Product.Core.

(** * Exponential Objects *)

(** * 指数对象 *)

(** Evaluation represents maps out of products with the fixed argument object. *)

(** 求值表示从与固定参数对象取积后出发的映射。 *)

Definition is_exponential {C : Cat} `{HP : !HasProduct C}
    (X Y E : Ob) (ev : Hom (E × X) Y)
  := ∀ Z (f : Hom (Z × X) Y),
    ∃ h : Hom Z E, is_unique (λ h, ev ∘ (h × id) ≈ f) h.

(** Selected exponential objects and evaluations relative to chosen products. *)

(** 相对于选定积的指数对象、求值及其泛性质。 *)

Class HasExponential {C : Cat} (HP : HasProduct C)
  :=
  { exp : Ob → Ob → Ob
  ; eval {X Y} : Hom (exp Y X × X) Y

  ; exponential_universal {X Y} : is_exponential X Y (exp Y X) eval
  }.

Arguments exponential_universal {_ _ _ _ _} _ _.

Notation "X '^' Y" := (exp X Y)
  (at level 30, right associativity): ob_scope.

(** Transpose a map out of a product into the chosen exponential. *)

(** 将从积出发的映射转置到选定指数中。 *)

Definition curry {C : Cat} `{HP : !HasProduct C} `{HE : !HasExponential HP}
    {X Y Z} (f : Hom (Z × X) Y)
  : Hom Z (Y ^ X)
  := (exponential_universal Z f).1.

Notation "'ƛ' f" := (curry f)
  (at level 35) : hom_scope.

(** Currying is the unique transpose with the prescribed evaluation. *)

(** 柯里化是具有给定求值行为的唯一转置。 *)

Theorem exponential_curry_unique {C : Cat}
    `{HP : !HasProduct C} `{HE : !HasExponential HP} {X Y Z}
    (f : Hom (Z × X) Y)
  : is_unique (λ h, eval ∘ (h × id) ≈ f) (ƛ f).
Proof. exact (exponential_universal Z f).2. Qed.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance exponential_curry_proper {C : Cat}
    `{HP : !HasProduct C} `{HE : !HasExponential HP} {X Y Z}
  : Proper (@HomEq[Z × X, Y] ==> @HomEq[Z, Y ^ X]) curry.
Proof.
  intros f g Hfg.
  destruct (exponential_curry_unique f) as [Hf _].
  apply (exponential_curry_unique g). transitivity f; assumption.
Qed.

Notation "'@eval' X Y" := (@eval _ _ _ _ X Y)
  (at level 35) : hom_scope.

(** ** Transposition and Substitution

    Only products and exponentials are needed. No terminal object, equality of
    functions, or equality of chosen universal-property witnesses is used. *)

(** ** 转置与替换

    仅需积和指数，不使用终对象、函数原生相等或选定泛性质见证的原生相等。 *)

Section Exponential.
Context {C : Cat} `{HP : !HasProduct C} `{HE : !HasExponential HP}.

(** Recover a map out of a product by evaluation. *)

(** 通过求值恢复从积出发的映射。 *)

Definition uncurry {X Y Z} (g : Hom Z (Y ^ X))
  : Hom (Z × X) Y
  := eval ∘ (g × id).

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance exponential_uncurry_proper {X Y Z}
  : Proper (@HomEq[Z, Y ^ X] ==> @HomEq[Z × X, Y]) uncurry.
Proof. intros f g Hfg. unfold uncurry. rewrite Hfg. reflexivity. Qed.

(** Uncurrying after currying recovers the original map. *)

(** 先柯里化再反柯里化恢复原映射。 *)

Theorem exponential_β {X Y Z} (f : Hom (Z × X) Y)
  : uncurry (ƛ f) ≈ f.
Proof. exact (@this _ _ _ _ _ (exponential_curry_unique f)). Qed.

(** Currying after uncurrying recovers the exponential-valued map. *)

(** 先反柯里化再柯里化恢复指数值映射。 *)

Theorem exponential_η {X Y Z} (g : Hom Z (Y ^ X))
  : ƛ (uncurry g) ≈ g.
Proof. symmetry. apply (exponential_curry_unique (uncurry g)). reflexivity. Qed.

(** The two respectful maps and the inverse laws give the hom-setoid
    correspondence. They retain their computational witness functions. *)

(** 两个保相等映射与互逆律给出 Hom 广集对应，并保留可计算的见证函数。 *)

Program Definition exponential_curry_resp {X Y Z}
  : HomSet (Z × X) Y →r HomSet Z (Y ^ X)
  :=
  {|func := curry
  |}.

(** Uncurrying as a respectful map between hom-setoids. *)

(** 反柯里化作为 Hom 广集间的保相等映射。 *)

Program Definition exponential_uncurry_resp {X Y Z}
  : HomSet Z (Y ^ X) →r HomSet (Z × X) Y
  :=
  {|func := uncurry
  |}.

(** Uncurrying commutes with precomposition in the context. *)

(** 反柯里化与上下文中的预合成交换。 *)

Lemma exponential_uncurry_comp_r {X Y Z W}
    (g : Hom Z (Y ^ X)) (σ : Hom W Z)
  : uncurry (g ∘ σ) ≈ uncurry g ∘ (σ × id).
Proof.
  unfold uncurry. rewrite comp_assoc, <- cross_comp, comp_id_l. reflexivity.
Qed.

(** Currying commutes with precomposition in the context. *)

(** 柯里化与上下文中的预合成交换。 *)

Lemma exponential_curry_comp_r {X Y Z W}
    (f : Hom (Z × X) Y) (σ : Hom W Z)
  : ƛ (f ∘ (σ × id)) ≈ (ƛ f) ∘ σ.
Proof.
  symmetry. apply exponential_curry_unique.
  change (uncurry ((ƛ f) ∘ σ) ≈ f ∘ (σ × id)).
  rewrite exponential_uncurry_comp_r, exponential_β. reflexivity.
Qed.

(** Covariant action on the result type, with the argument object fixed. *)

(** 固定参数对象后，指数在结果类型上的协变作用。 *)

Definition exponential_map {X Y Y'} (f : Hom Y Y')
  : Hom (Y ^ X) (Y' ^ X)
  := ƛ (f ∘ eval).

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance exponential_map_proper {X Y Y'}
  : Proper (@HomEq[Y, Y'] ==> @HomEq[Y ^ X, Y' ^ X]) exponential_map.
Proof. intros f g Hfg. unfold exponential_map. rewrite Hfg. reflexivity. Qed.

(** Uncurrying commutes with the induced map on result objects. *)

(** 反柯里化与结果对象上的诱导映射交换。 *)

Lemma exponential_uncurry_comp_l {X Y Y' Z}
    (f : Hom Y Y') (g : Hom Z (Y ^ X))
  : uncurry (exponential_map f ∘ g) ≈ f ∘ uncurry g.
Proof.
  rewrite exponential_uncurry_comp_r.
  unfold exponential_map. rewrite exponential_β. apply comp_assoc.
Qed.

(** Currying commutes with postcomposition in the result object. *)

(** 柯里化与结果对象上的后合成交换。 *)

Lemma exponential_curry_comp_l {X Y Y' Z}
    (f : Hom Y Y') (g : Hom (Z × X) Y)
  : ƛ (f ∘ g) ≈ exponential_map f ∘ (ƛ g).
Proof.
  symmetry. apply exponential_curry_unique.
  change (uncurry (exponential_map f ∘ (ƛ g)) ≈ f ∘ g).
  rewrite exponential_uncurry_comp_l, exponential_β. reflexivity.
Qed.

(** Compatibility with identities for [exponential_map]. *)

(** [exponential_map] 与恒等的相容性。 *)

Lemma exponential_map_id {X Y}
  : exponential_map (@id Y) ≈ @id (Y ^ X).
Proof.
  unfold exponential_map. rewrite comp_id_l.
  transitivity (ƛ (uncurry (@id (Y ^ X)))).
  - apply exponential_curry_proper. unfold uncurry.
    rewrite cross_id, comp_id_r. reflexivity.
  - apply exponential_η.
Qed.

(** Compatibility with composition for [exponential_map]. *)

(** [exponential_map] 与复合的相容性。 *)

Lemma exponential_map_comp {X Y Y' Y''} (g : Hom Y' Y'') (f : Hom Y Y')
  : exponential_map (X := X) (g ∘ f) ≈ exponential_map g ∘ exponential_map f.
Proof.
  unfold exponential_map at 1 3. rewrite comp_assoc.
  apply exponential_curry_comp_l.
Qed.

(** Application is evaluation in a shared context. These are the equations
    needed for function beta/eta and semantic simultaneous substitution. *)

(** 应用是在共同上下文中的求值；这些方程用于函数的 β、η 律和同时替换的语义。 *)

Definition app {X Y Z} (f : Hom Z (Y ^ X)) (a : Hom Z X)
  : Hom Z Y
  := eval ∘ ⟨f, a⟩.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance exponential_app_proper {X Y Z}
  : Proper (@HomEq[Z, Y ^ X] ==> @HomEq[Z, X] ==> @HomEq[Z, Y]) app.
Proof. intros f f' Hf a a' Ha. unfold app. rewrite Hf, Ha. reflexivity. Qed.

(** Application commutes with simultaneous substitution of function and
    argument. *)

(** 应用与函数及参数的同时替换交换。 *)

Lemma exponential_app_comp {X Y Z W}
    (f : Hom Z (Y ^ X)) (a : Hom Z X) (σ : Hom W Z)
  : app f a ∘ σ ≈ app (f ∘ σ) (a ∘ σ).
Proof. unfold app. rewrite comp_assoc, product_comp_r. reflexivity. Qed.

(** Application of a curried map computes by substitution. *)

(** 柯里化映射的应用按替换计算。 *)

Lemma exponential_app_β {X Y Z} (f : Hom (Z × X) Y) (a : Hom Z X)
  : app (ƛ f) a ≈ f ∘ ⟨id, a⟩.
Proof.
  rewrite <- (exponential_β f) at 2. unfold app, uncurry.
  rewrite comp_assoc, product_comp_l, comp_id_r, comp_id_l. reflexivity.
Qed.

(** A function is recovered by abstraction over its application. *)

(** 函数由其应用的抽象恢复。 *)

Lemma exponential_app_η {X Y Z} (f : Hom Z (Y ^ X))
  : ƛ (app (f ∘ π1) π2) ≈ f.
Proof.
  transitivity (ƛ (uncurry f)).
  - apply exponential_curry_proper. unfold app, uncurry.
    rewrite cross_η, comp_id_l. reflexivity.
  - apply exponential_η.
Qed.

End Exponential.

(** ** The Product–Exponential Adjunction *)

(** ** 积与指数的伴随 *)

(** Exponentiation as a functor in the result object. *)

(** 指数在结果对象上的函子。 *)

Program Definition ExponentialF {C : Cat}
    `{HP : !HasProduct C} `{HE : !HasExponential HP} (X : @Ob C)
  : Functor C C
  :=
  {|F0 Y := Y ^ X
  ; F1 Y Y' f := exponential_map f
  |}.
Next Obligation. apply exponential_map_id. Qed.
Next Obligation. apply exponential_map_comp. Qed.

Notation "'(-^' X ')'" := (ExponentialF X) : cat_scope.

(** The natural hom correspondence gives product left adjoint to
    exponentiation. *)

(** 自然 Hom 对应给出积函子左伴随于指数函子。 *)

Definition ProductExponentialAdjunction {C : Cat}
    `{HP : !HasProduct C} `{HE : !HasExponential HP} (X : @Ob C)
  : (-× X) ⊣ (-^ X).
Proof.
  refine (AdjunctionFromHom (-× X) (-^ X)
    (λ Z Y, exponential_curry_resp) (λ Z Y, exponential_uncurry_resp)
    _ _ _ _).
  - intros Z Y f. apply exponential_β.
  - intros Z Y g. apply exponential_η.
  - intros Z Z' Y f h. apply exponential_curry_comp_r.
  - intros Z Y Y' k f. apply exponential_curry_comp_l.
Defined.

(** The product-exponential adjunct is currying. *)

(** 积与指数伴随的正向转置就是柯里化。 *)

Theorem exponential_adjunct {C : Cat}
    `{HP : !HasProduct C} `{HE : !HasExponential HP} {X Y Z}
    (f : Hom (Z × X) Y)
  : f^♯[ProductExponentialAdjunction X] ≈ ƛ f.
Proof. apply adjunct_from_hom. Qed.

(** The inverse product-exponential adjunct is uncurrying. *)

(** 积与指数伴随的逆向转置就是反柯里化。 *)

Theorem exponential_unadjunct {C : Cat}
    `{HP : !HasProduct C} `{HE : !HasExponential HP} {X Y Z}
    (g : Hom Z (Y ^ X))
  : g^♭[ProductExponentialAdjunction X] ≈ uncurry g.
Proof. apply unadjunct_from_hom. Qed.

(** Transposing evaluation gives the identity on the exponential. *)

(** 求值的转置等于指数对象上的恒等。 *)

Lemma exponential_curry_eval {C : Cat} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} {X Y : @Ob C}
  : ƛ (@Cats.Cat.Exponential.Core.eval C HP HE X Y) ≈ id.
Proof.
  symmetry. apply exponential_curry_unique.
  rewrite cross_id, comp_id_r. reflexivity.
Qed.

(** Exponential-valued arrows are determined by their evaluations. *)

(** 指向指数的箭头由其求值确定。 *)

Lemma exponential_ext {C : Cat} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} {X Y Z : @Ob C}
    (f g : Hom Z (Y ^ X)) (H : uncurry f ≈ uncurry g)
  : f ≈ g.
Proof.
  rewrite <- (exponential_η f), <- (exponential_η g).
  apply exponential_curry_proper. exact H.
Qed.

(** Currying converts equations in either direction without new witnesses. *)

(** 柯里化无需新见证即可双向转换等式。 *)

Lemma exponential_curry_iff {C : Cat} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} {X Y Z : @Ob C}
    (f : Hom (Z × X) Y) (g : Hom Z (Y ^ X))
  : ƛ f ≈ g ↔ f ≈ uncurry g.
Proof.
  split; intros H.
  - rewrite <- H, exponential_β. reflexivity.
  - rewrite H, exponential_η. reflexivity.
Qed.

(** Equality of transposes is equivalent to equality of the original arrows. *)

(** 转置相等当且仅当原箭头相等。 *)

Lemma exponential_curry_eq_iff {C : Cat} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} {X Y Z : @Ob C}
    (f g : Hom (Z × X) Y)
  : ƛ f ≈ ƛ g ↔ f ≈ g.
Proof.
  split; intros H.
  - rewrite <- (exponential_β f), <- (exponential_β g), H. reflexivity.
  - rewrite H. reflexivity.
Qed.

(** Uncurrying is application to the two context projections. *)

(** 反柯里化是在两个上下文投影上的应用。 *)

Lemma exponential_uncurry_app {C : Cat} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} {X Y Z : @Ob C}
    (f : Hom Z (Y ^ X))
  : uncurry f ≈ app (f ∘ π1) π2.
Proof. unfold uncurry, app. rewrite cross_η, comp_id_l. reflexivity. Qed.

(** Uncurrying detects exactly the original hom equations. *)

(** 反柯里化恰好检测原有 Hom 等式。 *)

Lemma exponential_uncurry_eq_iff {C : Cat} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} {X Y Z : @Ob C}
    (f g : Hom Z (Y ^ X))
  : uncurry f ≈ uncurry g ↔ f ≈ g.
Proof.
  split; intros H; [apply exponential_ext; exact H | rewrite H; reflexivity].
Qed.
