From Cats Require Export
  Cat.Monad.Extension
  Cat.Monad.Category
  Cat.Monad.Adjunction
  Cat.Adjunction.

Local Open Scope monad_scope.

(** * Kleisli Categories and Adjunctions

    Objects are those of the base category; an arrow to [Y] is an ordinary
    arrow to [M Y]. Equality is exactly the existing hom-set equality.
    Only the ordinary Monad laws are needed: no strength, products or
    closed structure enter this construction. *)

(** * Kleisli 范畴与伴随

    对象取自基底范畴；到 [Y] 的箭头是到 [M Y] 的通常箭头，相等恰为已有
    Hom 广集相等。构造只需普通 Monad 定律，不使用强度、积或闭结构。 *)

(** Run the second argument first, then extend the first to its result. *)

(** 先运行第二个参数，再将第一个参数扩张到所得结果。 *)

Definition kleisli_comp {C : Cat} (M : Monad C)
    {X Y Z : C} (g : Hom Y (M Z)) (f : Hom X (M Y))
  : Hom X (M Z)
  := kleisli_extend M g ∘ f.

Notation "g '∘K[' M ']' f"
  := (kleisli_comp M g f)
  (at level 40, left associativity,
    format "g  ∘K[ M ]  f")
  : monad_scope.

(** ** The Kleisli Category and Its Functors

    Fix an ordinary Monad on a category. Prove the sequential composition
    laws and construct the Kleisli category, pure inclusion and extension functor. *)

(** ** Kleisli 范畴及其函子

    固定范畴上的普通 Monad，证明顺序复合定律，构造 Kleisli 范畴、纯嵌入及扩张函子。 *)

Section KleisliConstruction.
Context {C : Cat} (M : Monad C).

(** Kleisli composition respects both specified arrow equalities. *)

(** Kleisli 复合保持两个参数的指定箭头相等。 *)

Global Instance kleisli_comp_proper {X Y Z : C}
  : Proper (HomEq ==> HomEq ==> HomEq)
      (@kleisli_comp C M X Y Z).
Proof.
  intros g g' Hg f f' Hf. unfold kleisli_comp.
  rewrite Hg, Hf. reflexivity.
Qed.

(** The monad unit is a right identity for Kleisli composition. *)

(** Monad 单位是 Kleisli 复合的右恒等。 *)

Lemma kleisli_comp_id_r {X Y : C}
    (f : Hom X (M Y))
  : f ∘K[M] η[M] X ≈ f.
Proof. apply kleisli_extend_pure. Qed.

(** The monad unit is also a left identity. *)

(** Monad 单位也是左恒等。 *)

Lemma kleisli_comp_id_l {X Y : C}
    (f : Hom X (M Y))
  : η[M] Y ∘K[M] f ≈ f.
Proof.
  unfold kleisli_comp.
  rewrite kleisli_extend_unit, comp_id_l.
  reflexivity.
Qed.

(** Associativity reuses the extension law and preserves execution order. *)

(** 结合律复用扩张定律，并保持执行顺序。 *)

Lemma kleisli_comp_assoc {W X Y Z : C}
    (h : Hom Y (M Z)) (g : Hom X (M Y))
    (f : Hom W (M X))
  : (h ∘K[M] g) ∘K[M] f ≈ h ∘K[M] (g ∘K[M] f).
Proof.
  unfold kleisli_comp. rewrite kleisli_extend_assoc. apply comp_assoc.
Qed.

(** Reuse the base hom-sets, including their Type-valued equality witnesses.
    Composition and identity retain their transparent computational data. *)

(** 直接复用基底 Hom 广集及其 Type 值相等见证；复合及恒等保留透明计算数据。 *)

Program Definition KleisliCat
  : Cat
  :=
  {|Ob := C
  ; HomSet X Y := HomSet X (M Y)
  ; id X := η[M] X
  ; comp _ _ _ g f := g ∘K[M] f
  ; comp_proper _ _ _ := kleisli_comp_proper
  |}.
Next Obligation. apply kleisli_comp_id_r. Defined.
Next Obligation. apply kleisli_comp_id_l. Defined.
Next Obligation. apply kleisli_comp_assoc. Defined.

(** A pure arrow before a computation is ordinary input substitution. *)

(** 在计算之前运行纯箭头，就是通常输入代入。 *)

Lemma kleisli_comp_pure_r {X Y Z : C}
    (g : Hom Y (M Z)) (f : Hom X Y)
  : g ∘K[M] return[M; f] ≈ g ∘ f.
Proof.
  unfold kleisli_comp, monad_return.
  rewrite <- comp_assoc, kleisli_extend_pure.
  reflexivity.
Qed.

(** A pure arrow after a computation is ordinary result mapping. *)

(** 在计算之后运行纯箭头，就是通常结果映射。 *)

Lemma kleisli_comp_pure_l {X Y Z : C}
    (g : Hom Y Z) (f : Hom X (M Y))
  : return[M; g] ∘K[M] f ≈ fmap M g ∘ f.
Proof.
  unfold kleisli_comp, monad_return.
  rewrite kleisli_extend_pre, kleisli_extend_unit, comp_id_l. reflexivity.
Qed.

(** Send ordinary arrows to pure computations, keeping objects unchanged.
    This functor need not be faithful for an arbitrary monad. *)

(** 将通常箭头送为纯计算，对象不变。对任意 Monad，此函子不一定忠实。 *)

Program Definition KleisliPureF
  : Fct C KleisliCat
  :=
  {|fobj X := X
  ; fmap X Y f := return[M; f]
  ; isFct :=
      {|fmap_proper _ _ := monad_return_proper M
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation. exact (monad_return_id M X). Qed.
Next Obligation.
  change (return[M; f ∘ g] ≈ return[M; f] ∘K[M] return[M; g]).
  rewrite kleisli_comp_pure_r, monad_return_comp. reflexivity.
Qed.

(** Extend computations back into the base category. On objects this is
    the original Monad functor; on arrows it is Kleisli extension. *)

(** 将计算扩张回基底范畴；对象上使用原 Monad 函子，箭头上使用 Kleisli 扩张。 *)

Program Definition KleisliExtendF
  : Fct KleisliCat C
  :=
  {|fobj X := M X
  ; fmap X Y f := kleisli_extend M f
  ; isFct :=
      {|fmap_proper _ _ := kleisli_extend_proper M
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation. exact (kleisli_extend_unit M X). Qed.
Next Obligation. exact (kleisli_extend_assoc M g f). Qed.

(** The two functors recover the original endofunctor up to an identity-
    component natural isomorphism, without equating functor law records.
    This statement compares endofunctors, not entire Monad structures. *)

(** 两函子通过分量为恒等的自然同构恢复原自函子，不等同函子定律记录。
    此命题比较自函子，不比较完整 Monad 结构。 *)

Program Definition KleisliCompositeIso
  : KleisliExtendF ∘F KleisliPureF
    ≅N (M : Fct C C)
  := ({|nt X := id|}; _).
Next Obligation.
  change (id ∘ kleisli_extend M (return[M; f])
    ≈ fmap M f ∘ id).
  unfold monad_return.
  rewrite kleisli_extend_pre, kleisli_extend_unit,
    !comp_id_l, comp_id_r. reflexivity.
Defined.
Next Obligation.
  intros X. exists id.
  split; apply comp_id_l.
Defined.

End KleisliConstruction.

(** ** The Kleisli Adjunction and Recovery of the Monad

    The two hom-sets in the adjunction are the same base hom-set. Its
    identity correspondence gives the adjunction, and the existing general
    construction recovers the original Monad up to a Monad isomorphism.
    No strength, products or closed structure are needed. *)

(** ** Kleisli 伴随及 Monad 的恢复

    伴随两侧的 Hom 广集就是同一个基底 Hom 广集，恒等对应给出伴随。
    已有一般构造恢复原 Monad，比较为 Monad 同构。不需要强度、积或闭结构。 *)

Section FreeForgetfulAdjunction.
Context {C : Cat} (M : Monad C).

(** Reuse the general construction from mutually inverse respectful hom
    maps. Naturality in the source is pure substitution; naturality in the
    target is the definition of Kleisli composition. *)

(** 复用互逆保相等 Hom 映射的一般伴随构造。来源自然性就是纯值代入，目标
    自然性就是 Kleisli 复合的定义。 *)

Program Definition KleisliAdj
  : KleisliPureF M ⊣ KleisliExtendF M
  := AdjOfHom (KleisliPureF M) (KleisliExtendF M)
      (λ X Y, id_resp) (λ X Y, id_resp) _ _ _ _.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation.
  exact (kleisli_comp_pure_r M f h).
Defined.
Next Obligation. reflexivity. Defined.

(** Transposition retains the underlying computation unchanged. *)

(** 转置保持底层计算不变。 *)

Lemma kleisli_adjunct {X Y : C}
    (f : Hom X (M Y))
  : f^♯[KleisliAdj] ≈ f.
Proof. reflexivity. Qed.

(** Inverse transposition also retains the computation. *)

(** 逆转置也保持计算不变。 *)

Lemma kleisli_unadjunct {X Y : C}
    (f : Hom X (M Y))
  : f^♭[KleisliAdj] ≈ f.
Proof. reflexivity. Qed.

(** The unit is the original Monad unit, by transposing a Kleisli identity. *)

(** 单位是原 Monad 单位，由转置 Kleisli 恒等得到。 *)

Lemma kleisli_adj_unit (X : C)
  : adj_unit KleisliAdj X ≈ η[M] X.
Proof. reflexivity. Qed.

(** The counit at [X] is the base identity on [M X], viewed as a Kleisli
    arrow from [M X] to [X]. *)

(** [X] 处的余单位是 [M X] 上的基底恒等，视为从 [M X] 到 [X] 的 Kleisli 箭头。 *)

Lemma kleisli_adj_counit (X : C)
  : adj_counit KleisliAdj X ≈ id.
Proof. reflexivity. Qed.

(** The left triangle uses Kleisli composition and its identity. The proof
    is inherited from the general hom-correspondence theory. *)

(** 左三角使用 Kleisli 复合及其恒等，证明继承自一般 Hom 对应理论。 *)

Lemma kleisli_adj_triangle_l (X : C)
  : adj_counit KleisliAdj X
      ∘K[M] return[M; adj_unit KleisliAdj X]
    ≈ η[M] X.
Proof. exact (adj_triangle_l KleisliAdj X). Qed.

(** The right triangle takes place in the base category. *)

(** 右三角在基底范畴中成立。 *)

Lemma kleisli_adj_triangle_r (X : C)
  : kleisli_extend M (adj_counit KleisliAdj X)
      ∘ adj_unit KleisliAdj (M X)
    ≈ id.
Proof. exact (adj_triangle_r KleisliAdj X). Qed.

(** Use the general adjunction-to-Monad construction without reproving its
    laws for this particular category. *)

(** 使用一般伴随到 Monad 构造，不为此具体范畴重新证明其定律。 *)

Definition KleisliMonad
  : Monad C
  := AdjMonad KleisliAdj.

(** The recovered unit is the original unit. *)

(** 恢复后的单位就是原单位。 *)

Lemma kleisli_monad_unit (X : C)
  : η[KleisliMonad] X ≈ η[M] X.
Proof. exact (kleisli_adj_unit X). Qed.

(** Extending the identity computation recovers the original multiplication. *)

(** 扩张恒等计算，恢复原乘法。 *)

Lemma kleisli_monad_mul (X : C)
  : μ[KleisliMonad] X ≈ μ[M] X.
Proof.
  change (kleisli_extend M (id[M X]) ≈ μ[M] X).
  unfold kleisli_extend.
  rewrite fmap_id, comp_id_r. reflexivity.
Qed.

(** The existing comparison of underlying functors preserves both Monad
    operations, so it is an actual fixed-base Monad morphism. *)

(** 已有底层函子比较保持两个 Monad 运算，因此是实际的固定基底 Monad 态射。 *)

Program Definition KleisliMonadTo
  : MonadHomS KleisliMonad M
  := ((KleisliCompositeIso M).1; _).
Next Obligation.
  split; intros X.
  - change (id ∘ η[KleisliMonad] X ≈ η[M] X).
    rewrite comp_id_l. apply kleisli_monad_unit.
  - change (id ∘ μ[KleisliMonad] X
      ≈ μ[M] X ∘ (id ∘ fmap KleisliMonad (id[M X]))).
    rewrite fmap_id, !comp_id_l, comp_id_r. apply kleisli_monad_mul.
Defined.

(** The inverse natural comparison also preserves unit and multiplication. *)

(** 逆向自然比较也保持单位及乘法。 *)

Program Definition KleisliMonadFrom
  : MonadHomS M KleisliMonad
  := (InvN (KleisliCompositeIso M).1
      (KleisliCompositeIso M).2; _).
Next Obligation.
  split; intros X.
  - change (id ∘ η[M] X ≈ η[KleisliMonad] X).
    rewrite comp_id_l. symmetry.
    apply kleisli_monad_unit.
  - change (id ∘ μ[M] X
      ≈ μ[KleisliMonad] X ∘ (id ∘ fmap M (id[M X]))).
    rewrite fmap_id, !comp_id_l, comp_id_r.
    symmetry. apply kleisli_monad_mul.
Defined.

(** Recovery is an isomorphism in the existing category of Monads, not
    native equality of structures or their law witnesses. *)

(** 恢复给出已有 Monad 范畴中的同构，不使用结构或其定律见证的原生相等。 *)

Program Definition KleisliMonadIso
  : KleisliMonad ≅[MonadCat C] M
  := (KleisliMonadTo; (KleisliMonadFrom; _)).
Next Obligation.
  split; intros X; change ((id[M X]) ∘ id ≈ id);
    apply comp_id_l.
Defined.

End FreeForgetfulAdjunction.

(** ** The Kleisli Comparison of an Adjunction

    Fix an ordinary adjunction with independently sized categories. Its
    induced Monad has a canonical Kleisli comparison into the adjunction's
    target: keep the left adjoint on objects and inverse-transpose arrows.
    The comparison is fully faithful with explicit transpose preimages.
    No strength, products or object representatives are needed. *)

(** ** 伴随的 Kleisli 比较

    固定两个大小独立的范畴之间的普通伴随。诱导 Monad 的 Kleisli 范畴具有到
    伴随目标范畴的规范比较：对象沿左伴随映射，箭头作逆转置。比较全忠实，
    原像显式取转置，不需要强度、积或对象代表。 *)

Section ComparisonFunctor.
Context {C D : Cat}
  {F : Fct C D} {U : Fct D C}
  (A : F ⊣ U).

(** Inverse transposition turns Kleisli composition into target composition.
    Multiplication is the image of the counit; reuse inverse naturality. *)

(** 逆转置将 Kleisli 复合变为目标复合。乘法为余单位的像，证明复用逆转置自然性。 *)

Lemma adj_kleisli_unadjunct_comp {X Y Z : C}
    (f : Hom Y (U (F Z))) (g : Hom X (U (F Y)))
  : (f ∘K[AdjMonad A] g)^♭[A] ≈ f^♭[A] ∘ g^♭[A].
Proof.
  change ((fmap U (adj_counit A (F Z))
    ∘ fmap U (fmap F f) ∘ g)^♭[A]
    ≈ f^♭[A] ∘ g^♭[A]).
  rewrite <- fmap_comp, <- (unadjunct_counit A f).
  apply unadjunct_comp_l.
Qed.

(** The comparison functor uses the left adjoint on objects and the supplied
    inverse Hom correspondence on arrows. *)

(** 比较函子在对象上使用左伴随，在箭头上使用所给 Hom 逆对应。 *)

Program Definition AdjKleisliF
  : Fct (KleisliCat (AdjMonad A)) D
  :=
  {|fobj := F
  ; fmap X Y f := f^♭[A]
  ; isFct :=
      {|fmap_proper X Y := unadjunct_proper A
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation. exact (adj_β A (id[F X])). Qed.
Next Obligation.
  exact (adj_kleisli_unadjunct_comp f g).
Qed.

(** Transposition supplies computational fullness witnesses and reflects
    equality through the two inverse laws. The target need not consist only
    of image objects, so essential surjectivity is not asserted. *)

(** 转置提供可计算满性见证，并由两条互逆律反映相等。目标不必只有像对象，
    因此这里不宣称本质满。 *)

Definition adj_kleisli_fully_faithful
  : is_fully_faithful AdjKleisliF.
Proof.
  split.
  - intros X Y f. exists (f^♯[A]).
    exact (adj_β A f).
  - intros X Y f g E.
    transitivity ((f^♭[A])^♯[A]);
      [symmetry; exact (adj_η A f)|].
    transitivity ((g^♭[A])^♯[A]).
    + exact (adjunct_proper A _ _ E).
    + exact (adj_η A g).
Defined.

End ComparisonFunctor.
