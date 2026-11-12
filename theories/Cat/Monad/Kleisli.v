From Cats Require Export
  Cat.Monad.Extension.

Local Open Scope monad_scope.

(** * The Kleisli Category of an Ordinary Monad

    Objects are those of the base category; an arrow to [Y] is an ordinary
    arrow to [M Y]. Equality is exactly the existing hom-set equality.
    Only the ordinary Monad laws are needed: no strength, products or
    closed structure enter this construction. *)

(** * 普通 Monad 的 Kleisli 范畴

    对象取自基底范畴；到 [Y] 的箭头是到 [M Y] 的通常箭头，相等恰为已有
    Hom 广集相等。构造只需普通 Monad 定律，不使用强度、积或闭结构。 *)

(** Run the second argument first, then extend the first to its result. *)

(** 先运行第二个参数，再将第一个参数扩张到所得结果。 *)

Definition kleisli_comp {C : Cat} (M : Monad C) {X Y Z : @Ob C}
    (g : Hom Y (M Z)) (f : Hom X (M Y))
  : Hom X (M Z)
  := kleisli_extend M g ∘ f.

Notation "g '∘K[' M ']' f" := (kleisli_comp M g f)
  (at level 40, left associativity) : monad_scope.

(** ** The Kleisli Category and Its Functors

    Fix an ordinary Monad on a category. Prove the sequential composition
    laws and construct the Kleisli category, pure inclusion and extension functor. *)

(** ** Kleisli 范畴及其函子

    固定范畴上的普通 Monad，证明顺序复合定律，构造 Kleisli 范畴、纯嵌入及扩张函子。 *)

Section Kleisli.
Context {C : Cat} (M : Monad C).

(** Kleisli composition respects both specified arrow equalities. *)

(** Kleisli 复合保持两个参数的指定箭头相等。 *)

Global Instance kleisli_comp_proper {X Y Z : @Ob C}
  : Proper (HomEq ==> HomEq ==> HomEq) (@kleisli_comp C M X Y Z).
Proof.
  intros g g' Hg f f' Hf. unfold kleisli_comp. rewrite Hg, Hf. reflexivity.
Qed.

(** The monad unit is a right identity for Kleisli composition. *)

(** Monad 单位是 Kleisli 复合的右恒等。 *)

Lemma kleisli_comp_id_r {X Y : @Ob C} (f : Hom X (M Y))
  : f ∘K[M] η[M] X ≈ f.
Proof. apply kleisli_extend_pure. Qed.

(** The monad unit is also a left identity. *)

(** Monad 单位也是左恒等。 *)

Lemma kleisli_comp_id_l {X Y : @Ob C} (f : Hom X (M Y))
  : η[M] Y ∘K[M] f ≈ f.
Proof.
  unfold kleisli_comp. rewrite kleisli_extend_unit, comp_id_l. reflexivity.
Qed.

(** Associativity reuses the extension law and preserves execution order. *)

(** 结合律复用扩张定律，并保持执行顺序。 *)

Lemma kleisli_comp_assoc {W X Y Z : @Ob C}
    (h : Hom Y (M Z)) (g : Hom X (M Y)) (f : Hom W (M X))
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
  {|Ob := @Ob C
  ; HomSet X Y := @HomSet C X (M Y)
  ; id X := η[M] X
  ; comp _ _ _ g f := g ∘K[M] f
  ; comp_proper X Y Z := @kleisli_comp_proper X Y Z
  |}.
Next Obligation. apply kleisli_comp_id_r. Defined.
Next Obligation. apply kleisli_comp_id_l. Defined.
Next Obligation. apply kleisli_comp_assoc. Defined.

(** A pure arrow before a computation is ordinary input substitution. *)

(** 在计算之前运行纯箭头，就是通常输入代入。 *)

Lemma kleisli_comp_pure_r {X Y Z : @Ob C}
    (g : Hom Y (M Z)) (f : Hom X Y)
  : g ∘K[M] return[M; f] ≈ g ∘ f.
Proof.
  unfold kleisli_comp, monad_return.
  rewrite <- comp_assoc, kleisli_extend_pure. reflexivity.
Qed.

(** A pure arrow after a computation is ordinary result mapping. *)

(** 在计算之后运行纯箭头，就是通常结果映射。 *)

Lemma kleisli_comp_pure_l {X Y Z : @Ob C}
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
  : Functor C KleisliCat
  :=
  {|F0 X := X
  ; F1 X Y f := return[M; f]
  ; functor_fmap_proper X Y := @monad_return_proper C M X Y
  |}.
Next Obligation. exact (monad_return_id M X). Defined.
Next Obligation.
  change (return[M; f ∘ g] ≈ return[M; f] ∘K[M] return[M; g]).
  rewrite kleisli_comp_pure_r, monad_return_comp. reflexivity.
Defined.

(** Extend computations back into the base category. On objects this is
    the original Monad functor; on arrows it is Kleisli extension. *)

(** 将计算扩张回基底范畴；对象上使用原 Monad 函子，箭头上使用 Kleisli 扩张。 *)

Program Definition KleisliExtendF
  : Functor KleisliCat C
  :=
  {|F0 X := M X
  ; F1 X Y f := kleisli_extend M f
  ; functor_fmap_proper X Y := @kleisli_extend_proper C M X Y
  |}.
Next Obligation. exact (kleisli_extend_unit M X). Defined.
Next Obligation. exact (kleisli_extend_assoc M g f). Defined.

(** The two functors recover the original endofunctor up to an identity-
    component natural isomorphism, without equating functor law records.
    This statement compares endofunctors, not entire Monad structures. *)

(** 两函子通过分量为恒等的自然同构恢复原自函子，不等同函子定律记录。
    此命题比较自函子，不比较完整 Monad 结构。 *)

Program Definition KleisliCompositeIso
  : KleisliExtendF ∘F KleisliPureF ≅N (M : Functor C C)
  := ({|nt X := id|}; _).
Next Obligation.
  change (id ∘ kleisli_extend M (return[M; f]) ≈ fmap M f ∘ id).
  unfold monad_return.
  rewrite kleisli_extend_pre, kleisli_extend_unit,
    !comp_id_l, comp_id_r. reflexivity.
Defined.
Next Obligation. intros X. exists id. split; apply comp_id_l. Defined.

End Kleisli.
