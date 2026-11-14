From Cats Require Export
  Cat.Computational.Arrow.StaticEvaluation
  Cat.Computational.Arrow.StaticValues
  Cat.Exponential.Laws
  Instance.Set.Isomorphism.
Import Cats.Cat.Exponential.Core.
Local Open Scope computation_scope.
Local Open Scope applicative_scope.
(** * Static Global-Function Representations

    Fix a cartesian Arrow with selected exponentials. Its specified global-
    function evaluation map is static when each Hom map has an explicit
    inverse. Keep the two category sizes independent; the following
    reification and unique-representation laws assume this property. *)

(** * 全局函数的静态表示

    固定具有选定指数的笛卡尔 Arrow。当其指定全局函数求值的每个 Hom 映射具有显式逆时，称该表示为静态。两个范畴大小保持独立；以下恢复与唯一表示定律使用此性质。 *)

Section General.
Context {C K : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    `{HE : !HasExponential HP}
    (A : Arrow C K (@CartesianMonoidal C HT HP)).

(** The actual evaluation operation is a map of the native computation Hom
    setoids. *)

(** 实际求值运算是原生计算 Hom 广集之间的映射。 *)

Program Definition arrow_static_eval_resp (X Y : @Ob C)
  : HomSet (A 1) (A (Y ^ X)%ob) →r HomSet (A X) (A Y)
  := {|func := arrow_static_eval A|}.

(** Staticness means invertibility of these specific evaluation maps,
    retaining inverse witnesses in Type. It is a property of the supplied
    Arrow and choices. *)

(** 静态性表示这些指定求值映射可逆，在 Type 中保留逆见证；它是所给 Arrow 及选择的性质。 *)

Definition is_static_arrow
  : Type
  := ∀ X Y : @Ob C, @is_iso SetCat _ _ (arrow_static_eval_resp X Y).
Context (H : is_static_arrow).

(** Recover the global internal-function computation with the specified
    inverse. *)

(** 用指定逆恢复全局内部函数计算。 *)

Definition arrow_reify {X Y : @Ob C} (f : Hom (A X) (A Y))
  : Hom (A 1) (A (Y ^ X)%ob)
  := (H X Y).1 f.

(** Recovery respects the original computation equality. *)

(** 恢复保持原计算相等。 *)

Global Instance arrow_reify_proper {X Y : @Ob C}
  : Proper (HomEq ==> HomEq) (@arrow_reify X Y).
Proof. apply func_proper. Qed.

(** Recovery after evaluation returns the global representation. *)

(** 求值后恢复返回原全局表示。 *)

Lemma arrow_reify_eval {X Y : @Ob C} (f : Hom (A 1) (A (Y ^ X)%ob))
  : arrow_reify (arrow_static_eval A f) ≈ f.
Proof. exact (fst (H X Y).2 f). Qed.

(** Evaluation after recovery returns the original computation. *)

(** 恢复后求值返回原计算。 *)

Lemma arrow_eval_reify {X Y : @Ob C} (f : Hom (A X) (A Y))
  : arrow_static_eval A (arrow_reify f) ≈ f.
Proof. exact (snd (H X Y).2 f). Qed.

(** The inverse has the complete unique-representation property in native
    Hom equality. *)

(** 逆映射在原生 Hom 相等下具有完整的唯一表示性质。 *)

Definition arrow_static_universal {X Y : @Ob C} (f : Hom (A X) (A Y))
  : is_unique (R := HomEq)
      (λ g, arrow_static_eval A g ≈ f) (arrow_reify f)
  := iso_fiber_universal (arrow_static_eval_resp X Y; H X Y) f.

End General.

(** * Unique Representations and Structural Recovery

    Fix the same finite-product and exponential data. Characterize
    staticness by Type-valued unique fibers, then prove that its inverse
    preserves pure names, execution-order composition and ordinary context. *)

(** * 唯一表示与结构恢复

    固定同样的有限积与指数数据，以 Type 值唯一纤维刻画静态性，再证明其逆保持纯命名、执行次序复合及通常上下文。 *)

Section UniversalCriterion.
Context {C K : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    `{HE : !HasExponential HP}
    (A : Arrow C K (@CartesianMonoidal C HT HP)).

(** Supplied Type-valued unique representations construct the actual
    inverse, without an additional choice axiom. *)

(** 给定 Type 值唯一表示即可构造实际逆，不附加选择公理。 *)

Definition static_arrow_of_universal
    (H : ∀ (X Y : @Ob C) (f : Hom (A X) (A Y)),
      ∃ g : Hom (A 1) (A (Y ^ X)%ob),
        is_unique (R := HomEq) (λ g, arrow_static_eval A g ≈ f) g)
  : is_static_arrow A.
Proof.
  intros X Y. apply is_iso_of_unique_fibers. exact (H X Y).
Defined.

(** Invertible evaluation and Type-valued unique representation are
    equivalent criteria. *)

(** 可逆求值与 Type 值唯一表示是等价条件。 *)

Definition static_arrow_universal_iff
  : is_static_arrow A ↔
      (∀ (X Y : @Ob C) (f : Hom (A X) (A Y)),
        ∃ g : Hom (A 1) (A (Y ^ X)%ob),
          is_unique (R := HomEq) (λ g, arrow_static_eval A g ≈ f) g).
Proof.
  split.
  - intros H X Y f. exists (arrow_reify A H f).
    exact (arrow_static_universal A H f).
  - exact static_arrow_of_universal.
Defined.
Context (H : is_static_arrow A).

(** Under the criterion, evaluation also reflects the specified equality. *)

(** 在该条件下，求值也反映指定相等。 *)

Lemma arrow_static_eval_reflects {X Y : @Ob C}
    (f g : Hom (A 1) (A (Y ^ X)%ob))
    (Hfg : arrow_static_eval A f ≈ arrow_static_eval A g)
  : f ≈ g.
Proof.
  transitivity (arrow_reify A H (arrow_static_eval A f));
    [symmetry; apply arrow_reify_eval |].
  transitivity (arrow_reify A H (arrow_static_eval A g));
    [apply arrow_reify_proper; exact Hfg | apply arrow_reify_eval].
Qed.

(** Recovery of a pure arrow is the pure name of that ordinary arrow. *)

(** 纯箭头的恢复是该通常箭头的纯命名。 *)

Lemma arrow_reify_arr {X Y : @Ob C} (f : Hom X Y)
  : arrow_reify A H arr[A; f] ≈ arr[A; exponential_name f].
Proof.
  apply arrow_static_eval_reflects.
  rewrite arrow_eval_reify, arrow_static_eval_pure. reflexivity.
Qed.

(** Recovery preserves sequential execution through ordered global pairing. *)

(** 恢复通过有序全局配对保持顺序执行。 *)

Lemma arrow_reify_comp {X Y Z : @Ob C}
    (f : Hom (A X) (A Y)) (g : Hom (A Y) (A Z))
  : arrow_reify A H (g ∘ f) ≈ arr[A; internal_then X Y Z] ∘
      (arrow_reify A H f &&&[A] arrow_reify A H g).
Proof.
  apply arrow_static_eval_reflects.
  rewrite arrow_eval_reify, arrow_static_eval_comp, !arrow_eval_reify.
  reflexivity.
Qed.

(** Recovery preserves the same original context action through the internal
    context map. *)

(** 恢复通过内部上下文映射保持同一原上下文作用。 *)

Lemma arrow_reify_context {X Y : @Ob C} (Z : @Ob C)
    (f : Hom (A X) (A Y))
  : arrow_reify A H (context[A; Z; f]) ≈
      arr[A; internal_context Z X Y] ∘ arrow_reify A H f.
Proof.
  apply arrow_static_eval_reflects.
  etransitivity; [apply arrow_eval_reify |]. symmetry.
  etransitivity.
  - exact (@arrow_static_eval_context C K HT HP HE A X Y Z
      (arrow_reify A H f)).
  - rewrite (arrow_eval_reify A H f). reflexivity.
Qed.

End UniversalCriterion.

(** * Applicative-Generated Static Arrows Satisfy the Criterion

    Fix any Applicative on selected finite products and exponentials.
    Compare actual global-function interpretation with the existing
    terminal-input value map, and reuse its transparent inverse. No setoid-
    base or well-pointedness assumption is needed here. *)

(** * 由 Applicative 生成的静态 Arrow 满足条件

    固定选定有限积与指数上的任意 Applicative，比较实际全局函数解释与已有终输入值映射，并复用其透明逆。此处不要求广集基底或良点性。 *)

Section StaticModel.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} (B : Applicative C HT HP).

(** For the actual static Arrow, interpretation is exactly the existing
    terminal-input value map. Only ordinary exponential diagrams are
    compared. *)

(** 对于实际静态 Arrow，解释恰为已有终输入值映射；只比较通常指数图。 *)

Lemma static_eval_value {X Y : @Ob C}
    (f : Hom 1 (B ((Y ^ X) ^ 1)%ob))
  : arrow_static_eval (StaticArrow B) f ≈ static_value B f.
Proof.
  unfold arrow_static_eval, arrow_global_context.
  change (static_arr B (app π2 π1 : Hom (X × (Y ^ X)) Y) ∘ˢ[B]
    (static_context B X f ∘ˢ[B] static_arr B ⟨id, !⟩) ≈ static_value B f).
  rewrite static_comp_pure_r, static_comp_pure_l.
  unfold static_context, static_value.
  rewrite <- !comp_assoc, <- !functor_comp.
  apply comp_proper; [| reflexivity]. apply functor_fmap_proper.
  rewrite <- exponential_dimap_id_r.
  apply exponential_ext. rewrite !exponential_uncurry_app.
  unfold exponential_unit_iso. cbn [projT1].
  unfold exponential_unit_eval.
  repeat first [rewrite exponential_app_dimap | rewrite internal_context_app |
    rewrite exponential_app_comp | rewrite cross_η |
    rewrite product_comp_r | rewrite comp_assoc | rewrite product_β1 |
    rewrite product_β2 | rewrite comp_id_l | rewrite comp_id_r |
    rewrite term_comp_l]. reflexivity.
Qed.

(** Every Applicative-generated static Arrow has the transparent inverse
    already supplied by [static_function]. *)

(** 每个由 Applicative 生成的静态 Arrow 都具有 [static_function] 已提供的透明逆。 *)

Definition static_arrow_is_static
  : is_static_arrow (StaticArrow B).
Proof.
  intros X Y.
  unshelve notypeclasses refine (({|func := static_function B|}); _).
  - exact (@static_function_proper C HT HP HE B 1 (Y ^ X)%ob).
  - split.
    + intros f. change (static_function B
        (arrow_static_eval (StaticArrow B) f) ≈ f).
      rewrite static_eval_value, static_function_value. reflexivity.
    + intros f. change (arrow_static_eval (StaticArrow B)
        (static_function B f) ≈ f).
      rewrite static_eval_value, static_value_function. reflexivity.
Defined.

End StaticModel.
