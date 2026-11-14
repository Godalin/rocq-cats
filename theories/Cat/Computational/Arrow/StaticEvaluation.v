From Cats Require Export
  Cat.Computational.Arrow.GlobalContext
  Cat.Exponential.Context.

Import Cats.Cat.Exponential.Core.
Local Open Scope computation_scope.

(** * Interpreting Global Internal Functions

    Fix a cartesian Arrow whose value category has selected exponentials.
    Run a global internal-function computation alongside its ordinary
    argument, then evaluate purely. The generic context laws prove pure,
    sequential and context preservation with independent category sizes;
    no Applicative endofunctor representation is assumed here. *)

(** * 解释全局内部函数

    固定值范畴具有选定指数的笛卡尔 Arrow，将全局内部函数计算与其通常参数
    一起运行，再作纯求值。一般上下文定律在独立范畴大小下证明纯箭头、顺序及
    上下文保持性；此处不假设 Applicative 自函子表示。 *)

Section StaticEvaluation.
Context {C K : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    `{HE : !HasExponential HP}
    (A : Arrow C K (@CartesianMonoidal C HT HP)).

(** Interpret a global internal function by carrying its argument and
    applying ordinary evaluation. *)

(** 携带参数并作通常求值，从而解释全局内部函数。 *)

Definition arrow_static_eval {X Y : @Ob C}
    (f : Hom (A 1) (A (Y ^ X)%ob))
  : Hom (A X) (A Y)
  := arr[A; (app π2 π1 : Hom (X × (Y ^ X)) Y)] ∘
    arrow_global_context A X f.

(** Interpretation respects the specified computation equality. *)

(** 解释保持指定的计算相等。 *)

Global Instance arrow_static_eval_proper {X Y : @Ob C}
  : Proper (HomEq ==> HomEq) (@arrow_static_eval X Y).
Proof.
  intros f g H. unfold arrow_static_eval. rewrite H. reflexivity.
Qed.

(** Interpreting a pure named function recovers the original pure arrow. *)

(** 解释纯命名函数，恢复原来的纯箭头。 *)

Lemma arrow_static_eval_pure {X Y : @Ob C} (f : Hom X Y)
  : arrow_static_eval arr[A; exponential_name f] ≈ arr[A; f].
Proof.
  unfold arrow_static_eval. rewrite arrow_global_context_pure, <- functor_comp.
  apply functor_fmap_proper.
  rewrite exponential_app_comp, product_β1, product_β2.
  rewrite exponential_name_app, comp_id_r. reflexivity.
Qed.

(** A pure map selecting internal functions can be fused into ordinary
    evaluation. *)

(** 选取内部函数的纯映射可合并到通常求值中。 *)

Lemma arrow_static_eval_map {P X Y : @Ob C} (h : Hom P (Y ^ X))
    (f : Hom (A 1) (A P))
  : arrow_static_eval (arr[A; h] ∘ f) ≈
      arr[A; (app (h ∘ π2) π1 : Hom (X × P) Y)] ∘
        arrow_global_context A X f.
Proof.
  unfold arrow_static_eval. rewrite arrow_global_context_map, <- comp_assoc,
    <- functor_comp. apply comp_proper; [| reflexivity].
  apply functor_fmap_proper.
  rewrite exponential_app_comp.
  repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r]. reflexivity.
Qed.

(** Ordered global internal composition interprets as sequential computation
    composition. *)

(** 有序全局内部复合解释为顺序计算复合。 *)

Lemma arrow_static_eval_comp {X Y Z : @Ob C}
    (f : Hom (A 1) (A (Y ^ X)%ob))
    (g : Hom (A 1) (A (Z ^ Y)%ob))
  : arrow_static_eval (arr[A; internal_then X Y Z] ∘ (f &&&[A] g)) ≈
      arrow_static_eval g ∘ arrow_static_eval f.
Proof.
  rewrite arrow_static_eval_map, arrow_global_context_pair.
  unfold arrow_static_eval.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc (arrow_global_context A Y g)),
    arrow_global_context_pre.
  rewrite <- !comp_assoc.
  apply comp_proper; [| reflexivity]. apply comp_proper; [| reflexivity].
  rewrite <- !functor_comp. apply functor_fmap_proper.
  unfold product_assoc. cbn [projT1].
  repeat first [rewrite internal_then_app | rewrite exponential_app_comp |
    rewrite cross_η | rewrite product_comp_r | rewrite comp_assoc | rewrite product_β1 |
    rewrite product_β2 | rewrite comp_id_l | rewrite comp_id_r]. reflexivity.
Qed.

(** Interpreting internal context extension agrees with the original Arrow
    context action. *)

(** 解释内部上下文扩展，与原 Arrow 的上下文作用一致。 *)

Lemma arrow_static_eval_context {X Y : @Ob C} (W : @Ob C)
    (f : Hom (A 1) (A (Y ^ X)%ob))
  : arrow_static_eval (arr[A; internal_context W X Y] ∘ f) ≈
      context[A; W; arrow_static_eval f].
Proof.
  rewrite arrow_static_eval_map. unfold arrow_static_eval.
  change (arr[A; (app (internal_context W X Y ∘ π2) π1 :
    Hom ((W × X) × (Y ^ X)) (W × Y))] ∘
      arrow_global_context A (W × X)%ob f ≈
    second[A; arr[A; (app π2 π1 : Hom (X × (Y ^ X)) Y)] ∘
    arrow_global_context A X f; W]).
  rewrite arrow_second_comp, arrow_second_arr, arrow_global_context_nested,
    <- !comp_assoc.
  apply comp_proper; [| reflexivity].
  rewrite <- functor_comp. apply functor_fmap_proper.
  rewrite internal_context_app.
  unfold product_assoc. cbn [projT1].
  repeat first [rewrite internal_then_app | rewrite exponential_app_comp |
    rewrite cross_η | rewrite product_comp_r | rewrite comp_assoc | rewrite product_β1 |
    rewrite product_β2 | rewrite comp_id_l | rewrite comp_id_r]. reflexivity.
Qed.

End StaticEvaluation.
