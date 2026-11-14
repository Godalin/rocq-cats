From Cats.STLC Require Export VariableSpine.

(** * Joint Recovery from Projected Elimination Spines

    The declared head type fixes every forward elimination and argument
    type. Two projection extensions therefore retain a common prefix;
    their final markers jointly recover the original product marker.
    Comparing both extensions also distinguishes an empty spine from a
    nonempty one, without comparing hidden type annotations. *)

(** * 从投影消去链联合恢复

    声明的头部类型确定每个前向消去及实参类型。因此两个投影延伸保持共同
    前缀，其终端标记联合恢复原积标记。同时比较两个延伸还可区分空链与非空
    链，无须比较隐藏的类型注解。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** Recovering a Spine at a Fixed Declaration

    Fix arbitrary labels, a raw argument context and a product result.
    Equality here compares canonical spine codes, including their retained
    raw arguments and markers; no equality of arbitrary law fields is used. *)

(** ** 在固定声明处恢复消去链

    固定任意标签、原始实参上下文及积结果。此处的相等比较规范消去链编码，
    包括所保留的原始实参与标记，不使用任意定律字段之间的相等。 *)

Section SpineRecovery.
Context {B : Type} (Γ : Ctx B) {A U : Ty B}.

(** Both projection extensions jointly determine the original spine.
    Their first tags separate a leaf from an existing continuation; equal
    continuations reduce the question to their common child. *)

(** 两个投影延伸联合确定原消去链。第一次消去的标签区分叶端与已有后续；
    相同后续将问题归结到共同子项。 *)

Definition spine_projections_injective (D : Ty B)
  : ∀ (p q : AlignedSpine Γ D (A × U)),
      spine_fst p = spine_fst q → spine_snd p = spine_snd q → p = q.
Proof.
  induction D as [b | | D ihD V ihV | D ihD V ihV];
    intros [x | p] [y | q] left right.
  all: try exact (match product_marker_left (new_var_inv x) with end).
  all: try exact (match product_marker_left (new_var_inv y) with end).
  all: try exact (match p with end).
  all: try exact (match q with end).
  - cbn in left, right.
    injection left as left. injection right as right.
    pose proof (f_equal new_var_inv left) as l.
    pose proof (f_equal new_var_inv right) as r.
    rewrite (new_var_inv_inv (product_marker_left (new_var_inv x))),
      (new_var_inv_inv (product_marker_left (new_var_inv y))) in l.
    rewrite (new_var_inv_inv (product_marker_right (new_var_inv x))),
      (new_var_inv_inv (product_marker_right (new_var_inv y))) in r.
    pose proof (product_marker_projections_injective
      (new_var_inv x) (new_var_inv y) l r) as same.
    pose proof (f_equal new_var_inv same) as back.
    rewrite !new_var_inv_inv in back. f_equal. exact back.
  - destruct q as [[y | q] | [y | q]];
      cbn in left, right; discriminate left || discriminate right.
  - destruct p as [[x | p] | [x | p]];
      cbn in left, right; discriminate left || discriminate right.
  - destruct p as [p | p], q as [q | q].
    + assert (same : p = q).
      { apply ihD.
        - destruct p, q; cbn in left |- *; congruence.
        - destruct p, q; cbn in right |- *; congruence. }
      subst q. reflexivity.
    + destruct p, q; cbn in left; discriminate left.
    + destruct p, q; cbn in left; discriminate left.
    + assert (same : p = q).
      { apply ihV.
        - destruct p, q; cbn in left |- *; congruence.
        - destruct p, q; cbn in right |- *; congruence. }
      subst q. reflexivity.
  - destruct p as [a p], q as [c q].
    assert (args : a = c).
    { destruct p, q; cbn in left; congruence. }
    subst c. assert (same : p = q).
    { apply ihV.
      - destruct p, q; cbn in left |- *; congruence.
      - destruct p, q; cbn in right |- *; congruence. }
    subst q. reflexivity.
Defined.

End SpineRecovery.

(** ** Retaining the Context Position

    Keep the raw argument context fixed while ranging over head
    declarations. The sum tags retain positions before the spine at the
    selected declaration is compared. *)

(** ** 保持上下文位置

    遍历头部声明时保持原始实参上下文固定。先由和类型标签保持位置，再比较
    选定声明处的消去链。 *)

Section VariableSpineRecovery.
Context {B : Type} (Γ : Ctx B) {A U : Ty B}.

(** Joint recovery also retains the original variable position. *)

(** 联合恢复同时保持原变量的位置。 *)

Definition variable_spine_projections_injective (Δ : Ctx B)
  : ∀ (p q : VariableSpine Γ Δ (A × U)),
      variable_spine_fst Γ Δ A U p = variable_spine_fst Γ Δ A U q →
      variable_spine_snd Γ Δ A U p = variable_spine_snd Γ Δ A U q →
      p = q.
Proof.
  induction Δ as [| Δ ih D]; intros p q left right;
    [exact (match p with end) |].
  destruct p as [p | p], q as [q | q]; cbn in left, right;
    try discriminate left.
  - injection left as left. injection right as right.
    f_equal. exact (ih p q left right).
  - injection left as left. injection right as right.
    f_equal. exact (spine_projections_injective Γ D p q left right).
Defined.

End VariableSpineRecovery.

(** ** Recovering Raw Variable-Headed Terms

    Fix arbitrary labels. One inferred spine view and the two native
    projection equations discover the other view and identify their codes.
    Reconstruction then identifies terms, retaining all raw arguments. *)

(** ** 恢复变量头原始项

    固定任意标签。一个推断消去链视图及两个原生投影等式发现另一视图，并
    识别两者的编码。随后由重构识别项，保持全部原始实参。 *)

Section TermRecovery.
Context {B : Type}.

(** Having a variable-headed view suffices for joint projection recovery;
    neither beta normalization nor a decision about labels is needed. *)

(** 具有变量头视图即足以进行联合投影恢复，无须 β 正规化或标签判定。 *)

Definition variable_headed_product_projections_injective
    {Γ : Ctx B} {A U : Ty B} (t v : Tm Γ (A × U))
    (p : VariableSpine Γ Γ (A × U))
    (view : variable_spine_view t = Some p)
    (left : π₁ t = π₁ v) (right : π₂ t = π₂ v)
  : t = v.
Proof.
  pose proof (f_equal (λ r : Tm Γ A, variable_spine_view r) left)
    as first.
  cbn [variable_spine_view] in first. rewrite view in first.
  destruct (variable_spine_view v) as [q |] eqn:other;
    cbn in first; [| discriminate first].
  injection first as first.
  pose proof (f_equal (λ r : Tm Γ U, variable_spine_view r) right)
    as second.
  cbn [variable_spine_view] in second.
  rewrite view, other in second. cbn in second.
  injection second as second.
  pose proof (variable_spine_projections_injective Γ Γ p q first second)
    as same.
  subst q.
  exact (eq_trans (eq_sym (variable_spine_view_reconstruct t p view))
    (variable_spine_view_reconstruct v p other)).
Defined.

(** At a head-terminal non-pair product term the required view is
    constructed by the integrated extraction theorem. No property of
    the other term or its arguments is assumed. *)

(** 对于头部终止的非配对积项，所需视图由已集成的提取定理构造。不假设另一
    项及其实参的任何性质。 *)

Definition head_terminal_product_projections_injective
    {Γ : Ctx B} {A U : Ty B} (t v : Tm Γ (A × U))
    (terminal : head_contractum t = None) (parts : pair_parts t = None)
    (left : π₁ t = π₁ v) (right : π₂ t = π₂ v)
  : t = v.
Proof.
  destruct (head_terminal_product_spine t terminal parts) as [p [view _]].
  exact (variable_headed_product_projections_injective t v p view
    left right).
Defined.

End TermRecovery.
