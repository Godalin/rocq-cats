From Cats.STLC Require Export
  ReductionRoot
  ReductionSubstitution.

(** * Head Beta Reduction

    Follow the principal child of a projection or application until its
    introduction is exposed. Contract there, without reducing arguments,
    pair components or lambda bodies. This is one deterministic strategy
    inside full contextual beta reduction, not a new equational theory.
    The computation inspects constructors and uses no label decision. *)

(** * 头部 β 归约

    沿投影或应用的主要子项寻找引入形式，并在那里收缩；不归约实参、配对
    分量或 λ 项体。这是完整上下文 β 归约中的一种确定策略，不是新的等式
    理论。计算只检查构造器，不判定标签相等。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_sub_scope.

(** ** A Selected Successor

    Fix arbitrary base labels. A successful observation selects exactly
    one beta step. Absence means head termination only; redexes can remain
    in arguments or under introductions. *)

(** ** 选定后继

    固定任意基标签。成功观测恰好选择一个 β 步骤。缺失仅表示头部终止；
    实参中或引入形式之下仍可能存在可归约式。 *)

Section HeadObservation.
Context {B : Type}.

(** Prefer a root contraction; otherwise search the principal child. *)

(** 优先收缩根；否则搜索主要子项。 *)

Fixpoint head_contractum {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : option (Tm Γ A)
  := match t in Tm Γ A return option (Tm Γ A) with
     | tm_fst p =>
         match pair_parts p with
         | Some z => Some (fst z)
         | None => option_map tm_fst (head_contractum p)
         end
     | tm_snd p =>
         match pair_parts p with
         | Some z => Some (snd z)
         | None => option_map tm_snd (head_contractum p)
         end
     | tm_app f a =>
         match lambda_body f with
         | Some q => Some q[a/]
         | None => option_map (λ g, g · a) (head_contractum f)
         end
     | _ => None
     end.

(** If the child is not a pair, the left projection follows its step. *)

(** 子项不是配对时，左投影沿其步骤前进。 *)

Definition head_contractum_fst {Γ : Ctx B} {A U : Ty B}
    (t : Tm Γ (A × U)) (parts : pair_parts t = None)
  : head_contractum (π₁ t) = option_map tm_fst (head_contractum t).
Proof. cbn [head_contractum]. rewrite parts. reflexivity. Defined.

(** The right projection follows the very same child computation. *)

(** 右投影沿完全相同的子项计算前进。 *)

Definition head_contractum_snd {Γ : Ctx B} {A U : Ty B}
    (t : Tm Γ (A × U)) (parts : pair_parts t = None)
  : head_contractum (π₂ t) = option_map tm_snd (head_contractum t).
Proof. cbn [head_contractum]. rewrite parts. reflexivity. Defined.

End HeadObservation.

(** A small Type-valued certificate of the selected edge. Its observation
    is retained, and can be converted to an ordinary beta derivation. *)

(** 选定边的小型 Type 值证书。它保留观测，可转换为普通 β 推导。 *)

Record HeadBetaStep@{b} {B : Type@{b}} {Γ : Ctx B} {A : Ty B}
    (t u : Tm Γ A)
  : Set
  := {
  head_beta_observation : head_contractum@{b b} t = Some u
}.

(** A successful head computation reconstructs a full contextual beta
    witness. Root observations align hidden types before reconstruction;
    recursive cases use the existing constructor compatibility. *)

(** 成功的头部计算重构完整上下文 β 见证。根观测先对齐隐藏类型再重构；
    递归情形复用既有构造器相容性。 *)

Definition head_contractum_beta@{b e l +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ u, head_contractum t = Some u → BetaStep@{b e l b} t u.
Proof.
  induction t; intros u h; cbn [head_contractum] in h;
    try discriminate h.
  - destruct (pair_parts t) as [[a v] |] eqn:parts.
    + apply (context_step_root _). apply root_contractum_beta.
      cbn [root_contractum]. rewrite parts. exact h.
    + destruct (head_contractum t) as [t' |] eqn:step;
        cbn in h; [| discriminate h].
      injection h as h. subst u.
      exact (beta_step_lift op_fst (IHt t' eq_refl)).
  - destruct (pair_parts t) as [[a v] |] eqn:parts.
    + apply (context_step_root _). apply root_contractum_beta.
      cbn [root_contractum]. rewrite parts. exact h.
    + destruct (head_contractum t) as [t' |] eqn:step;
        cbn in h; [| discriminate h].
      injection h as h. subst u.
      exact (beta_step_lift op_snd (IHt t' eq_refl)).
  - destruct (lambda_body t1) as [q |] eqn:body.
    + apply (context_step_root _). apply root_contractum_beta.
      cbn [root_contractum]. rewrite body. exact h.
    + destruct (head_contractum t1) as [t' |] eqn:step;
        cbn in h; [| discriminate h].
      injection h as h. subst u.
      exact (beta_step_lift (op_app_l t2) (IHt1 t' eq_refl)).
Defined.

(** Forget the strategy restriction, retaining a beta witness. *)

(** 忘却策略限制，保留 β 见证。 *)

Definition head_beta_step_beta@{b e l +} {B : Type@{b}}
    {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A} (h : HeadBetaStep t u)
  : BetaStep@{b e l b} t u
  := head_contractum_beta t u (head_beta_observation _ _ h).
