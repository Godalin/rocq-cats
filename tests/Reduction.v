From Cats.STLC Require Import Reduction.
From Cats.Set.Relation Require Import Closure.

(** * Contextual Reduction Interface Regressions *)

(** * 上下文归约接口回归检查 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

Section LargerEvidence.
Universes b e.
Constraint b < e.
Context (B : Type@{b}) (Γ : Ctx B) (A : Ty B) (t u : Tm Γ A).

(** Both conversions retain evidence strictly above the syntax universe. *)

(** 两个转换保留严格高于语法宇宙的见证。 *)

Definition separated_reduction_comparison
  : TmEq@{b e _} t u ↔ ZigStar@{b e _ _} t u
  := tm_eq_zig_star t u.

Definition separated_beta_embedding (h : RootBeta@{b e _} t u)
  : BetaStep@{b e _ _} t u
  := context_step_root _ h.

End LargerEvidence.

Section SameLevel.
Universe b.
Context (B : Type@{b}) (Γ : Ctx B) (A : Ty B) (t u : Tm Γ A).

(** The same interface also accepts equal syntax and evidence levels. *)

(** 同一接口也允许语法与见证层级相同。 *)

Definition same_level_reduction_comparison
  : TmEq@{b b _} t u ↔ ZigStar@{b b _ _} t u
  := tm_eq_zig_star t u.

End SameLevel.

(** A reusable redex for the concrete constructor-position checks below. *)

(** 下面构造器位置检查复用的可归约项。 *)

Definition IdentityRedex {B : Type} {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : Tm Γ A
  := (ƛ (# var_zero)) · t.

Definition identity_beta_step {B : Type} {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : BetaStep (IdentityRedex t) t
  := context_step_root _ (root_beta_function (# var_zero) t).

(** Abstraction changes the context index of the lifted step. *)

(** 抽象改变被提升步骤的上下文索引。 *)

Definition beta_inside_lambda {B : Type} {Γ : Ctx B} {A U : Ty B}
    (t : Tm (Γ ▻ A) U)
  : BetaStep (ƛ (IdentityRedex t)) (ƛ t)
  := context_step_lift _ op_lam (identity_beta_step t).

(** Each binary position changes independently; none is a weak strategy. *)

(** 每个二元位置独立改变；这里没有弱求值策略的限制。 *)

Definition beta_in_pair_left {B : Type} {Γ : Ctx B} {A U : Ty B}
    (t : Tm Γ A) (u : Tm Γ U)
  : BetaStep (⟨IdentityRedex t, u⟩) (⟨t, u⟩)
  := context_step_lift _ (op_pair_l u) (identity_beta_step t).

Definition beta_in_pair_right {B : Type} {Γ : Ctx B} {A U : Ty B}
    (t : Tm Γ A) (u : Tm Γ U)
  : BetaStep (⟨t, IdentityRedex u⟩) (⟨t, u⟩)
  := context_step_lift _ (op_pair_r t) (identity_beta_step u).

Definition beta_in_application_left {B : Type} {Γ : Ctx B} {A U : Ty B}
    (f : Tm Γ (A ⇒ U)) (u : Tm Γ A)
  : BetaStep ((IdentityRedex f) · u) (f · u)
  := context_step_lift _ (op_app_l u) (identity_beta_step f).

Definition beta_in_application_right {B : Type} {Γ : Ctx B} {A U : Ty B}
    (f : Tm Γ (A ⇒ U)) (u : Tm Γ A)
  : BetaStep (f · (IdentityRedex u)) (f · u)
  := context_step_lift _ (op_app_r f) (identity_beta_step u).

(** Eta expansion has the stated direction for functions and products. *)

(** 函数与积的 η 展开具有所声明的方向。 *)

Definition eta_function_step {B : Type} {Γ : Ctx B} {A U : Ty B}
    (f : Tm Γ (A ⇒ U))
  : EtaExpandStep f (ƛ ((f⟨wkRen⟩) · (# var_zero)))
  := context_step_root _ (root_eta_function f).

Definition eta_product_step {B : Type} {Γ : Ctx B} {A U : Ty B}
    (p : Tm Γ (A × U))
  : EtaExpandStep p (⟨π₁ p, π₂ p⟩)
  := context_step_root _ (root_eta_product p).

(** Unit eta remains a separate rule even when its source is the unit term. *)

(** 即使源为单位项，单位 η 仍保持为独立规则。 *)

Definition unit_eta_step {B : Type} {Γ : Ctx B} (t : Tm Γ ⊤)
  : UnitEtaStep t ⋆
  := context_step_root _ (root_unit_eta t).

(** Mix a forward beta step with a backward eta expansion. *)

(** 混合一个正向 β 步骤与一个反向 η 展开。 *)

Definition mixed_forward_backward {B : Type} {Γ : Ctx B} {A U : Ty B}
    (f : Tm Γ (A ⇒ U))
  : ZigStar (IdentityRedex (ƛ ((f⟨wkRen⟩) · (# var_zero)))) f
  := zig_star_trans
      (zig_star_step (inl
        (identity_beta_step (ƛ ((f⟨wkRen⟩) · (# var_zero))))))
      (zig_star_sym (zig_star_step (inr (inl (eta_function_step f))))).

(** Observe the generated witnesses through a transparent preorder fold.
    This detects opaque conversions and accidental simultaneous updates. *)

(** 通过透明预序折叠观察生成见证，以检测不透明转换及误将两次更新合为一次。 *)

Local Program Instance count_steps_PreOrder (X : Type)
  : PreOrder (λ _ _ : X, nat)
  :=
  {|PreOrder_Reflexive x := 0
  ; PreOrder_Transitive x y z h k := (h + k)%nat
  |}.

Definition zig_star_length {B : Type} {Γ : Ctx B} {A : Ty B}
    {t u : Tm Γ A} (p : ZigStar t u)
  : nat
  := rtc_preserves (S := λ _ _ : Tm Γ A, nat)
      (λ x, x) (λ x y p, 1) p.

(** A beta equation computes to one step, and a binary congruence with
    two changed arguments computes to two separate steps. *)

(** 一个 β 方程计算为一步，两个参数都改变的二元合同计算为两个独立步骤。 *)

Definition ClosedUnit
  : Tm (∅ : Ctx Empty_set) ⊤
  := ⋆.

Example beta_conversion_computes
  : zig_star_length
      (tm_eq_to_zig_star (tm_eq_function_β (# var_zero) ClosedUnit)) = 1.
Proof. reflexivity. Qed.

Example binary_congruence_uses_two_steps
  : zig_star_length
      (tm_eq_to_zig_star
        (tm_eq_pair (tm_eq_function_β (# var_zero) ClosedUnit)
          (tm_eq_function_β (# var_zero) ClosedUnit))) = 2.
Proof. reflexivity. Qed.

(** Equal endpoints need not erase a nontrivial derivation: the unit loop
    has one edge whereas the reflexive derivation has none. *)

(** 端点相同不消去非平凡推导：单位自环具有一条边，自反推导则没有边。 *)

Example unit_loop_witness_is_retained
  : zig_star_length (tm_eq_to_zig_star (tm_eq_unit_η ClosedUnit)) = 1.
Proof. reflexivity. Qed.

Example empty_path_has_no_edges
  : zig_star_length (tm_eq_to_zig_star (tm_eq_refl ClosedUnit)) = 0.
Proof. reflexivity. Qed.
