From Cats Require Import
  STLC.Normalization
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core.

(** * Executable NbE Interface Regressions *)

(** * 可执行 NbE 接口回归检查 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_tm_scope.

Section SeparatedBounds.
Universes b r s l.
Constraint b < r.
Constraint r < s.
Constraint s < l.
Context (B : Type@{b}) (Γ : Ctx B) (A : Ty B) (t : Tm Γ A).

(** Evaluation retains distinct syntax, world equality, semantic and
    world-law bounds through its public natural-transformation interface. *)

(** 求值的公开自然变换接口保留独立的语法、世界相等、语义与世界定律界限。 *)

Definition separated_evaluation
  : @Nat ((RenamingCat@{b r l _ _ _ _ _} B)^op)
      SetCat@{s s _ _ _ _ _}
      (EnvF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} Γ)
      (SemF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A)
  := EvalN t.

(** Initial environments use the same explicit semantic family. *)

(** 初始环境使用同一个显式语义族。 *)

Definition separated_initial_environment
  : EnvF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} Γ Γ
  := initial_env Γ.

(** The complete executable pipeline and its renaming law retain these
    distinct bounds, including those hidden by the normal-syntax result. *)

(** 完整可执行流水线及其重命名律保留这些独立界限，包括被正规语法结果隐藏的
    界限。 *)

Definition separated_normalization
  : Nf Γ A
  := nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t.

Definition separated_normalization_renaming (Δ : Ctx B) (ρ : Ren Δ Γ)
  : nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t⟨ρ⟩ =
      separated_normalization⟨ρ⟩nf.
Proof.
  exact (nf_rename@{b r s l
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t Δ ρ).
Defined.

(** Variable eta expansion also retains the chosen universe bounds. *)

(** 变量 η 展开也保留所选宇宙界限。 *)

Definition separated_variable_normalization (x : Var Γ A)
  : nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} (# x) =
      eta_expand_ne (ne_var x).
Proof.
  exact (nf_var@{b r s l
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} x).
Defined.

End SeparatedBounds.

Section SmallerWorldLawBound.
Universes b r l s.
Constraint b < r.
Constraint r < l.
Constraint l < s.
Context (B : Type@{b}) (Γ : Ctx B) (A : Ty B) (t : Tm Γ A).

(** Evaluation does not require semantic values to fit below world laws. *)

(** 求值不要求语义值界限低于世界定律界限。 *)

Definition smaller_world_law_evaluation
  : @Nat ((RenamingCat@{b r l _ _ _ _ _} B)^op)
      SetCat@{s s _ _ _ _ _}
      (EnvF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} Γ)
      (SemF@{b r s l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} A)
  := EvalN t.

(** The normalization function also accepts this ordering of bounds. *)

(** 正规化函数也接受此界限顺序。 *)

Definition smaller_world_law_normalization
  : Nf Γ A
  := nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t.

Definition smaller_world_law_normalization_renaming
    (Δ : Ctx B) (ρ : Ren Δ Γ)
  : nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t⟨ρ⟩ =
      smaller_world_law_normalization⟨ρ⟩nf.
Proof.
  exact (nf_rename@{b r s l
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} t Δ ρ).
Defined.

(** Variable eta expansion also retains the chosen universe bounds. *)

(** 变量 η 展开也保留所选宇宙界限。 *)

Definition smaller_world_law_variable_normalization (x : Var Γ A)
  : nf@{b r s l
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} (# x) =
      eta_expand_ne (ne_var x).
Proof.
  exact (nf_var@{b r s l
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} x).
Defined.

End SmallerWorldLawBound.

Section Computations.
Context {B : Type} (p q : B) (Γ : Ctx B).

(** A beta redex at a base type computes to its open argument. *)

(** 基类型处的 β 红式直接计算为其开放实参。 *)

Example beta_identity_computes
  : nf ((ƛ (# var_zero)) · (# var_zero) : Tm (Γ ▻ ty_base p) _) =
      nf_base (ne_var var_zero).
Proof. reflexivity. Qed.

(** Evaluation reduces redexes inside an abstraction, not just at the
    outermost term node. *)

(** 求值也消去抽象内部的红式，不仅处理项的最外层节点。 *)

Example beta_under_lambda_computes
  : nf (ƛ ((ƛ (# var_zero)) · (# var_zero)) :
      Tm Γ (ty_base p ⇒ ty_base p)) =
      nf_lam (nf_base (ne_var var_zero)).
Proof. reflexivity. Qed.

(** Passing a free variable beneath another binder preserves its position
    relative to the new variable; it is not captured by that binder. *)

(** 将自由变量传到另一绑定之下时，保留它相对于新变量的位置，不被该绑定捕获。 *)

Example beta_avoids_capture
  : nf ((ƛ (ƛ (# (var_succ var_zero)))) · (# var_zero) :
      Tm (Γ ▻ ty_base p) (ty_base q ⇒ ty_base p)) =
      nf_lam (nf_base (ne_var (var_succ var_zero))).
Proof. reflexivity. Qed.

(** Pair construction and projection execute before reification. *)

(** 配对构造与投影在实化前执行。 *)

Example product_beta_computes
  : nf (π₁ (⟨# var_zero, ⋆⟩) : Tm (Γ ▻ ty_base p) _) =
      nf_base (ne_var var_zero).
Proof. reflexivity. Qed.

(** Unit eta is enforced by the semantic singleton, including open inputs. *)

(** 语义单元素值落实单位 η，包括开放输入。 *)

Example unit_eta_computes
  : nf (# var_zero : Tm (Γ ▻ ⊤) ⊤) = nf_unit.
Proof. reflexivity. Qed.

(** A free function becomes an eta-long lambda after normalization. *)

(** 自由函数经正规化后成为 η 长 λ。 *)

Example function_eta_computes
  : nf (# var_zero : Tm (Γ ▻ (ty_base p ⇒ ty_base q)) _) =
      nf_lam (nf_base (ne_app (ne_var (var_succ var_zero))
        (nf_base (ne_var var_zero)))).
Proof. reflexivity. Qed.

(** A blocked higher-order application reifies its function argument to
    an eta-long lambda, with both old variables weakened under its binder. *)

(** 被阻塞的高阶应用将函数实参实化为 η 长 λ，并在其绑定下弱化两个旧变量。 *)

Example higher_order_open_application_computes
  : nf ((# var_zero) · (# (var_succ var_zero)) :
      Tm (Γ ▻ (ty_base p ⇒ ty_base q) ▻
        ((ty_base p ⇒ ty_base q) ⇒ ty_base q)) _) =
      nf_base (ne_app (ne_var var_zero)
        (nf_lam (nf_base
          (ne_app (ne_var (var_succ (var_succ var_zero)))
            (nf_base (ne_var var_zero)))))).
Proof. reflexivity. Qed.

(** A product variable expands by projections and type-directed eta. *)

(** 积变量通过投影与类型导向 η 展开。 *)

Example product_eta_computes
  : nf (# var_zero : Tm (Γ ▻ (ty_base p × ⊤)) _) =
      nf_pair (nf_base (ne_fst (ne_var var_zero))) nf_unit.
Proof. reflexivity. Qed.

End Computations.
