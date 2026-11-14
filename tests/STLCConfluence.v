From Cats.STLC Require Import BetaEtaLocal.

(** * Beta Confluence and Mixed-Peak Regressions

    Check the public results at separated and equal universes. Concrete
    critical peaks observe duplication, erasure and eta residual work by
    computing the common reduct and path lengths. These are interface
    regressions, not alternative proofs of the general theorems. *)

(** * β 合流与混合分叉回归

    在宇宙分离及相等时检查公开结果。具体临界分叉通过计算共同归约结果及
    路径长度，观察复制、丢弃和 η 剩余工作。这些是接口回归，不是一般定理的
    另一套证明。 *)

Local Open Scope relation_scope.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** Separate Computational Levels

    Fix [b < e < p < l]. No syntax/edge or edge/path identification is
    allowed, for either beta confluence or the mixed local diagram. *)

(** ** 分离的计算层级

    固定 [b < e < p < l]。β 合流及混合局部图式都不允许识别语法与边、边与
    路径的层级。 *)

Section SeparateLevels.
Universes b e p l.
Constraint b < e, e < p, p < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** The beta theorem returns joins at the requested path bound. *)

(** β 定理在要求的路径界返回汇合见证。 *)

Definition separated_beta_confluence
  : is_confluent@{b e p p} (@BetaStep@{b e l b} B Γ A)
  := beta_confluent Γ A.

(** Mixed peaks retain beta and eta edge tags in the residual paths. *)

(** 混合分叉在剩余路径中保留 β 与 η 的边标签。 *)

Definition separated_mixed_peak
  : is_locally_joinable@{b e e e p p}
      (@BetaStep@{b e l b} B Γ A) (@EtaContractStep@{b e l} B Γ A)
      (@BetaEtaContractStep@{b e l} B Γ A)
  := beta_eta_locally_joinable Γ A.

End SeparateLevels.

(** ** Paths above Classification

    Fix [b < e < l < p]. The edge-classification bound must not constrain
    the output paths. *)

(** ** 高于分类界的路径

    固定 [b < e < l < p]。边分类界不应限制输出路径。 *)

Section LargePaths.
Universes b e l p.
Constraint b < e, e < l, l < p.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** Beta confluence permits paths above the classification bound. *)

(** β 合流允许路径高于分类界。 *)

Definition large_beta_confluence
  : is_confluent@{b e p p} (@BetaStep@{b e l b} B Γ A)
  := beta_confluent Γ A.

(** The mixed theorem has the same independence. *)

(** 混合定理具有相同的独立性。 *)

Definition large_mixed_peak
  : is_locally_joinable@{b e e e p p}
      (@BetaStep@{b e l b} B Γ A) (@EtaContractStep@{b e l} B Γ A)
      (@BetaEtaContractStep@{b e l} B Γ A)
  := beta_eta_locally_joinable Γ A.

End LargePaths.

(** ** Equal Levels

    Syntax, steps and paths can share [b], with only [b < l]. *)

(** ** 相等层级

    语法、步骤与路径可以共用 [b]，只要求 [b < l]。 *)

Section EqualLevels.
Universes b l.
Constraint b < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** Equal computational bounds remain supported. *)

(** 继续支持相等的计算界。 *)

Definition equal_beta_confluence
  : is_confluent@{b b b b} (@BetaStep@{b b l b} B Γ A)
  := beta_confluent Γ A.

(** No strict separation is needed for mixed peaks either. *)

(** 混合分叉也不需要严格分离。 *)

Definition equal_mixed_peak
  : is_locally_joinable@{b b b b b b}
      (@BetaStep@{b b l b} B Γ A) (@EtaContractStep@{b b l} B Γ A)
      (@BetaEtaContractStep@{b b l} B Γ A)
  := beta_eta_locally_joinable Γ A.

End EqualLevels.

(** ** Explicit Residual Paths

    Use an empty base signature and closed unit terms. Count path edges
    without comparing their witnesses. All checks below compute by native
    reflexivity, including the duplicated eta argument. *)

(** ** 显式剩余路径

    使用空基签名及闭单位项。计算路径边数，不比较见证。以下检查都按原生
    自反性计算，包括被复制的 η 实参。 *)

Section ResidualPaths.

(** Count edges of any finite path. *)

(** 计算任意有限路径的边数。 *)

Fixpoint path_length {X : Type} {R : crelation X} {x y : X}
    (p : (R^*) x y)
  : nat
  := match p with rtc_refl _ => 0 | rtc_cons _ q => S (path_length q) end.

(** A closed beta redex of unit type. *)

(** 单位类型的闭 β 可归约式。 *)

Definition unit_redex
  : Tm (ctx_empty : Ctx Empty_set) ⊤
  := (ƛ (# var_zero)) · ⋆.

(** A root projection discards a beta step in its other component. *)

(** 根投影丢弃另一分量中的 β 步骤。 *)

Example discarded_beta_peak
  : let h := beta_root_join (root_beta_fst unit_redex unit_redex)
      (beta_step_lift op_fst (beta_step_lift (op_pair_r unit_redex)
        (context_step_root _ (root_beta_function (# var_zero) ⋆)))) in
    (projT1 h, path_length (fst (projT2 h)),
      path_length (snd (projT2 h))) = (unit_redex, 0, 1).
Proof. reflexivity. Defined.

(** A root projection retains a beta step in its selected component. *)

(** 根投影保留所选分量中的 β 步骤。 *)

Example retained_beta_peak
  : let h := beta_root_join (root_beta_fst unit_redex unit_redex)
      (beta_step_lift op_fst (beta_step_lift (op_pair_l unit_redex)
        (context_step_root _ (root_beta_function (# var_zero) ⋆)))) in
    (projT1 h, path_length (fst (projT2 h)),
      path_length (snd (projT2 h))) = (⋆, 1, 1).
Proof. reflexivity. Defined.

(** A product-valued redex duplicates its unit argument. *)

(** 返回积的可归约式复制单位实参。 *)

Definition pair_redex
  : Tm (ctx_empty : Ctx Empty_set) (⊤ × ⊤)
  := (ƛ (⟨# var_zero, # var_zero⟩)) · ⋆.

(** Eta at the root and beta in one projection leave a second beta
    copy, followed by eta. Both legs are computed explicitly. *)

(** 根 η 与一个投影内的 β 留下第二份 β，再后接 η；显式计算两腿。 *)

Example mixed_product_peak
  : let h := eta_root_beta_join (root_eta_contract_product pair_redex)
      (beta_step_lift (op_pair_l (π₂ pair_redex))
        (beta_step_lift op_fst (context_step_root _
          (root_beta_function (⟨# var_zero, # var_zero⟩) ⋆)))) in
    (projT1 h, path_length (fst (projT2 h)),
      path_length (snd (projT2 h))) = (⟨⋆, ⋆⟩, 1, 2).
Proof. reflexivity. Defined.

(** Beta duplicates an eta-redex argument. Two eta residuals remain on
    the beta side; the eta side takes the single root beta step. *)

(** β 复制带 η 可归约式的实参：β 一侧留下两份 η，η 一侧执行一次根 β。 *)

Example duplicated_eta_peak
  : let body := (⟨# var_zero, # var_zero⟩ :
      Tm ((ctx_empty : Ctx Empty_set) ▻ (⊤ × ⊤))
        ((⊤ × ⊤) × (⊤ × ⊤))) in
    let arg := (⟨π₁ pair_redex, π₂ pair_redex⟩) in
    let h := beta_root_eta_join (root_beta_function body arg)
      (eta_contract_lift (op_app_r (ƛ body))
        (eta_contract_root (root_eta_contract_product pair_redex))) in
    (projT1 h, path_length (fst (projT2 h)),
      path_length (snd (projT2 h))) = (⟨pair_redex, pair_redex⟩, 2, 1).
Proof. reflexivity. Defined.

End ResidualPaths.
