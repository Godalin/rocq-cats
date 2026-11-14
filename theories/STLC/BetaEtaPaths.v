From Cats.STLC Require Export
  EtaContraction
  ReductionPaths.
From Cats.Set.Relation Require Import Compatible.

(** * Finite Beta/Eta Contraction Paths

    Specialize the general compatible-relation path theory. Substitution
    may duplicate an argument's eta steps, so paths rather than single
    steps are needed when moving eta past root beta. *)

(** * 有限 βη 收缩路径

    专化一般相容关系路径理论。替换可能复制实参的 η 步骤，因此将 η 移过
    根 β 时需要路径，而非单独一步。 *)

Local Open Scope relation_scope.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** ** Paths and Assignments

    Fix independent syntax, edge, path and classification bounds. All
    maps retain the selected beta/eta branch of each edge. *)

(** ** 路径与赋值

    固定独立的语法、边、路径及分类界。所有映射都保留每条边所选的 βη 分支。 *)

Section BetaEtaPaths.
Universes b e p l.
Context {B : Type@{b}}.

(** The tagged sum is compatible because each alternative is compatible. *)

(** 带标签和相容，因为每个备选都相容。 *)

Definition beta_eta_contract_compatible
  : is_compatible (TmContexts B)
      (tm_relation_family (@BetaEtaContractStep@{b e l} B)).
Proof. intros [Γ A] [Δ U] c x y h. exact (beta_eta_contract_lift c h). Defined.

(** Apply an enclosing constructor throughout a finite mixed path. *)

(** 将外层构造器应用于整条有限混合路径。 *)

Definition beta_eta_rtc_lift {Γ Δ : Ctx B} {A U : Ty B}
    (c : TmOperation (Γ, A) (Δ, U)) {t u : Tm Γ A}
    (h : ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} t u)
  : ReflTransClosure@{b e p} BetaEtaContractStep@{b e l}
      (TmContexts B _ _ c t) (TmContexts B _ _ c u)
  := tm_rtc_lift _ beta_eta_contract_compatible c h.

(** Rename every edge without changing the path's direction. *)

(** 重命名每条边，不改变路径方向。 *)

Definition beta_eta_rtc_rename {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} t u)
    (Δ : Ctx B) (ρ : Ren Δ Γ)
  : ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} t⟨ρ⟩ u⟨ρ⟩
  := rtc_preserves (λ v, v⟨ρ⟩)
      (λ x y k, rtc_step (beta_eta_contract_rename k Δ ρ)) h.

(** Substitute throughout a mixed path, keeping every generating step. *)

(** 对混合路径作替换，保留每个生成步骤。 *)

Definition beta_eta_rtc_subst {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} t u)
    (Δ : Ctx B) (σ : Sub Δ Γ)
  : ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} t[σ] u[σ]
  := rtc_preserves (λ v, v[σ])
      (λ x y k, rtc_step (beta_eta_contract_subst k Δ σ)) h.

(** The generic assignment theorem handles repeated occurrences. *)

(** 一般赋值定理处理重复出现。 *)

Definition beta_eta_rtc_single {Γ : Ctx B} {A U : Ty B}
    (t : Tm (Γ ▻ A) U) {u u' : Tm Γ A}
    (h : ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} u u')
  : ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} t[u/] t[u'/]
  := tm_rtc_single _ beta_eta_contract_compatible
      (λ Γ A t u k Δ ρ, beta_eta_contract_rename k Δ ρ) t h.

End BetaEtaPaths.
