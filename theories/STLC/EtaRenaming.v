From Cats.STLC Require Export
  EtaRoot
  PartialReduction.

(** * Restricting Eta Steps and Reflecting Weakening

    Eta source shapes are stable under every defined partial renaming.
    The rule-independent contextual theorem extends root stability to
    full steps. Specializing to removal of the newest variable reflects
    eta contraction through weakening, with its target reconstructed by
    the section law. This does not assert reflection through arbitrary
    noninjective renamings, which can create eta redexes. *)

(** * 限制 η 步骤并反射弱化

    η 来源形状在每个有定义的部分重命名下稳定。独立于规则的上下文定理将根
    稳定性扩张至完整步骤。专化到移除最新变量后，可以经弱化反射 η 收缩，
    并由截面律重构目标。这不断言经任意非单射重命名反射，因为后者可产生
    η 可归约式。 *)

Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** ** Defined Partial Images

    Fix arbitrary base labels and independent syntax, evidence and
    classification bounds. All returned steps retain computational data. *)

(** ** 有定义的部分像

    固定任意基标签，以及独立的语法、证据和分类界。返回步骤均保留计算数据。 *)

Section EtaRestrictions.
Universes b e l.
Constraint b <= e, e < l.
Context {B : Type@{b}}.

(** Root stability in the form required by the general context theorem. *)

(** 以一般上下文定理所需的形式表达根稳定性。 *)

Definition root_eta_partial_step (Γ : Ctx B) (A : Ty B)
    (t u : Tm Γ A) (h : RootEtaContract@{b e} t u)
  : PartialStep (@RootEtaContract@{b e} B) t u.
Proof.
  intros Δ σ t' k. destruct (root_eta_partial h Δ σ t' k)
    as [u' [p q]].
  exists u'. split; [exact p | exact (context_step_root _ q)].
Defined.

(** A defined source restricts to a defined target and an eta step. *)

(** 有定义的来源限制为有定义的目标及一个 η 步骤。 *)

Definition eta_contract_partial {Γ : Ctx B} {A : Ty B} {t u : Tm Γ A}
    (h : EtaContractStep@{b e l} t u)
  : ∀ (Δ : Ctx B) (σ : PartialRen Δ Γ) (t' : Tm Δ A),
      partial_rename t Δ σ = Some t' →
      ∃ u', partial_rename u Δ σ = Some u' ∧ EtaContractStep@{b e l} t' u'.
Proof.
  intros Δ σ t' k.
  destruct (context_step_partial _ root_eta_partial_step
    (eta_contract_context h) Δ σ t' k) as [u' [p q]].
  exists u'. split; [exact p | exact (context_eta_contract q)].
Defined.

(** A step from a weakened term comes from a step before weakening, and
    its endpoint is exactly the weakening of the reconstructed endpoint. *)

(** 弱化项的步骤来自弱化前的步骤，且终点恰为所重构终点的弱化。 *)

Definition eta_contract_weaken_inv {Γ : Ctx B} {A U : Ty B}
    (t : Tm Γ U) (u : Tm (Γ ▻ A) U)
    (h : EtaContractStep@{b e l} t⟨wkRen⟩ u)
  : ∃ v, EtaContractStep@{b e l} t v ∧ u = v⟨wkRen⟩.
Proof.
  destruct (eta_contract_partial h Γ partial_drop t
    (partial_drop_weaken t)) as [v [p q]].
  exists v. split; [exact q | exact (partial_drop_section u v p)].
Defined.

End EtaRestrictions.
