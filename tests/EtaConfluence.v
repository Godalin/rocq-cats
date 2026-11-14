From Cats.STLC Require Import BetaEtaConfluence.

(** * Eta Diagrams with Independent Path Bounds

    These regressions retain the remaining product-root premise explicitly.
    They check the assembled interface with paths both below and above
    classification, and the unconditional weakening-reflection interface. *)

(** * 路径界独立的 η 图式

    这些回归显式保留剩余的积根前提，检查路径分别低于及高于分类界的组装接口，
    以及无条件的弱化反射接口。 *)

Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** ** Paths below Classification

    Fix [b < e < p < l]. No diagram may force paths to contain [l]. *)

(** ** 路径低于分类

    固定 [b < e < p < l]。图式不能强制路径容纳 [l]。 *)

Section SmallPaths.
Universes b e p l.
Constraint b < e, e < p, p < l.
Context {B : Type@{b}}.
Context (roots : @is_eta_product_root_joinable@{b e p l} B).

(** The remaining premise suffices at the smaller path bound. *)

(** 剩余前提在较小路径界处已经足够。 *)

Definition small_path_conditional_confluence (Γ : Ctx B) (A : Ty B)
  : is_confluent@{b e p _} (@BetaEtaContractStep@{b e l} B Γ A)
  := beta_eta_confluent_of_product_roots roots Γ A.

(** Weakening reflection does not require the product-root premise. *)

(** 弱化反射不要求积根前提。 *)

Definition separated_eta_weakening {Γ : Ctx B} {A U : Ty B}
    (t : Tm Γ U) (u : Tm (Γ ▻ A) U)
    (h : EtaContractStep@{b e l} t⟨wkRen⟩ u)
  : ∃ v, EtaContractStep@{b e l} t v ∧ u = v⟨wkRen⟩
  := eta_contract_weaken_inv t u h.

End SmallPaths.

(** ** Paths above Classification

    Fix [b < e < l < p]. Classification must not contain the path bound. *)

(** ** 路径高于分类

    固定 [b < e < l < p]。分类不应容纳路径界。 *)

Section LargePaths.
Universes b e l p.
Constraint b < e, e < l, l < p.
Context {B : Type@{b}}.
Context (roots : @is_eta_product_root_joinable@{b e p l} B).

(** The opposite ordering supports the same explicit-premise theorem. *)

(** 相反次序支持同一个带显式前提的定理。 *)

Definition large_path_conditional_confluence (Γ : Ctx B) (A : Ty B)
  : is_confluent@{b e p _} (@BetaEtaContractStep@{b e l} B Γ A)
  := beta_eta_confluent_of_product_roots roots Γ A.

End LargePaths.
