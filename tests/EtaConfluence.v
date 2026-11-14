From Cats.STLC Require Import BetaEtaConfluence.
From CatsTests Require Import STLCConfluence.

(** * Eta Diagrams with Independent Path Bounds

    These regressions retain the remaining product-root premise explicitly.
    They check the assembled interface with paths both below and above
    classification, and the unconditional weakening-reflection interface.
    Pair-root recovery also checks equal bounds and transparent residuals
    without evaluating the remaining non-pair operation. *)

(** * 路径界独立的 η 图式

    这些回归显式保留剩余的积根前提，检查路径分别低于及高于分类界的组装接口，
    以及无条件的弱化反射接口。配对根恢复还检查相等界及透明剩余路径，且不对
    尚余的非配对操作求值。 *)

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

(** A displayed pair determines its root target even at separated
    syntax and evidence bounds. *)

(** 即使语法界与证据界分离，给定配对仍确定其根目标。 *)

Definition separated_product_pair_unique {Γ : Ctx B} {A U : Ty B}
    (a : Tm Γ A) (u : Tm Γ U) (v : Tm Γ (ty_prod A U))
    (h : RootEtaContract@{b e}
      (⟨π₁ (⟨a, u⟩), π₂ (⟨a, u⟩)⟩) v)
  : ⟨a, u⟩ = v
  := root_eta_product_pair_unique a u v h.

(** Only the non-pair input is needed to recover the original interface
    with paths below classification. It remains an explicit premise. *)

(** 路径低于分类时，只需非配对输入即可恢复原接口；该输入仍为显式前提。 *)

Definition small_path_nonpair_confluence
    (nonpairs : @is_eta_nonpair_product_root_joinable@{b e p l} B)
    (Γ : Ctx B) (A : Ty B)
  : is_confluent@{b e p _} (@BetaEtaContractStep@{b e l} B Γ A)
  := beta_eta_confluent_of_product_roots
      (eta_product_roots_of_nonpairs nonpairs) Γ A.

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

(** The restriction also suffices when paths exceed classification. *)

(** 路径高于分类时，受限输入也已足够。 *)

Definition large_path_nonpair_confluence
    (nonpairs : @is_eta_nonpair_product_root_joinable@{b e p l} B)
    (Γ : Ctx B) (A : Ty B)
  : is_confluent@{b e p _} (@BetaEtaContractStep@{b e l} B Γ A)
  := beta_eta_confluent_of_product_roots
      (eta_product_roots_of_nonpairs nonpairs) Γ A.

End LargePaths.

(** ** Equal Bounds and Transparent Pair Recovery

    Fix equal syntax, evidence and path bounds, with only classification
    larger. The non-pair operation stays abstract: resolving a pair root
    must not call it, and the resulting common reduct computes directly. *)

(** ** 相等界与透明的配对恢复

    固定相等的语法、证据与路径界，仅分类界更大。非配对操作保持抽象：解决
    配对根时不能调用它，所得共同归约结果应当直接计算出来。 *)

Section EqualBounds.
Universes b l.
Constraint b < l.
Context {B : Type@{b}}.
Context (nonpairs : @is_eta_nonpair_product_root_joinable@{b b b l} B).

(** Neither the restriction nor the assembly requires a strict increase
    from syntax to edges or paths. *)

(** 限制及组装均不要求语法到边或路径严格增大。 *)

Definition equal_bound_product_roots
  : @is_eta_product_root_joinable@{b b b l} B
  := eta_product_roots_of_nonpairs nonpairs.

(** The abstract remaining operation is not forced at a pair root.
    Both computed residual paths are reflexive. *)

(** 配对根不会求值尚余的抽象操作；计算得到的两条剩余路径均为自反路径。 *)

Example pair_root_recovery_computes {Γ : Ctx B} {A U : Ty B}
    (a : Tm Γ A) (u : Tm Γ U)
  : let pair := ⟨a, u⟩ in
    let h := equal_bound_product_roots Γ A U pair pair
      (root_eta_contract_product pair) in
    (projT1 h, path_length (fst (projT2 h)),
      path_length (snd (projT2 h))) = (pair, 0, 0).
Proof. reflexivity. Defined.

End EqualBounds.
