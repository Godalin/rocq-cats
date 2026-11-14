From Cats.STLC Require Import BetaEtaConfluence.
From CatsTests Require Import STLCConfluence.

(** * Product Variable Views and Eta Roots

    Check that variable views remain small at a large signature, and that
    variable eta roots retain separated evidence bounds. The remaining
    elimination operation is kept abstract in the path and computation
    regressions: it must not be evaluated for a variable root. *)

(** * 积变量视图与 η 根

    检查变量视图在较大签名下仍然小，且变量 η 根保持独立的证据界。在路径和
    计算回归中，剩余的消去操作保持抽象：变量根不能对该操作求值。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** ** Small Views at a Large Signature

    Fix [Set < b]. The views, like the original variables, remain in
    [Set]; they do not store a newly sized copy of the context. *)

(** ** 较大签名下的小视图

    固定 [Set < b]。与原变量一样，视图仍位于 [Set]，不重新储存上下文的大副本。 *)

Section LargeSignature.
Universe b.
Constraint Set < b.
Context {B : Type@{b}}.

(** Both projections fit into a small pair. *)

(** 两个投影可放入一个小配对。 *)

Definition small_product_views {Γ : Ctx B} {A U : Ty B}
    (x : Var Γ (A × U))
  : (LeftProductVar Γ A * RightProductVar Γ U)%type
  := (product_var_left x, product_var_right x).

(** Their joint recovery does not identify the signature with [Set]. *)

(** 两者的联合恢复不会将签名界与 [Set] 识别。 *)

Definition large_signature_recovery {Γ : Ctx B} {A U : Ty B}
    (x y : Var Γ (A × U))
    (h : fst (small_product_views x) = fst (small_product_views y))
    (k : snd (small_product_views x) = snd (small_product_views y))
  : x = y
  := product_var_projections_injective x y h k.

End LargeSignature.

(** ** Paths below Classification

    Fix [b < e < p < l]. Variable recovery must not force the evidence
    bound to equal the syntax bound, or paths to contain classification. *)

(** ** 路径低于分类

    固定 [b < e < p < l]。变量恢复不能强制证据界等于语法界，也不能要求路径
    界容纳分类界。 *)

Section SmallPaths.
Universes b e p l.
Constraint b < e, e < p, p < l.
Context {B : Type@{b}}.

(** Root uniqueness has no remaining product-root premise. *)

(** 根唯一性没有剩余的积根前提。 *)

Definition separated_variable_root {Γ : Ctx B} {A U : Ty B}
    (x : Var Γ (A × U)) (v : Tm Γ (A × U))
    (h : RootEtaContract@{b e} (⟨π₁ (# x), π₂ (# x)⟩) v)
  : # x = v
  := root_eta_product_var_unique x v h.

(** Only targets with both observations absent need residual paths. *)

(** 只有两种观测均缺失的目标才需要剩余路径。 *)

Definition small_path_elimination_roots
    (remaining : ∀ (Γ : Ctx B) (A U : Ty B) (t v : Tm Γ (A × U)),
      RootEtaContract@{b e} (⟨π₁ t, π₂ t⟩) v →
      pair_parts t = None → variable_position t = None →
      Join@{b e p} BetaEtaContractStep@{b e l} t v)
  : @is_eta_product_root_joinable@{b e p l} B
  := eta_product_roots_of_eliminations remaining.

End SmallPaths.

(** ** Paths above Classification

    Fix [b < e < l < p]. The same residual interface supports the opposite
    ordering without changing the root-recovery construction. *)

(** ** 路径高于分类

    固定 [b < e < l < p]。同一个剩余接口支持相反次序，无须改变根恢复构造。 *)

Section LargePaths.
Universes b e l p.
Constraint b < e, e < l, l < p.
Context {B : Type@{b}}.

(** The larger path bound need not fit below classification. *)

(** 更大的路径界无须位于分类界之下。 *)

Definition large_path_elimination_roots
    (remaining : ∀ (Γ : Ctx B) (A U : Ty B) (t v : Tm Γ (A × U)),
      RootEtaContract@{b e} (⟨π₁ t, π₂ t⟩) v →
      pair_parts t = None → variable_position t = None →
      Join@{b e p} BetaEtaContractStep@{b e l} t v)
  : @is_eta_product_root_joinable@{b e p l} B
  := eta_product_roots_of_eliminations remaining.

End LargePaths.

(** ** Computing Newest and Older Variable Roots

    Fix equal syntax, evidence and path bounds, with only classification
    larger. The component types and context stay abstract. The remaining
    elimination operation must not be forced for either variable position. *)

(** ** 计算最新和旧变量根

    固定相等的语法、证据与路径界，只有分类界更大。分量类型和上下文保持
    抽象；两种变量位置均不能迫使剩余的消去操作求值。 *)

Section VariableComputations.
Universes b l.
Constraint b < l.
Context {B : Type@{b}}.
Context (remaining : ∀ (Γ : Ctx B) (A U : Ty B) (t v : Tm Γ (A × U)),
  RootEtaContract@{b b} (⟨π₁ t, π₂ t⟩) v →
  pair_parts t = None → variable_position t = None →
  Join@{b b b} BetaEtaContractStep@{b b l} t v).

(** The interface works at equal computational bounds. *)

(** 该接口可用于相等的计算界。 *)

Definition equal_bound_elimination_roots
  : @is_eta_product_root_joinable@{b b b l} B
  := eta_product_roots_of_eliminations remaining.

(** The newest variable is recovered with two empty residual paths. *)

(** 最新变量通过两条空剩余路径恢复。 *)

Example newest_variable_root_computes {Γ : Ctx B} {A U : Ty B}
  : let t := (# (var_zero : Var (Γ ▻ (A × U)) (A × U))) in
    let h := equal_bound_elimination_roots (Γ ▻ (A × U)) A U t t
      (root_eta_contract_product t) in
    (projT1 h, path_length (fst (projT2 h)),
      path_length (snd (projT2 h))) = (t, 0, 0).
Proof. reflexivity. Defined.

(** Adding an unrelated newest declaration keeps the old position. *)

(** 加入无关的最新声明仍保持旧位置。 *)

Example older_variable_root_computes {Γ : Ctx B} {A U V : Ty B}
  : let t := (# (var_succ var_zero :
      Var (Γ ▻ (A × U) ▻ V) (A × U))) in
    let h := equal_bound_elimination_roots (Γ ▻ (A × U) ▻ V) A U t t
      (root_eta_contract_product t) in
    (projT1 h, path_length (fst (projT2 h)),
      path_length (snd (projT2 h))) = (t, 0, 0).
Proof. reflexivity. Defined.

(** Equal declaration types do not identify different positions. *)

(** 相等的声明类型不会识别不同位置。 *)

Example product_views_distinguish_positions {Γ : Ctx B} {A U : Ty B}
  : product_var_left (var_succ var_zero :
      Var (Γ ▻ (A × U) ▻ (A × U)) (A × U)) <>
      product_var_left (var_zero :
        Var (Γ ▻ (A × U) ▻ (A × U)) (A × U)).
Proof. discriminate. Defined.

End VariableComputations.
