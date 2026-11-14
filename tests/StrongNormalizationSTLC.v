From Cats.STLC Require Import StrongNormalization.

(** * STLC Strong-Normalization Regressions

    Check independent candidate membership, path, tree and law bounds;
    all-term normalization at separated and equal levels; and the binder
    premise of the substitution theorem. Examples include duplication,
    discarding, higher-order use and reductions under a lambda. *)

(** * STLC 强归一化回归

    检查候选成员性、路径、树和定律大小界独立，层级分离及相等时所有项的强
    归一化，以及替换定理的绑定前提。例子涵盖复制、丢弃、高阶使用和 λ 下
    归约。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** ** Paths below Normalization Trees

    Fix [p < a < r < w < s < k]. A path at [w] transports membership at
    the smaller [p], independently of the candidate's tree bound [s]. *)

(** ** 低于归一化树的路径

    固定 [p < a < r < w < s < k]。[w] 处的路径传递较小 [p] 处的成员性，
    独立于候选的树界 [s]。 *)

Section SmallerPaths.
Universes p a r w s k.
Constraint p < a, a < r, r < w, w < s, s < k.
Context {X : Type@{a}} (R : X → X → Type@{r}) (N : X → Set).
Context (P : X → Type@{p}).
Context (hP : IsReducibilityCandidate@{a r Set p s k} R N P).

(** Small paths need not share the normalization-tree size. *)

(** 小路径无须共用归一化树的大小。 *)

Definition smaller_path_membership {x y : X}
    (h : ReflTransClosure@{a r w} R x y)
  : P x → P y
  := candidate_rtc hP h.

End SmallerPaths.

(** ** Paths above Candidate Laws

    Fix [r < a < s < p < k < w]. Large path evidence may transport large
    membership while candidate trees and laws remain smaller than the path. *)

(** ** 高于候选定律的路径

    固定 [r < a < s < p < k < w]。大路径证据可以传递大成员性，同时候选树
    和候选定律仍小于路径。 *)

Section LargerPaths.
Universes r a s p k w.
Constraint r < a, a < s, s < p, p < k, k < w.
Context {X : Type@{a}} (R : X → X → Type@{r}) (N : X → Set).
Context (P : X → Type@{p}).
Context (hP : IsReducibilityCandidate@{a r Set p s k} R N P).

(** No path-to-tree or path-to-law resizing is assumed. *)

(** 不假设将路径缩小到树界或定律界。 *)

Definition larger_path_membership {x y : X}
    (h : ReflTransClosure@{a r w} R x y)
  : P x → P y
  := candidate_rtc hP h.

End LargerPaths.

(** ** Candidate Expansion with Small Membership

    Fix [p < b < e < s < k < l]. Candidate laws may lie below relation
    classification while expansion returns smaller membership data. *)

(** ** 小成员性的候选展开

    固定 [p < b < e < s < k < l]。候选定律可以低于关系分类界，展开返回更小
    的成员数据。 *)

Section SmallCandidate.
Universes p b e s k l.
Constraint p < b, b < e, e < s, s < k, k < l.
Context {B : Type@{b}} {Γ : Ctx B} {A U : Ty B}.
Context (P : Tm Γ U → Type@{p}).
Context (hP : IsReducibilityCandidate@{b e Set p s k}
  (@BetaStep@{b e l b} B Γ U) (@is_neutral_tm B Γ U) P).

(** Function beta expansion retains the independent candidate bounds. *)

(** 函数 β 展开保留独立候选大小界。 *)

Definition small_candidate_beta (t : Tm (Γ ▻ A) U) (u : Tm Γ A)
    (hu : SN@{b e s} (@BetaStep@{b e l b} B Γ A) u) (ht : P t[u/])
  : P ((ƛ t) · u)
  := candidate_beta_function P hP t u hu ht.

(** A projection may discard a component whose evidence is much larger
    than the selected component's membership. *)

(** 投影可丢弃一个分量，其证据远大于所选分量的成员性。 *)

Definition small_candidate_projection (t : Tm Γ U) (u : Tm Γ A)
    (ht : P t) (hu : SN@{b e s} (@BetaStep@{b e l b} B Γ A) u)
  : P (π₁ ⟨t, u⟩)
  := candidate_fst_pair P hP t u ht hu.

End SmallCandidate.

(** ** Candidate Expansion with Large Membership

    Fix [b < e < l < s < p < k]. Membership may exceed the tree universe
    and the relation-classification bound in the expansion theorem. *)

(** ** 大成员性的候选展开

    固定 [b < e < l < s < p < k]。展开定理的成员性可以高于树宇宙及关系分类界。 *)

Section LargeCandidate.
Universes b e l s p k.
Constraint b < e, e < l, l < s, s < p, p < k.
Context {B : Type@{b}} {Γ : Ctx B} {A U : Ty B}.
Context (P : Tm Γ U → Type@{p}).
Context (hP : IsReducibilityCandidate@{b e Set p s k}
  (@BetaStep@{b e l b} B Γ U) (@is_neutral_tm B Γ U) P).

(** The beta result is allowed to carry data larger than its SN trees. *)

(** β 结果允许携带大于其 SN 树的数据。 *)

Definition large_candidate_beta (t : Tm (Γ ▻ A) U) (u : Tm Γ A)
    (hu : SN@{b e s} (@BetaStep@{b e l b} B Γ A) u) (ht : P t[u/])
  : P ((ƛ t) · u)
  := candidate_beta_function P hP t u hu ht.

(** The other projection keeps the same independent bounds. *)

(** 另一投影保持相同的独立大小界。 *)

Definition large_candidate_projection (t : Tm Γ A) (u : Tm Γ U)
    (ht : SN@{b e s} (@BetaStep@{b e l b} B Γ A) t) (hu : P u)
  : P (π₂ ⟨t, u⟩)
  := candidate_snd_pair P hP t u ht hu.

End LargeCandidate.

(** ** All Terms at Separate Levels

    Fix [b < e < s < l] and arbitrary labels. The main theorem gives a
    normalization tree with the requested step/tree sizes. The fundamental
    theorem handles arbitrary reducible assignments and future binders. *)

(** ** 层级分离时的所有项

    固定 [b < e < s < l] 及任意标签。主定理按要求的步骤／树大小给出归一化树；
    基本定理处理任意可归约赋值与后续绑定。 *)

Section SeparatedLevels.
Universes b e s l.
Constraint b < e, e < s, s < l.
Context {B : Type@{b}} {Γ Δ : Ctx B} {A : Ty B}.

(** No hypothesis of reducibility remains in the final theorem. *)

(** 最终定理不再带有可归约性假设。 *)

Definition separated_beta_sn (t : Tm Γ A)
  : SN@{b e s} (@BetaStep@{b e l b} B Γ A) t
  := beta_strong_normalization t.

(** The substitution theorem retains the declared membership universe. *)

(** 替换定理保留所声明的成员性宇宙。 *)

Definition separated_substitution (t : Tm Γ A) (σ : Sub Δ Γ)
    (h : is_reducible_sub@{b e s l} σ)
  : Reducible@{b e s l} A Δ t[σ]
  := reducible_subst t Δ σ h.

(** The binder test assigns old variables after renaming and the newest
    one directly, using only the explicit reducibility hypotheses. *)

(** 绑定测试先对旧变量赋值重命名，再直接赋予最新变量，只用显式可归约性假设。 *)

Definition separated_binder {U : Ty B} (t : Tm (Γ ▻ A) U)
    (σ : Sub Δ Γ) (h : is_reducible_sub@{b e s l} σ)
  : Reducible@{b e s l} (A ⇒ U) Δ (ƛ t[σ^↑Sub])
  := reducible_subst (ƛ t) Δ σ h.

End SeparatedLevels.

(** ** Large Trees above Classification

    Fix [b < e < l < s]. Strong normalization does not force its tree
    universe below the relation-classification universe. *)

(** ** 高于分类界的大树

    固定 [b < e < l < s]。强归一化不要求树宇宙低于关系分类宇宙。 *)

Section LargeTrees.
Universes b e l s.
Constraint b < e, e < l, l < s.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** All terms normalize at a tree bound larger than classification. *)

(** 所有项在大于分类界的树界处强归一化。 *)

Definition large_tree_beta_sn (t : Tm Γ A)
  : SN@{b e s} (@BetaStep@{b e l b} B Γ A) t
  := beta_strong_normalization t.

End LargeTrees.

(** ** Equal Computational Levels

    Fix syntax, step and tree universes equal to [b], with only [b < l]
    for classification. No strict separation of actual witnesses is needed. *)

(** ** 相同的计算层级

    固定语法、步骤和树宇宙同为 [b]，只对分类要求 [b < l]；实际见证无须严格
    分离。 *)

Section EqualLevels.
Universes b l.
Constraint b < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** The theorem is also available at a common computational bound. *)

(** 定理也适用于共同计算界。 *)

Definition equal_level_beta_sn (t : Tm Γ A)
  : SN@{b b b} (@BetaStep@{b b l b} B Γ A) t
  := beta_strong_normalization t.

End EqualLevels.

(** ** Duplication, Discarding and Binders

    Use an empty base signature. The examples expose beta steps in
    arguments even when the root would discard them, duplication into
    products, higher-order application and full reduction under a lambda.
    All receive SN trees from the same unconditional theorem. *)

(** ** 复制、丢弃与绑定

    使用空基签名。例子暴露即使根收缩会丢弃实参时仍可进行的实参步骤、复制到
    积中、高阶应用及 λ 下的完整归约；都从同一个无条件定理取得 SN 树。 *)

Section Examples.

(** A closed unit redex used as an argument. *)

(** 用作实参的闭单位可归约式。 *)

Definition unit_redex
  : Tm (@ctx_empty Empty_set) ⊤
  := (ƛ (# var_zero)) · ⋆.

(** Duplication substitutes the argument into both pair components. *)

(** 复制将实参代入配对的两个分量。 *)

Definition duplicating_redex
  : Tm (@ctx_empty Empty_set) (⊤ × ⊤)
  := (ƛ (⟨# var_zero, # var_zero⟩)) · unit_redex.

(** The unused argument can still reduce before the root contraction. *)

(** 未使用的实参仍可在根收缩之前归约。 *)

Definition discarding_redex
  : Tm (@ctx_empty Empty_set) ⊤
  := (ƛ ⋆) · unit_redex.

(** A higher-order identity applied to an identity and then unit. *)

(** 将高阶恒等函数用于恒等函数，再用于单位。 *)

Definition higher_order_redex
  : Tm (@ctx_empty Empty_set) ⊤
  := ((ƛ (# var_zero)) · (ƛ (# var_zero))) · ⋆.

(** A beta step remains possible under an unapplied lambda. *)

(** 尚未应用的 λ 之下仍可进行 β 步骤。 *)

Definition binder_redex
  : Tm (@ctx_empty Empty_set) (⊤ ⇒ ⊤)
  := ƛ ((ƛ (# var_zero)) · (# var_zero)).

(** Duplication has a normalization tree, without selecting a strategy. *)

(** 复制具有归一化树，无须选择策略。 *)

Example duplication_sn
  : SN BetaStep duplicating_redex
  := beta_strong_normalization duplicating_redex.

(** Discarding also covers the argument-first reduction choice. *)

(** 丢弃也覆盖先归约实参的选择。 *)

Example discarding_argument_sn
  : SN BetaStep ((ƛ ⋆) · (⋆ : Tm (@ctx_empty Empty_set) ⊤))
  := sn_step (beta_strong_normalization discarding_redex)
      (beta_step_lift (op_app_r (ƛ ⋆))
        (context_step_root _ (root_beta_function (# var_zero) ⋆))).

(** Higher-order application is covered by the same all-terms theorem. *)

(** 同一个所有项定理也覆盖高阶应用。 *)

Example higher_order_sn
  : SN BetaStep higher_order_redex
  := beta_strong_normalization higher_order_redex.

(** Follow the body step under the lambda, preserving an SN subtree. *)

(** 沿 λ 下的项体步骤前进，保留 SN 子树。 *)

Example binder_reduct_sn
  : SN BetaStep (ƛ (# var_zero) : Tm (@ctx_empty Empty_set) (⊤ ⇒ ⊤))
  := sn_step (beta_strong_normalization binder_redex)
      (beta_step_lift op_lam
        (context_step_root _
          (root_beta_function (# var_zero) (# var_zero)))).

(** An infinite sequence would contradict the theorem's tree. *)

(** 无限序列会与主定理的树矛盾。 *)

Example no_closed_unit_infinite_sequence
    (f : nat → Tm (@ctx_empty Empty_set) ⊤)
  : (∀ n, BetaStep (f n) (f (S n))) → Empty_set
  := beta_no_infinite_sequence f.

End Examples.
