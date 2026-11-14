From Cats.STLC Require Import Reducibility.

(** * Reducibility Interface Regressions

    Check independent candidate universes, normalization trees on both
    sides of the step-classification bound, equal-level use, noninjective
    renaming and transparent root observations. These examples do not
    assert reducibility of all typed terms. *)

(** * 可归约性接口回归

    检查候选宇宙独立、归一化树位于步骤分类界两侧、同层使用、非单射重命名及
    透明根观测。这些例子不断言所有带类型项均可归约。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** ** Small Membership and Larger Edge Evidence

    Fix [p < a < r < s < k], with neutrality at an independent [n < k].
    Small membership can entail a larger normalization tree without
    shrinking the stored step witnesses. *)

(** ** 小成员性与大步骤证据

    固定 [p < a < r < s < k]，中性性位于独立的 [n < k]。小成员性可以蕴含
    较大的归一化树，而不缩小所存步骤见证。 *)

Section SmallMembership.
Universes p a r n s k.
Constraint p < a, a < r, r < s, s < k, n < k.
Context {X : Type@{a}} (R : X → X → Type@{r}).
Context (N : X → Type@{n}) (P Q : X → Type@{p}).
Context (h : IsReducibilityCandidate@{a r n p s k} R N P).

(** The general interface preserves a separate tree universe. *)

(** 一般接口保留独立的树宇宙。 *)

Definition small_membership_sn (x : X) (p : P x)
  : SN@{a r s} R x
  := @candidate_sn _ R N P h x p.

(** Pointwise equivalence transports all laws, retaining the same bounds. *)

(** 逐点等价传递全部定律，并保持相同大小界。 *)

Definition small_membership_equiv (e : ∀ x, P x ↔ Q x)
  : IsReducibilityCandidate@{a r n p s k} R N Q
  := fst (IsReducibilityCandidate_proper R N P Q e) h.

End SmallMembership.

(** ** Large Membership and Smaller Edge Evidence

    Fix [n < r < a < s < p < k]. A candidate may store large membership
    data while returning a smaller normalization tree. This does not
    resize its members: its normalization law is an explicit assumption. *)

(** ** 大成员性与小步骤证据

    固定 [n < r < a < s < p < k]。候选可以保存大的成员数据，同时返回较小
    归一化树。这不缩小成员本身：其归一化律是显式假设。 *)

Section LargeMembership.
Universes n r a s p k.
Constraint n < r, r < a, a < s, s < p, p < k.
Context {X : Type@{a}} (R : X → X → Type@{r}).
Context (N : X → Type@{n}) (P : X → Type@{p}).
Context (h : IsReducibilityCandidate@{a r n p s k} R N P).

(** Membership and normalization evidence need not share a universe. *)

(** 成员性与归一化证据无须共用宇宙。 *)

Definition large_membership_sn (x : X) (p : P x)
  : SN@{a r s} R x
  := @candidate_sn _ R N P h x p.

End LargeMembership.

(** ** Trees below the Classification Bound

    Fix [b < e < s < l] and arbitrary labels. Reducibility supports
    normalization, neutral expansion, step closure and reindexing without
    a label equality decision. *)

(** ** 低于分类界的树

    固定 [b < e < s < l] 及任意标签。可归约性支持强归一化、中性展开、步骤
    封闭和重索引，不需要标签相等判定。 *)

Section SmallerTrees.
Universes b e s l.
Constraint b < e, e < s, s < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** A reducible term returns the declared normalization tree. *)

(** 可归约项返回所声明大小的归一化树。 *)

Definition smaller_tree_sn (t : Tm Γ A) (p : Reducible@{b e s l} A Γ t)
  : SN@{b e s} (@BetaStep@{b e l b} B Γ A) t
  := reducible_sn A Γ t p.

(** All reducts suffice for a neutral source, at the same independent levels. *)

(** 在相同独立层级处，全部后继的可归约性足以推出中性源项的可归约性。 *)

Definition smaller_tree_expand (t : Tm Γ A) (n : is_neutral_tm t)
    (h : ∀ u, BetaStep@{b e l b} t u → Reducible@{b e s l} A Γ u)
  : Reducible@{b e s l} A Γ t
  := reducible_expand A Γ t n h.

(** Renaming changes the context, including variable-identifying maps. *)

(** 重命名更换上下文，包括合并变量的映射。 *)

Definition smaller_tree_rename (t : Tm Γ A)
    (p : Reducible@{b e s l} A Γ t) (Δ : Ctx B) (ρ : Ren Δ Γ)
  : Reducible@{b e s l} A Δ t⟨ρ⟩
  := reducible_rename A Γ t p Δ ρ.

(** A step preserves reducibility without changing its witness universe. *)

(** 步骤保持可归约性，不改变其见证宇宙。 *)

Definition smaller_tree_step (t u : Tm Γ A)
    (h : BetaStep@{b e l b} t u) (p : Reducible@{b e s l} A Γ t)
  : Reducible@{b e s l} A Γ u
  := reducible_step A Γ t u h p.

(** Reflection retains the larger step universe when rebuilding a target. *)

(** 重构目标时，反射保留较大的步骤宇宙。 *)

Definition smaller_tree_reflect (t : Tm Γ A) (Δ : Ctx B) (ρ : Ren Δ Γ)
    (u : Tm Δ A) (h : BetaStep@{b e l b} t⟨ρ⟩ u)
  : ∃ v, BetaStep@{b e l b} t v ∧ u = v⟨ρ⟩
  := beta_step_rename_inv t Δ ρ u h.

End SmallerTrees.

(** ** Trees above the Classification Bound

    Fix [b < e < l < s]. The relation-classification universe does not
    bound the stored reducibility or normalization witnesses. *)

(** ** 高于分类界的树

    固定 [b < e < l < s]。关系分类宇宙不约束所存可归约性或归一化见证的上界。 *)

Section LargerTrees.
Universes b e l s.
Constraint b < e, e < l, l < s.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** A variable is reducible at a bound above relation classification. *)

(** 变量在高于关系分类的界处仍可归约。 *)

Definition larger_tree_var (x : Var Γ A)
  : Reducible@{b e s l} A Γ (# x)
  := reducible_var A Γ x.

(** Function reducibility is tested in a genuinely extended context. *)

(** 函数可归约性可在实际扩张的上下文中测试。 *)

Definition larger_tree_function_test {U : Ty B} (f : Tm Γ (A ⇒ U))
    (p : Reducible@{b e s l} (A ⇒ U) Γ f)
  : Reducible@{b e s l} U (Γ ▻ A) (f⟨wkRen⟩ · (# var_zero))
  := p (Γ ▻ A) wkRen (# var_zero) (reducible_var A (Γ ▻ A) var_zero).

(** The candidate instance uses the same large tree universe. *)

(** 候选实例使用同一大树宇宙。 *)

Definition larger_tree_candidate (t : Tm Γ A)
    (p : Reducible@{b e s l} A Γ t)
  : SN@{b e s} (@BetaStep@{b e l b} B Γ A) t
  := @candidate_sn _ _ _ _ (Reducible_IsReducibilityCandidate A Γ) t p.

End LargerTrees.

(** ** Equal Syntax, Step and Tree Universes

    Fix one common [b] and a larger [l]. The theory does not require
    strict separation among the actual computational witnesses. *)

(** ** 相同的语法、步骤和树宇宙

    固定共同的 [b] 及较大的 [l]。理论不要求实际计算见证的层级严格分离。 *)

Section EqualLevels.
Universes b l.
Constraint b < l.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B}.

(** Every variable yields an equal-level normalization tree. *)

(** 每个变量给出同层归一化树。 *)

Definition equal_level_variable_sn (x : Var Γ A)
  : SN@{b b b} (@BetaStep@{b b l b} B Γ A) (# x)
  := reducible_sn A Γ (# x) (reducible_var A Γ x).

End EqualLevels.

(** ** Independent Root-Witness Sizes

    Fix [b < r < s]. Uniqueness compares targets of root derivations
    whose edge witnesses live at different levels, in either argument order. *)

(** ** 独立的根见证大小

    固定 [b < r < s]。唯一性比较不同层级的根推导的目标，支持两个参数顺序。 *)

Section RootSizes.
Universes b r s.
Constraint b < r, r < s.
Context {B : Type@{b}} {Γ : Ctx B} {A : Ty B} {t u v : Tm Γ A}.

(** Small then large root evidence. *)

(** 先小后大的根证据。 *)

Definition root_unique_small_large (h : RootBeta@{b r b} t u)
    (k : RootBeta@{b s b} t v)
  : u = v
  := root_beta_unique h k.

(** Large then small root evidence. *)

(** 先大后小的根证据。 *)

Definition root_unique_large_small (h : RootBeta@{b s b} t u)
    (k : RootBeta@{b r b} t v)
  : u = v
  := root_beta_unique h k.

End RootSizes.

(** ** Transparent Computations

    Use an empty base signature and two unit variables. A renaming
    identifies both variables; reflection must still recover the original
    beta target. Root observation must not search inside constructors. *)

(** ** 透明计算

    使用空基签名和两个单位变量。重命名合并两个变量，反射仍须恢复原来的 β
    目标；根观测不得搜索构造器内部。 *)

Section Computations.

(** A two-variable context and a one-variable destination. *)

(** 双变量上下文及单变量目标。 *)

Definition two_units
  : Ctx Empty_set
  := (∅ ▻ ⊤) ▻ ⊤.

(** Both old variables are assigned the same destination variable. *)

(** 两个原变量均赋为同一个目标变量。 *)

Definition identify_units
  : Ren (∅ ▻ ⊤) two_units.
Proof.
  intros A [x | x].
  - destruct x as [x | x]; [destruct x | destruct x; exact var_zero].
  - destruct x. exact var_zero.
Defined.

(** The argument deliberately selects the older source variable. *)

(** 实参有意选取源上下文中的旧变量。 *)

Definition identifying_redex
  : Tm two_units ⊤
  := (ƛ (# var_zero)) · (# (var_succ var_zero)).

(** Observation computes the single root beta contractum. *)

(** 观测计算唯一的根 β 收缩结果。 *)

Example root_function_computes
  : root_contractum identifying_redex = Some (# (var_succ var_zero)).
Proof. reflexivity. Defined.

(** Reflection recovers the older variable even though its image agrees
    with the newer variable's image. No injectivity assumption is hidden. *)

(** 即使旧变量的像与新变量的像相同，反射仍恢复旧变量；没有隐藏单射假设。 *)

Example identifying_reflection_computes
  : projT1 (beta_step_rename_inv identifying_redex (∅ ▻ ⊤)
      identify_units (# var_zero)
      (context_step_root _ (root_beta_function (# var_zero) (# var_zero))))
      = (# (var_succ var_zero)).
Proof. reflexivity. Defined.

(** Reflection also lifts under a binder, keeping its fresh variable
    separate from the identified older variables. *)

(** 反射也提升到绑定之下，将新鲜变量与被合并的旧变量保持分离。 *)

Example binder_reflection_computes
  : projT1 (beta_step_rename_inv
      (ƛ ((ƛ (# var_zero)) · (# (var_succ var_zero)))
        : Tm two_units (⊤ ⇒ ⊤))
      (∅ ▻ ⊤) identify_units (ƛ (# (var_succ var_zero)))
      (beta_step_lift op_lam
        (context_step_root _
          (root_beta_function (# var_zero) (# (var_succ var_zero))))))
      = (ƛ (# (var_succ var_zero))).
Proof. reflexivity. Defined.

(** Projection observes the first component directly. *)

(** 投影直接观测第一分量。 *)

Example root_projection_computes
  : root_contractum (π₁ ⟨identifying_redex, (⋆ : Tm two_units ⊤)⟩)
      = Some identifying_redex.
Proof. reflexivity. Defined.

(** A redex underneath a pair is not a root contraction of that pair. *)

(** 配对内部的可归约式不是该配对的根收缩。 *)

Example root_pair_does_not_search
  : root_contractum (⟨identifying_redex, (⋆ : Tm two_units ⊤)⟩) = None.
Proof. reflexivity. Defined.

End Computations.
