From Cats.STLC Require Export
  EtaRenaming
  ContextConfluence
  BetaEtaPaths.
From Cats.Set.Relation Require Export Confluence.

(** * Eta Roots against Internal Contraction

    An internal change of a function eta source descends from a change of
    the weakened function, so weakening reflection supplies its residual.
    An internal change of a product eta source changes one copy of its
    argument; reduce the other copy before contracting the outer eta.
    Product root/root overlaps are a separate obligation and are not
    claimed by the following diagrams. *)

(** * η 根与内部收缩

    函数 η 来源的内部改变来自弱化函数的改变，因此弱化反射提供其剩余步骤。
    积 η 来源的内部改变作用于实参的一个副本；先归约另一副本，再收缩外层 η。
    积的根／根重叠是独立的证明义务，下列图式不声称已经完成它。 *)

Local Open Scope relation_scope.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** ** Root Diagrams without Label Decisions

    Fix arbitrary base labels and independent evidence, path and auxiliary
    classification bounds. The resulting joins use eta steps alone. *)

(** ** 不需要标签判定的根图式

    固定任意基标签，以及独立的证据、路径和辅助分类界。所得汇合仅使用 η 步骤。 *)

Section EtaRootDiagrams.
Universes b e p l.
Constraint b <= e, e < l.
Context {B : Type@{b}}.

(** A function eta root joins every eta step from the same source. *)

(** 函数 η 根可与同源的每个 η 步骤汇合。 *)

Definition eta_function_root_join {Γ : Ctx B} {A U : Ty B}
    (f : Tm Γ (A ⇒ U)) (v : Tm Γ (A ⇒ U))
    (k : EtaContractStep@{b e l} (ƛ (f⟨wkRen⟩ · (# var_zero))) v)
  : Join@{b e p} EtaContractStep@{b e l} f v.
Proof.
  destruct (eta_contract_source k) as [r | [body' [s z]]].
  - pose proof (root_eta_function_unique f v r) as q.
    subst v. exact (join_refl _).
  - destruct (context_step_source _ s) as [r | child].
    { exact (match root_eta_neutral_absurd r tt with end). }
    destruct child as [[g [s' q]] | [a [s' q]]].
    + destruct (eta_contract_weaken_inv f g (context_eta_contract s'))
        as [g' [r q']].
      subst g body' v. exists g'. split.
      * exact (rtc_step r).
      * exact (rtc_step (eta_contract_root (root_eta_contract_function g'))).
    + exact (match eta_contract_var_absurd var_zero
        (context_eta_contract s') with end).
Defined.

(** If the left projection changes internally, the unchanged right
    projection has the same residual step. The final root removes the
    duplicated projections. *)

(** 若左投影内部改变，未变的右投影具有同一剩余步骤；最后的根步骤去掉重复
    投影。 *)

Definition eta_product_left_join {Γ : Ctx B} {A U : Ty B}
    (t : Tm Γ (A × U)) (v : Tm Γ A)
    (h : ContextStep (@RootEtaContract@{b e} B) (π₁ t) v)
  : Join@{b e p} EtaContractStep@{b e l} t (⟨v, π₂ t⟩).
Proof.
  destruct (context_step_source _ h) as [r | [t' [s z]]].
  { exact (match root_eta_neutral_absurd r tt with end). }
  subst v. exists t'. split.
  - exact (rtc_step (context_eta_contract s)).
  - refine (rtc_cons
      (eta_contract_lift (op_pair_r (π₁ t'))
        (eta_contract_lift op_snd (context_eta_contract s))) _).
    exact (rtc_step (eta_contract_root (root_eta_contract_product t'))).
Defined.

(** The right-projection diagram follows the same residual construction
    in the other component; no witness equality is imposed. *)

(** 右投影图式在另一分量中使用同一剩余构造，不要求见证相等。 *)

Definition eta_product_right_join {Γ : Ctx B} {A U : Ty B}
    (t : Tm Γ (A × U)) (v : Tm Γ U)
    (h : ContextStep (@RootEtaContract@{b e} B) (π₂ t) v)
  : Join@{b e p} EtaContractStep@{b e l} t (⟨π₁ t, v⟩).
Proof.
  destruct (context_step_source _ h) as [r | [t' [s z]]].
  { exact (match root_eta_neutral_absurd r tt with end). }
  subst v. exists t'. split.
  - exact (rtc_step (context_eta_contract s)).
  - refine (rtc_cons
      (eta_contract_lift (op_pair_l (π₂ t'))
        (eta_contract_lift op_fst (context_eta_contract s))) _).
    exact (rtc_step (eta_contract_root (root_eta_contract_product t'))).
Defined.

End EtaRootDiagrams.

(** ** The Remaining Product Root Interface

    Keep the same arbitrary signature. Isolate the product root/root
    diagram as an explicit input, allowing beta residuals as well as eta.
    The assembly below discharges every other eta/eta peak. It does not
    construct this input or claim unconditional local confluence. *)

(** ** 剩余的积根接口

    保持任意签名。将积的根／根图式隔离为显式输入，允许 β 和 η 剩余步骤。
    下列组装处理其他全部 η／η 分叉，但不构造此输入，也不断言无条件局部合流。 *)

Section EtaProductInterface.
Universes b e p l.
Constraint b <= e, e < l.
Context {B : Type@{b}}.

(** A candidate diagram for the only unresolved root shape. *)

(** 唯一尚未解决的根形状所需的候选图式。 *)

Definition is_eta_product_root_joinable
  : Type@{p}
  := ∀ (Γ : Ctx B) (A U : Ty B) (t v : Tm Γ (A × U)),
      RootEtaContract@{b e} (⟨π₁ t, π₂ t⟩) v →
      Join@{b e p} BetaEtaContractStep@{b e l} t v.

(** Restrict the missing diagram to targets with no pair observation.
    The competing target also has no pair observation by
    [root_eta_product_parts]. This remains an explicit, unconstructed
    obligation for arbitrary base labels. *)

(** 将缺失图式限制到没有配对观测的目标。由 [root_eta_product_parts]，竞争
    目标也没有配对观测。这仍是任意基标签下显式、尚未构造的证明义务。 *)

Definition is_eta_nonpair_product_root_joinable
  : Type@{p}
  := ∀ (Γ : Ctx B) (A U : Ty B) (t v : Tm Γ (A × U)),
      RootEtaContract@{b e} (⟨π₁ t, π₂ t⟩) v →
      pair_parts t = None →
      Join@{b e p} BetaEtaContractStep@{b e l} t v.

(** The pair branch needs no residual steps: its targets already agree.
    Thus only the non-pair branch needs the supplied joining operation.
    The conclusion is the original interface, with no new global instance. *)

(** 配对分支无须剩余步骤，因为其目标已经相等。因此只有非配对分支需要给定
    的汇合操作。结论是原有接口，不引入新的全局实例。 *)

Definition eta_product_roots_of_nonpairs
    (nonpairs : is_eta_nonpair_product_root_joinable)
  : is_eta_product_root_joinable.
Proof.
  intros Γ A U t v h.
  pose proof (pair_parts_spec t) as spec.
  destruct (pair_parts t) as [[a u] |] eqn:parts.
  - cbn in spec. subst t.
    pose proof (root_eta_product_pair_unique a u v h) as same.
    subst v. exact (join_refl _).
  - exact (nonpairs Γ A U t v h parts).
Defined.

Context (product_roots : is_eta_product_root_joinable).

(** Given that diagram, every eta root joins any eta step from its source. *)

(** 给定该图式后，每个 η 根均可与同源的任意 η 步骤汇合。 *)

Definition eta_root_join_of_product_roots {Γ : Ctx B} {A : Ty B}
    {t u v : Tm Γ A} (h : RootEtaContract@{b e} t u)
    (k : EtaContractStep@{b e l} t v)
  : Join@{b e p} BetaEtaContractStep@{b e l} u v.
Proof.
  destruct h as [Γ A U f | Γ A U t].
  - exact (join_preserves (λ x, x) (λ x y s, inr s)
      (eta_function_root_join f v k)).
  - destruct (eta_contract_source k) as [r | child].
    + exact (product_roots Γ A U t v r).
    + destruct child as [[x [s z]] | [x [s z]]]; subst v.
      * exact (join_preserves (λ x, x) (λ x y s, inr s)
          (eta_product_left_join t x s)).
      * exact (join_preserves (λ x, x) (λ x y s, inr s)
          (eta_product_right_join t x s)).
Defined.

(** The general two-family context theorem lifts the root diagrams.
    The product-root input remains an explicit parameter of this result. *)

(** 一般双规则族上下文定理提升根图式；积根输入仍为本结果的显式参数。 *)

Definition eta_eta_joinable_of_product_roots (Γ : Ctx B) (A : Ty B)
  : is_locally_joinable@{b e e e p _}
      (@EtaContractStep@{b e l} B Γ A) (@EtaContractStep@{b e l} B Γ A)
      (@BetaEtaContractStep@{b e l} B Γ A).
Proof.
  intros t u v h k.
  exact (context_locally_joinable (@RootEtaContract@{b e} B)
    (@RootEtaContract@{b e} B) (@BetaEtaContractStep@{b e l} B)
    beta_eta_contract_compatible
    (λ Γ A x y s, inr (context_eta_contract s))
    (λ Γ A x y s, inr (context_eta_contract s))
    (λ Γ A x y z r s,
      eta_root_join_of_product_roots r (context_eta_contract s))
    (λ Γ A x y z r s,
      join_sym (eta_root_join_of_product_roots r (context_eta_contract s)))
    Γ A t u v (eta_contract_context h) (eta_contract_context k)).
Defined.

End EtaProductInterface.
