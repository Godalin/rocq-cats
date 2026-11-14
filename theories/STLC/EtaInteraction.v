From Cats.STLC Require Export
  BetaEtaPaths
  ReductionRoot.
From Cats.Set.Relation Require Import
  Compatible
  QuasiCommutation.

(** * Interaction of Eta Contraction with Beta

    An eta expansion of an introduction is still an introduction. Its
    components return to the old components by finite mixed paths. These
    paths handle beta at an enclosing elimination without dependent
    constructor injection or a decision procedure on base labels.

    The eventual quasi-commutation diagram retains a genuine first beta
    step; a merely convertible replacement would not prove termination. *)

(** * η 收缩与 β 的相互作用

    引入形式的 η 展开仍是引入形式，其分量通过有限混合路径返回旧分量。这些
    路径处理外层消去处的 β，不使用依赖构造器单射或基标签判定过程。

    最终准交换图保留实际的首个 β 步骤；仅给出可转换的替换不足以证明终止。 *)

Local Open Scope relation_scope.
Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** ** Introductions after Eta Expansion

    Fix syntax [b], edges [e], paths [p] and classification [l]. The
    existing typed observers recognize introductions without injecting
    equal indexed constructors. No assertion is made for other heads. *)

(** ** η 展开后的引入形式

    固定语法 [b]、边 [e]、路径 [p] 及分类 [l]。既有带类型观测识别引入形式，
    不对相等的索引构造器作单射消去；对其他头部不作断言。 *)

Section EtaIntroductions.
Universes b e p l.
Context {B : Type@{b}}.

(** A discovered pair retains paths back to its components. A discovered
    lambda retains a path back after applying either body to any argument. *)

(** 发现的配对保留返回其分量的路径；发现的 λ 保留将任意实参代入两个项体
    后的返回路径。 *)

Definition EtaExpansionIntro {Γ : Ctx B} {A : Ty B} (t u : Tm Γ A)
  : Type@{p}
  := match A as V return Tm Γ V → Tm Γ V → Type@{p} with
  | ty_prod U V => λ t u,
      match pair_parts t with
      | Some (a, c) => ∃ a' c', u = ⟨a', c'⟩ ∧
          ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} a' a ∧
          ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} c' c
      | None => unit
      end
  | ty_arr U V => λ t u,
      match lambda_body t with
      | Some body => ∃ body', u = ƛ body' ∧ ∀ a : Tm Γ U,
          ReflTransClosure@{b e p} BetaEtaContractStep@{b e l}
            body'[a/] body[a/]
      | None => unit
      end
  | _ => λ _ _, unit
  end t u.

(** At a root expansion, the added elimination contracts by beta to the
    original component or applied body. Typed observer specifications
    recover the original introduction by homogeneous syntax equality. *)

(** 在根展开处，新增消去通过 β 收缩到原分量或代入后的项体。带类型观测的
    规格以同类型语法相等恢复原引入形式。 *)

Definition root_eta_expansion_intro {Γ : Ctx B} {A : Ty B}
    {t u : Tm Γ A} (h : RootEtaExpand@{b e b} t u)
  : EtaExpansionIntro t u.
Proof.
  destruct h as [Γ A U f | Γ A U t]; cbn.
  - pose proof (lambda_body_spec f) as spec.
    destruct (lambda_body f) as [body |]; cbn in *; [| exact tt].
    rewrite spec. eexists. split; [reflexivity |]. intros a.
    change (ReflTransClosure@{b e p} BetaEtaContractStep@{b e l}
      ((ƛ body)⟨wkRen⟩[a/] · a) body[a/]).
    apply rtc_step. left. rewrite subst_weaken_single.
    exact (context_step_root _ (root_beta_function body a)).
  - pose proof (pair_parts_spec t) as spec.
    destruct (pair_parts t) as [[a c] |]; cbn in *; [| exact tt].
    rewrite spec. eexists; eexists. split; [reflexivity |]. split.
    + exact (rtc_step (inl (context_step_root _ (root_beta_fst a c)))).
    + exact (rtc_step (inl (context_step_root _ (root_beta_snd a c)))).
Defined.

(** Retain the expansion witness to construct a returning contraction
    in the changed child. No recursive child-head analysis is necessary. *)

(** 保留展开见证，在变化的子项中构造返回收缩，无须递归分析子项头部。 *)

Definition eta_expansion_intro_compatible
  : is_compatible (TmContexts B)
      (λ i t u, ContextStep (@RootEtaExpand@{b e b} B) t u ∧
        EtaExpansionIntro t u).
Proof.
  intros [Γ A] [Δ U] c t u [h spec]. split.
  - exact (context_step_lift _ c h).
  - destruct c; cbn.
    + exists u, u0. split; [reflexivity |].
      exact (rtc_step (inr h), rtc_refl _).
    + exists t0, u. split; [reflexivity |].
      exact (rtc_refl _, rtc_step (inr h)).
    + destruct A0; exact tt.
    + destruct U0; exact tt.
    + exists u. split; [reflexivity |]. intros a.
      exact (rtc_step (inr (eta_contract_subst h _ (sub_single a)))).
    + destruct U0; exact tt.
    + destruct U0; exact tt.
Defined.

(** The compatible fold gives the introduction information for an eta
    expansion at arbitrary depth, including beneath binders. *)

(** 相容折叠为任意深度的 η 展开给出引入形式信息，包括绑定之下。 *)

Definition eta_expansion_intro {Γ : Ctx B} {A : Ty B}
    {t u : Tm Γ A} (h : EtaExpandStep@{b e l b} t u)
  : EtaExpansionIntro t u
  := snd (context_closure_preserves (TmContexts B)
      eta_expansion_intro_compatible
      (λ i x y k, (context_step_root _ k, root_eta_expansion_intro k))
      (Γ, A) t u h).

End EtaIntroductions.

(** ** Moving Beta before Eta

    Fix the same four size bounds. Read an expansion from [x] to [y] as
    a contraction from [y] to [x]. Given beta out of [x], construct a
    genuine beta out of [y] followed by a finite mixed path to its target.
    All one-hole operations, including binders, must preserve this diagram. *)

(** ** 将 β 移到 η 之前

    固定相同的四个大小界。将 [x] 到 [y] 的展开读作 [y] 到 [x] 的收缩。
    给定从 [x] 出发的 β，构造从 [y] 出发的实际 β，再接有限混合路径到原
    目标。所有单孔操作，包括绑定，都须保持该图。 *)

Section EtaBetaDiagrams.
Universes b e p l.
Context {B : Type@{b}}.

(** The first edge is beta, whereas the finite remainder may mix rules. *)

(** 首边为 β，而有限剩余部分允许混合规则。 *)

Definition EtaBetaDiagram {Γ : Ctx B} {A : Ty B} (x y : Tm Γ A)
  : Type@{p}
  := ∀ z, BetaStep@{b e l b} x z →
      ∃ v, BetaStep@{b e l b} y v ∧
        ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} v z.

(** A function expansion lifts beta once. A product expansion lifts it
    into both copies, then contracts the resulting eta expansion. *)

(** 函数展开将 β 提升一次；积展开将其提升到两个副本，再收缩结果的 η 展开。 *)

Definition root_eta_beta_diagram {Γ : Ctx B} {A : Ty B}
    {x y : Tm Γ A} (h : RootEtaExpand@{b e b} x y)
  : EtaBetaDiagram x y.
Proof.
  destruct h as [Γ A U f | Γ A U t]; intros z k.
  - exists (ƛ (z⟨wkRen⟩ · (# var_zero))). split.
    + exact (beta_step_lift op_lam (beta_step_lift
        (op_app_l (# var_zero)) (beta_step_rename k _ wkRen))).
    + exact (rtc_step (inr (eta_contract_root
        (root_eta_contract_function z)))).
  - exists (⟨π₁ z, π₂ t⟩). split.
    + exact (beta_step_lift (op_pair_l (π₂ t))
        (beta_step_lift op_fst k)).
    + exact (rtc_cons (inl (beta_step_lift (op_pair_r (π₁ z))
        (beta_step_lift op_snd k)))
        (rtc_step (inr (eta_contract_root (root_eta_contract_product z))))).
Defined.

(** An enclosing root elimination sees an expanded introduction. Observe
    its body or components, beta-contract the expanded introduction first,
    then follow its returning path. In an argument position, substitution
    transports the eta edge to every occurrence of that argument. *)

(** 外层根消去看到一个展开的引入形式。观测其项体或分量，先对展开后的引入
    作 β 收缩，再沿返回路径前进。在实参位置，替换将 η 边传到实参的每次
    出现。 *)

Definition eta_expansion_root_context {i j : TmIndex B}
    (c : TmOperation i j) {x y : TmAt i}
    (h : EtaExpandStep@{b e l b} x y) {z : TmAt j}
    (r : RootBeta@{b e b} (TmContexts B _ _ c x) z)
  : ∃ v, BetaStep@{b e l b} (TmContexts B _ _ c y) v ∧
      ReflTransClosure@{b e p} BetaEtaContractStep@{b e l} v z.
Proof.
  pose proof (root_beta_contractum r) as target.
  destruct c as [Γ A U a | Γ A U f | Γ A U | Γ A U | Γ A U |
    Γ A U a | Γ A U f]; cbn in *; try discriminate target.
  - pose proof (eta_expansion_intro h) as intro.
    unfold EtaExpansionIntro in intro.
    destruct (pair_parts x) as [[a d] |] eqn:parts;
      cbn in *; rewrite ?parts in target, intro; cbn in *;
      [| discriminate target].
    injection target as target. subst z.
    destruct intro as [a' [d' [shape [pa pd]]]]. subst y.
    exists a'. split; [| exact pa].
    exact (context_step_root _ (root_beta_fst a' d')).
  - pose proof (eta_expansion_intro h) as intro.
    unfold EtaExpansionIntro in intro.
    destruct (pair_parts x) as [[a d] |] eqn:parts;
      cbn in *; rewrite ?parts in target, intro; cbn in *;
      [| discriminate target].
    injection target as target. subst z.
    destruct intro as [a' [d' [shape [pa pd]]]]. subst y.
    exists d'. split; [| exact pd].
    exact (context_step_root _ (root_beta_snd a' d')).
  - pose proof (eta_expansion_intro h) as intro.
    unfold EtaExpansionIntro in intro.
    destruct (lambda_body x) as [body |] eqn:body_shape;
      cbn in *; rewrite ?body_shape in target, intro; cbn in *;
      [| discriminate target].
    injection target as target. subst z.
    destruct intro as [body' [shape back]]. subst y.
    exists body'[a/]. split; [| exact (back a)].
    exact (context_step_root _ (root_beta_function body' a)).
  - pose proof (lambda_body_spec f) as spec.
    destruct (lambda_body f) as [body |] eqn:body_shape;
      cbn in *; rewrite ?body_shape in target, spec; cbn in *;
      [| discriminate target].
    injection target as target. subst z.
    exists body[y/]. split.
    + rewrite spec. exact (context_step_root _ (root_beta_function body y)).
    + exact (beta_eta_rtc_single body (rtc_step (inr h))).
Defined.

(** Retain the original expansion for disjoint-position and enclosing-root
    cases. A beta step in the varying child uses its inductive diagram;
    a beta step in a fixed child is followed by the original eta edge. *)

(** 为不相交位置及外层根情形保留原展开。变化子项中的 β 使用其归纳图；固定
    子项中的 β 则后接原 η 边。 *)

Definition eta_beta_diagram_compatible
  : is_compatible (TmContexts B)
      (λ i x y, ContextStep (@RootEtaExpand@{b e b} B) x y ∧
        EtaBetaDiagram x y).
Proof.
  intros [Γ A] [Δ U] c x y [h ih]. split.
  - exact (context_step_lift _ c h).
  - destruct c; cbn; intros z k.
    + destruct (beta_step_pair_inv k) as [[v [kv shape]] | [v [kv shape]]];
        subst z.
      * destruct (ih v kv) as [w [first tail]]. exists ⟨w, u⟩. split.
        -- exact (beta_step_lift (op_pair_l u) first).
        -- exact (beta_eta_rtc_lift (op_pair_l u) tail).
      * exists ⟨y, v⟩. split.
        -- exact (beta_step_lift (op_pair_r y) kv).
        -- exact (rtc_step (inr (eta_contract_lift (op_pair_l v) h))).
    + destruct (beta_step_pair_inv k) as [[v [kv shape]] | [v [kv shape]]];
        subst z.
      * exists ⟨v, y⟩. split.
        -- exact (beta_step_lift (op_pair_l y) kv).
        -- exact (rtc_step (inr (eta_contract_lift (op_pair_r v) h))).
      * destruct (ih v kv) as [w [first tail]]. exists ⟨t, w⟩. split.
        -- exact (beta_step_lift (op_pair_r t) first).
        -- exact (beta_eta_rtc_lift (op_pair_r t) tail).
    + destruct (beta_step_fst_inv k) as [r | [v [kv shape]]].
      * exact (eta_expansion_root_context op_fst h r).
      * subst z. destruct (ih v kv) as [w [first tail]].
        exists (π₁ w). split.
        -- exact (beta_step_lift op_fst first).
        -- exact (beta_eta_rtc_lift op_fst tail).
    + destruct (beta_step_snd_inv k) as [r | [v [kv shape]]].
      * exact (eta_expansion_root_context op_snd h r).
      * subst z. destruct (ih v kv) as [w [first tail]].
        exists (π₂ w). split.
        -- exact (beta_step_lift op_snd first).
        -- exact (beta_eta_rtc_lift op_snd tail).
    + destruct (beta_step_lam_inv k) as [v [kv shape]]. subst z.
      destruct (ih v kv) as [w [first tail]]. exists (ƛ w). split.
      * exact (beta_step_lift op_lam first).
      * exact (beta_eta_rtc_lift op_lam tail).
    + destruct (beta_step_app_inv k) as [r | [[v [kv shape]] | [v [kv shape]]]].
      * exact (eta_expansion_root_context (op_app_l u) h r).
      * subst z. destruct (ih v kv) as [w [first tail]]. exists (w · u). split.
        -- exact (beta_step_lift (op_app_l u) first).
        -- exact (beta_eta_rtc_lift (op_app_l u) tail).
      * subst z. exists (y · v). split.
        -- exact (beta_step_lift (op_app_r y) kv).
        -- exact (rtc_step (inr (eta_contract_lift (op_app_l v) h))).
    + destruct (beta_step_app_inv k) as [r | [[v [kv shape]] | [v [kv shape]]]].
      * exact (eta_expansion_root_context (op_app_r t) h r).
      * subst z. exists (v · y). split.
        -- exact (beta_step_lift (op_app_l y) kv).
        -- exact (rtc_step (inr (eta_contract_lift (op_app_r v) h))).
      * subst z. destruct (ih v kv) as [w [first tail]]. exists (t · w). split.
        -- exact (beta_step_lift (op_app_r t) first).
        -- exact (beta_eta_rtc_lift (op_app_r t) tail).
Defined.

(** Fold the contextual expansion into its interaction diagram. This
    covers beta/eta overlap as well as disjoint and nested positions. *)

(** 将上下文展开折叠到其相互作用图中，覆盖 βη 重叠及不相交、嵌套位置。 *)

Definition eta_beta_diagram {Γ : Ctx B} {A : Ty B} {x y : Tm Γ A}
    (h : EtaExpandStep@{b e l b} x y)
  : EtaBetaDiagram x y
  := snd (context_closure_preserves (TmContexts B)
      eta_beta_diagram_compatible
      (λ i x y k, (context_step_root _ k, root_eta_beta_diagram k))
      (Γ, A) x y h).

(** Beta quasi-commutes over eta contraction on each typed judgement. *)

(** 在每个带类型判断处，β 在 η 收缩上准交换。 *)

Definition beta_eta_quasi_commuting (Γ : Ctx B) (A : Ty B)
  : is_quasi_commuting@{b e e p _ _}
      (@BetaStep@{b e l b} B Γ A) (@EtaContractStep@{b e l} B Γ A)
  := λ x y z h k, eta_beta_diagram h z k.

End EtaBetaDiagrams.
