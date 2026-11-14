From Cats.STLC Require Export ReducibilityConstructors.

(** * Strong Normalization of All Typed Terms

    A reducible substitution assigns a reducible term to each variable.
    Structural induction now proves that substituting such an assignment
    into any typed term gives a reducible term. In the lambda case, old
    assignments are renamed into a future context and the newest variable
    is assigned the supplied reducible argument. The existing binder
    substitution equation identifies precisely this assignment.

    Identity substitution is reducible because variables are reducible.
    Thus every intrinsically typed term is reducible, and its candidate
    normalization law yields a tree covering every directed beta step.
    This theorem concerns full beta contraction, including reduction under
    binders. It does not add eta expansion, unit eta or symmetric edges.
    No decision on base labels and no NbE algorithm enter the proof. *)

(** * 所有带类型项的强归一化

    可归约替换为每个变量赋予可归约项。现在用结构归纳证明：将这样的赋值代入
    任意带类型项，所得项都可归约。λ 分支中，旧赋值重命名到后续上下文，最新
    变量赋为传入的可归约实参；既有绑定替换等式恰好识别这一赋值。

    变量可归约，因而恒等替换可归约。所以每个内在类型化项都可归约，再由其
    候选归一化律取得覆盖每个有向 β 步骤的树。定理针对完整 β 收缩，包括绑定
    之下的归约，不加入 η 展开、单位 η 或对称边。证明不要求基类型标签可判定，
    也不使用 NbE 算法。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** ** Reducible Assignments

    Fix arbitrary labels and independent syntax, step, tree and
    classification bounds with [b <= e <= s] and [e < l]. Assignment
    reducibility is pointwise; respectful comparison uses [SubEq] and
    never equality of assignment functions. *)

(** ** 可归约赋值

    固定任意标签及独立的语法、步骤、树和分类界，满足 [b <= e <= s] 和
    [e < l]。赋值的可归约性逐点给出，以 [SubEq] 作尊重性比较，不要求赋值
    函数本身相等。 *)

Section ReducibleAssignments.
Universes b e s l.
Constraint b <= e, e <= s, e < l.
Context {B : Type@{b}}.

(** Each variable receives a reducible term of its own type. *)

(** 每个变量收到其自身类型的可归约项。 *)

Definition is_reducible_sub {Γ Δ : Ctx B} (σ : Sub@{b b} Δ Γ)
  : Type@{s}
  := ∀ A x, Reducible@{b e s l} A Δ (σ A x).

(** Pointwise equal assignments have equivalent reducibility evidence. *)

(** 逐点相等的赋值具有等价的可归约性见证。 *)

Global Instance is_reducible_sub_proper {Γ Δ : Ctx B}
  : Proper (SubEq ==> iffT) (@is_reducible_sub Γ Δ).
Proof.
  intros σ τ h. split; intros p A x.
  - rewrite <- (h A x). exact (p A x).
  - rewrite (h A x). exact (p A x).
Defined.

(** Renaming every assigned term preserves pointwise reducibility. *)

(** 对每个所赋的项重命名，保持逐点可归约性。 *)

Definition reducible_sub_rename {Γ Δ Θ : Ctx B} (σ : Sub Δ Γ)
    (h : is_reducible_sub σ) (ρ : Ren Θ Δ)
  : is_reducible_sub (λ A x, (σ A x)⟨ρ⟩)
  := λ A x, reducible_rename A Δ (σ A x) (h A x) Θ ρ.

(** Extending a reducible assignment by a reducible term preserves it. *)

(** 用可归约项扩张可归约赋值，仍得到可归约赋值。 *)

Definition reducible_sub_extend {Γ Δ : Ctx B} {A : Ty B}
    (σ : Sub Δ Γ) (h : is_reducible_sub σ) (a : Tm Δ A)
    (ha : Reducible@{b e s l} A Δ a)
  : is_reducible_sub (σ ▻Sub a).
Proof. intros U [x | x]; cbn; [exact (h U x) | destruct x; exact ha]. Defined.

(** Every variable assignment in the identity substitution is reducible. *)

(** 恒等替换中的每个变量赋值都可归约。 *)

Definition reducible_sub_id (Γ : Ctx B)
  : is_reducible_sub (Γ := Γ) idSub
  := λ A x, reducible_var A Γ x.

(** The fundamental theorem is structural induction, using the constructor
    laws. Its binder case combines renaming and assignment extension;
    no equality between functions or normalization trees is compared. *)

(** 基本定理是使用构造器律的结构归纳；绑定分支结合重命名与赋值扩张，不比较
    函数或归一化树之间的相等。 *)

Definition reducible_subst {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ Δ (σ : Sub Δ Γ), is_reducible_sub σ →
      Reducible@{b e s l} A Δ t[σ].
Proof.
  induction t; intros Δ σ h; cbn.
  - exact (h A v).
  - exact reducible_unit.
  - exact (reducible_pair (IHt1 Δ σ h) (IHt2 Δ σ h)).
  - exact (reducible_fst (IHt Δ σ h)).
  - exact (reducible_snd (IHt Δ σ h)).
  - apply reducible_lam. intros Θ ρ a ha.
    rewrite subst_lift_rename_single. apply IHt.
    exact (reducible_sub_extend _ (reducible_sub_rename σ h ρ) a ha).
  - exact (reducible_app (IHt1 Δ σ h) (IHt2 Δ σ h)).
Defined.

(** Identity substitution turns the fundamental theorem into
    reducibility of every typed term. *)

(** 恒等替换将基本定理转为每个带类型项的可归约性。 *)

Definition tm_reducible {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : Reducible@{b e s l} A Γ t.
Proof.
  pose proof (reducible_subst t Γ idSub (reducible_sub_id Γ)) as h.
  now rewrite subst_id in h.
Defined.

(** Every well-typed term has a tree for all contextual beta paths. This
    is independent of the choice or termination of a normalization strategy. *)

(** 每个良类型项都有覆盖全部上下文 β 路径的树，独立于归一化策略的选择或终止。 *)

Definition beta_strong_normalization {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : SN@{b e s} (@BetaStep@{b e l b} B Γ A) t
  := reducible_sn A Γ t (tm_reducible t).

(** An infinite directed beta sequence is impossible. This corollary uses
    the general tree argument, not a classical characterization of SN. *)

(** 不可能存在无限有向 β 序列；此推论使用一般树论证，而非 SN 的经典刻画。 *)

Definition beta_no_infinite_sequence {Γ : Ctx B} {A : Ty B}
    (f : nat → Tm Γ A) (h : ∀ n, BetaStep@{b e l b} (f n) (f (S n)))
  : Empty_set
  := sn_no_infinite_sequence f h (beta_strong_normalization (f 0)).

End ReducibleAssignments.
