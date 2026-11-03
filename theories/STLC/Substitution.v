From Cats Require Export STLC.Renaming.

(** * Simultaneous Substitution

    [Sub Δ Γ] assigns a term in Δ to each variable of Γ. Binder lifting first
    weakens the assigned terms and preserves the newest variable. All laws
    below concern raw structural equality and compare maps pointwise. *)

(** * 同时替换

    [Sub Δ Γ] 为 Γ 的每个变量赋一个 Δ 中的项。提升时先弱化已赋的项，并保持
    最新变量。以下定律使用原始结构相等，并逐点比较映射。 *)

Declare Scope stlc_sub_scope.
Delimit Scope stlc_sub_scope with sub.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.

(** A type-preserving assignment of variables to terms in the source context. *)

(** 将变量赋值为源上下文中同类型项的替换。 *)

Definition Sub {B : Type} (Δ Γ : Ctx B)
  : Type
  := ∀ A, Var Γ A → Tm Δ A.

(** Compare substitutions by structural equality at every variable. *)

(** 按每个变量处的结构相等比较替换。 *)

Definition SubEq {B : Type} {Δ Γ : Ctx B} (σ τ : Sub Δ Γ)
  : Type
  := ∀ A x, σ A x = τ A x.

Infix "≈Sub" := SubEq (at level 50, no associativity) : stlc_sub_scope.
Local Open Scope stlc_sub_scope.

(** Pointwise substitution equality is an equivalence relation. *)

(** 替换逐点相等构成等价关系。 *)

Global Instance SubEq_Equivalence {B : Type} {Δ Γ : Ctx B}
  : Equivalence (@SubEq B Δ Γ).
Proof.
  split.
  - intros σ A x. reflexivity.
  - intros σ τ H A x. symmetry. apply H.
  - intros σ τ ν H K A x. transitivity (τ A x); auto.
Defined.

(** Identity substitution assigns each variable its variable term. *)

(** 恒等替换将每个变量赋为对应的变量项。 *)

Definition sub_id {B : Type} {Γ : Ctx B}
  : Sub Γ Γ
  := λ A x, # x.

(** The empty simultaneous assignment, from any context to the empty one. *)

(** 从任意上下文指向空上下文的空同时赋值。 *)

Definition sub_empty {B : Type} {Δ : Ctx B}
  : Sub Δ ctx_empty
  := λ A x, match x with end.

(** All substitutions into the empty context agree pointwise. *)

(** 指向空上下文的所有替换逐点相等。 *)

Lemma sub_empty_unique {B : Type} {Δ : Ctx B} (σ : Sub Δ ctx_empty)
  : σ ≈Sub sub_empty.
Proof. intros A x. destruct x. Qed.

(** Embed a renaming as a substitution consisting of variable terms. *)

(** 将重命名嵌入为由变量项组成的替换。 *)

Definition RenSub {B : Type} {Γ Δ : Ctx B} (ρ : Ren Δ Γ)
  : Sub Δ Γ
  := λ A x, # (ρ A x).

(** The variable-term embedding preserves pointwise renaming equality. *)

(** 变量项嵌入保持重命名的逐点相等。 *)

Global Instance RenSub_proper {B : Type} {Γ Δ : Ctx B}
  : Proper (RenEq ==> SubEq) (@RenSub B Γ Δ).
Proof. intros ρ τ H A x. unfold RenSub. now rewrite H. Qed.

(** Lift a substitution under one binder using the established weakening. *)

(** 使用已有弱化将替换提升到一个绑定变量之下。 *)

Definition sub_lift {B : Type} {Γ Δ : Ctx B} {A : Ty B} (σ : Sub Δ Γ)
  : Sub (Δ ▻ A) (Γ ▻ A)
  := λ U x, match x with
  | inl x => (σ U x)⟨wkRen⟩
  | inr x => tm_var (Γ := Δ ▻ A) (inr x)
  end.

Notation "'idSub'" := sub_id : stlc_sub_scope.
Notation "σ '^↑Sub'" := (sub_lift σ) (at level 35) : stlc_sub_scope.

(** Lifted substitutions preserve pointwise equality of their assignments. *)

(** 替换提升保持赋值的逐点相等。 *)

Global Instance sub_lift_proper {B : Type} {Γ Δ : Ctx B} {A : Ty B}
  : Proper (SubEq ==> SubEq) (@sub_lift B Γ Δ A).
Proof. intros σ τ H U [x | x]; cbn; [now rewrite H | reflexivity]. Qed.

(** Identity substitution remains identity under a binder. *)

(** 恒等替换在绑定变量之下仍为恒等。 *)

Lemma sub_lift_id {B : Type} {Γ : Ctx B} {A : Ty B}
  : (@sub_id B Γ)^↑Sub ≈Sub @sub_id B (Γ ▻ A).
Proof. intros U [x | x]; reflexivity. Qed.

(** Lifted renamings agree pointwise with their substitution embeddings. *)

(** 重命名提升与其替换嵌入逐点相容。 *)

Lemma sub_lift_ren {B : Type} {Γ Δ : Ctx B} {A : Ty B} (ρ : Ren Δ Γ)
  : (@sub_lift B Γ Δ A (RenSub ρ)) ≈Sub RenSub (ρ^↑Ren).
Proof. intros U [x | x]; reflexivity. Qed.

(** Apply a simultaneous substitution, lifting on entering abstraction. *)

(** 应用同时替换，并在进入抽象时提升。 *)

Fixpoint subst {B : Type} {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
    {Δ : Ctx B} (σ : Sub Δ Γ)
  : Tm Δ A
  := match t in Tm Γ A return Sub Δ Γ → Tm Δ A with
  | tm_var x => λ σ, σ _ x
  | tm_unit => λ _, ⋆
  | tm_pair t u => λ σ, ⟨subst t σ, subst u σ⟩
  | tm_fst t => λ σ, π₁ (subst t σ)
  | tm_snd t => λ σ, π₂ (subst t σ)
  | tm_lam t => λ σ, ƛ (subst t (σ^↑Sub))
  | tm_app t u => λ σ, subst t σ · subst u σ
  end σ.

Notation "t '[' σ ']'" := (subst t σ)
  (at level 8, left associativity, format "t [ σ ]") : stlc_tm_scope.

(** Term substitution depends only on pointwise variable assignments. *)

(** 项的替换仅依赖逐点变量赋值。 *)

Lemma subst_ext {B : Type} {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ Δ (σ τ : Sub Δ Γ), σ ≈Sub τ → t[σ] = t[τ].
Proof.
  induction t; intros Δ σ τ H; cbn.
  - apply H.
  - reflexivity.
  - f_equal; [apply IHt1 | apply IHt2]; exact H.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. now apply sub_lift_proper.
  - f_equal; [apply IHt1 | apply IHt2]; exact H.
Qed.

(** Substitution preserves structural term and pointwise map equality. *)

(** 替换保持项的结构相等与映射的逐点相等。 *)

Global Instance subst_proper {B : Type} {Γ Δ : Ctx B} {A : Ty B}
  : Proper (eq ==> SubEq ==> eq) (λ t σ, @subst B Γ A t Δ σ).
Proof. intros t u H σ τ K. destruct H. now apply subst_ext. Qed.

(** Identity substitution leaves every raw term unchanged. *)

(** 恒等替换保持每个原始项。 *)

Lemma subst_id {B : Type} {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : t[idSub] = t.
Proof.
  induction t; cbn; try solve [f_equal; auto].
  f_equal. transitivity (t[idSub]).
  - apply subst_ext. apply sub_lift_id.
  - exact IHt.
Qed.

(** Substitution by renamed variables recovers term renaming. *)

(** 以重命名后的变量作替换，恢复项重命名。 *)

Lemma subst_ren {B : Type} {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ Δ (ρ : Ren Δ Γ), t[RenSub ρ] = t⟨ρ⟩.
Proof.
  induction t; intros Δ ρ; cbn; try solve [f_equal; auto].
  f_equal. transitivity (t[RenSub (ρ^↑Ren)]).
  - apply subst_ext. apply sub_lift_ren.
  - apply IHt.
Qed.

(** Substituting a renamed term composes the two variable assignments. *)

(** 对重命名后的项作替换，等于复合两次变量赋值。 *)

Lemma subst_rename {B : Type} {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ Δ Θ (ρ : Ren Δ Γ) (σ : Sub Θ Δ),
      t⟨ρ⟩[σ] = t[λ U x, σ U (ρ U x)].
Proof.
  induction t; intros Δ Θ ρ σ; cbn; try solve [f_equal; auto].
  f_equal. rewrite IHt. apply subst_ext. intros V [x | x]; reflexivity.
Qed.

(** Renaming a substituted term renames every assigned term. *)

(** 重命名替换后的项，等于重命名每个已赋的项。 *)

Lemma rename_subst {B : Type} {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ Δ Θ (σ : Sub Δ Γ) (ρ : Ren Θ Δ),
      t[σ]⟨ρ⟩ = t[λ U x, (σ U x)⟨ρ⟩].
Proof.
  induction t; intros Δ Θ σ ρ; cbn; try solve [f_equal; auto].
  f_equal. rewrite IHt. apply subst_ext. intros V [x | x]; cbn.
  - apply rename_weaken.
  - reflexivity.
Qed.

(** Substitution under a binder commutes with weakening an existing term. *)

(** 绑定变量之下的替换与已有项的弱化交换。 *)

Lemma subst_weaken {B : Type} {Γ Δ : Ctx B} {A U : Ty B}
    (t : Tm Γ U) (σ : Sub Δ Γ)
  : t⟨@ren_weaken B Γ A⟩[σ^↑Sub] = t[σ]⟨wkRen⟩.
Proof. rewrite subst_rename, rename_subst. reflexivity. Qed.

(** Compose substitutions by applying the second one to every assigned term. *)

(** 将第二次替换作用到每个已赋的项上，以此复合替换。 *)

Definition sub_comp {B : Type} {Γ Δ Θ : Ctx B}
    (σ : Sub Δ Γ) (τ : Sub Θ Δ)
  : Sub Θ Γ
  := λ A x, (σ A x)[τ].

Infix "∘Sub" := sub_comp (at level 40, left associativity) : stlc_sub_scope.

(** Composition preserves pointwise equality of both substitutions. *)

(** 复合保持两侧替换的逐点相等。 *)

Global Instance sub_comp_proper {B : Type} {Γ Δ Θ : Ctx B}
  : Proper (SubEq ==> SubEq ==> SubEq) (@sub_comp B Γ Δ Θ).
Proof.
  intros σ σ' H τ τ' K A x. unfold sub_comp.
  rewrite H. now apply subst_ext.
Qed.

(** Binder lifting preserves substitution composition. *)

(** 绑定变量提升保持替换复合。 *)

Lemma sub_lift_comp {B : Type} {Γ Δ Θ : Ctx B} {A : Ty B}
    (σ : Sub Δ Γ) (τ : Sub Θ Δ)
  : (σ ∘Sub τ)^↑Sub ≈Sub
      (@sub_lift B Γ Δ A σ) ∘Sub τ^↑Sub.
Proof.
  intros U [x | x]; cbn.
  - symmetry. apply subst_weaken.
  - reflexivity.
Qed.

(** Successive term substitutions agree with simultaneous composition. *)

(** 连续项替换与同时替换的复合一致。 *)

Lemma subst_comp {B : Type} {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ Δ Θ (σ : Sub Δ Γ) (τ : Sub Θ Δ), t[σ][τ] = t[σ ∘Sub τ].
Proof.
  induction t; intros Δ Θ σ τ; cbn; try solve [f_equal; auto].
  f_equal. rewrite IHt. apply subst_ext. symmetry. apply sub_lift_comp.
Qed.

(** Left identity for substitution composition. *)

(** 替换复合的左单位律。 *)

Lemma sub_comp_id_l {B : Type} {Γ Δ : Ctx B} (σ : Sub Δ Γ)
  : idSub ∘Sub σ ≈Sub σ.
Proof. intros A x. reflexivity. Qed.

(** Right identity for substitution composition. *)

(** 替换复合的右单位律。 *)

Lemma sub_comp_id_r {B : Type} {Γ Δ : Ctx B} (σ : Sub Δ Γ)
  : σ ∘Sub idSub ≈Sub σ.
Proof. intros A x. apply subst_id. Qed.

(** Associativity follows pointwise from the general term composition law. *)

(** 结合律逐点来自一般项替换复合定律。 *)

Lemma sub_comp_assoc {B : Type} {Γ Δ Θ Ξ : Ctx B}
    (σ : Sub Δ Γ) (τ : Sub Θ Δ) (ν : Sub Ξ Θ)
  : (σ ∘Sub τ) ∘Sub ν ≈Sub σ ∘Sub (τ ∘Sub ν).
Proof. intros A x. apply subst_comp. Qed.

(** Extend a substitution by the term assigned to the newest variable.
    Eliminating its typed marker requires no equality between type labels. *)

(** 用赋给最新变量的项扩张替换；消去带类型标记时不要求类型标签之间的相等。 *)

Definition sub_extend {B : Type} {Γ Δ : Ctx B} {A : Ty B}
    (σ : Sub Δ Γ) (t : Tm Δ A)
  : Sub Δ (Γ ▻ A)
  := λ U x, match x with
  | inl x => σ U x
  | inr x => match x in NewVar _ V return Tm Δ V with
    | new_var => t
    end
  end.

Notation "σ '▻Sub' t" := (sub_extend σ t)
  (at level 40, left associativity) : stlc_sub_scope.

(** Extension preserves pointwise assignment and structural term equality. *)

(** 扩张保持赋值的逐点相等及项的结构相等。 *)

Global Instance sub_extend_proper {B : Type} {Γ Δ : Ctx B} {A : Ty B}
  : Proper (SubEq ==> eq ==> SubEq) (@sub_extend B Γ Δ A).
Proof.
  intros σ τ H t u K. destruct K.
  intros U [x | x]; cbn; [apply H | reflexivity].
Qed.

(** Extension recovers the original assignment on every older variable. *)

(** 扩张在每个旧变量处恢复原赋值。 *)

Lemma sub_extend_β1 {B : Type} {Γ Δ : Ctx B} {A U : Ty B}
    (σ : Sub Δ Γ) (t : Tm Δ A) (x : Var Γ U)
  : (σ ▻Sub t) U (var_succ x) = σ U x.
Proof. reflexivity. Qed.

(** Extension assigns the specified term to the newest variable. *)

(** 扩张将指定项赋给最新变量。 *)

Lemma sub_extend_β2 {B : Type} {Γ Δ : Ctx B} {A : Ty B}
    (σ : Sub Δ Γ) (t : Tm Δ A)
  : (σ ▻Sub t) A var_zero = t.
Proof. reflexivity. Qed.

(** Every substitution into an extended context is recovered from its old
    assignments and its newest component. *)

(** 指向扩张上下文的每个替换都由旧变量赋值及最新分量恢复。 *)

Lemma sub_extend_η {B : Type} {Γ Δ : Ctx B} {A : Ty B}
    (σ : Sub Δ (Γ ▻ A))
  : ((λ U x, σ U (var_succ x)) ▻Sub σ A var_zero) ≈Sub σ.
Proof. intros U [x | x]; cbn; [reflexivity | destruct x; reflexivity]. Qed.

(** Extension commutes with subsequent substitution of all its components. *)

(** 扩张与随后对全部分量作替换相容。 *)

Lemma sub_extend_comp {B : Type} {Γ Δ Θ : Ctx B} {A : Ty B}
    (σ : Sub Δ Γ) (t : Tm Δ A) (τ : Sub Θ Δ)
  : (σ ▻Sub t) ∘Sub τ ≈Sub (σ ∘Sub τ) ▻Sub t[τ].
Proof. intros U [x | x]; cbn; [reflexivity | destruct x; reflexivity]. Qed.

(** Replace only the newest variable, preserving all older variables. *)

(** 只替换最新变量，并保持全部旧变量。 *)

Definition sub_single {B : Type} {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : Sub Γ (Γ ▻ A)
  := idSub ▻Sub t.

(** Single-variable substitution preserves structural equality of its term. *)

(** 单变量替换保持所赋项的结构相等。 *)

Global Instance sub_single_proper {B : Type} {Γ : Ctx B} {A : Ty B}
  : Proper (eq ==> SubEq) (@sub_single B Γ A).
Proof. intros t u H. destruct H. intros U x. reflexivity. Qed.

Notation "t '[' u '/]'" := (subst t (sub_single u))
  (at level 8, left associativity) : stlc_tm_scope.

(** Renaming commutes with replacing the newest variable, provided the
    renaming is lifted on the body. *)

(** 重命名与最新变量的代入交换，其中项体上的重命名须提升。 *)

Lemma rename_single {B : Type} {Γ Δ : Ctx B} {A U : Ty B}
    (t : Tm (Γ ▻ A) U) (u : Tm Γ A) (ρ : Ren Δ Γ)
  : t[u/]⟨ρ⟩ = t⟨ρ^↑Ren⟩[u⟨ρ⟩/].
Proof.
  rewrite rename_subst, subst_rename. apply subst_ext.
  intros V [x | x]; cbn; [reflexivity | destruct x; reflexivity].
Qed.

(** A lifted substitution followed by newest-variable replacement agrees
    pointwise with replacement followed by the original substitution. *)

(** 提升替换后再代入最新变量，与先代入再作原替换逐点一致。 *)

Lemma sub_lift_single {B : Type} {Γ Δ : Ctx B} {A : Ty B}
    (σ : Sub Δ Γ) (u : Tm Γ A)
  : σ^↑Sub ∘Sub sub_single u[σ] ≈Sub sub_single u ∘Sub σ.
Proof.
  intros U [x | x]; cbn.
  - rewrite subst_rename. change ((σ U x)[idSub] = σ U x).
    apply subst_id.
  - destruct x. reflexivity.
Qed.

(** Simultaneous substitution commutes with newest-variable replacement. *)

(** 同时替换与最新变量的代入交换。 *)

Lemma subst_single {B : Type} {Γ Δ : Ctx B} {A U : Ty B}
    (t : Tm (Γ ▻ A) U) (u : Tm Γ A) (σ : Sub Δ Γ)
  : t[u/][σ] = t[σ^↑Sub][u[σ]/].
Proof.
  rewrite !subst_comp. apply subst_ext. symmetry. apply sub_lift_single.
Qed.

(** Weakening below the newest binder, then replacing that binder by the old
    newest variable, recovers the original body. *)

(** 在最新绑定变量之下弱化，再用原最新变量代入该绑定变量，恢复原项体。 *)

Lemma rename_lift_single {B : Type} {Γ : Ctx B} {A U : Ty B}
    (t : Tm (Γ ▻ A) U)
  : t⟨(@ren_weaken B Γ A)^↑Ren⟩[# var_zero/] = t.
Proof.
  rewrite subst_rename. transitivity (t[idSub]).
  - apply subst_ext. intros V [x | x]; cbn;
      [reflexivity | destruct x; reflexivity].
  - apply subst_id.
Qed.
