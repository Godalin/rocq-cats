From Cats Require Export STLC.Syntax.

(** * Renaming and Binder Lifting

    [Ren Δ Γ] maps variables of Γ into Δ, in the direction of a context
    morphism Δ → Γ. Comparisons are pointwise structural equality, without
    equality of functions or assumptions on base type labels. *)

(** * 重命名与绑定变量提升

    [Ren Δ Γ] 将 Γ 的变量映到 Δ，与上下文态射 Δ → Γ 的方向一致。映射按逐点
    结构相等比较，不要求函数相等或基类型标签具有额外性质。 *)

(** ** A change of available inputs

    Read [Ren Δ Γ] as a context arrow from [Δ] to [Γ]: for each variable
    requested by [Γ], it selects an available variable in [Δ]. Applying it
    to a term therefore changes that term's context from [Γ] to [Δ]. This
    orientation will be the orientation of syntactic substitution and
    categorical composition as well.

    Weakening adds an unused newest input. Lifting a renaming under a binder
    has a different role: it weakens all selected old variables and maps the
    freshly bound variable to itself. Structural induction proves the
    identity and composition laws of these actions. Equality of renamings
    is pointwise [RenEq], which is enough to prove equality of renamed terms
    without asserting equality of functions. *)

(** ** 更换可用输入

    将 [Ren Δ Γ] 读作从 [Δ] 到 [Γ] 的上下文箭头：它为 [Γ] 所需的每个变量
    选取 [Δ] 中的一个可用变量。因此，作用于项时，上下文从 [Γ] 变为 [Δ]。
    后续的语法替换与范畴复合也采用相同方向。

    弱化增加一个暂不使用的最新输入。绑定之下的重命名提升则有另一项职责：
    所选旧变量全部弱化，新绑定变量映为自身。这些作用的单位律和复合律通过
    结构归纳证明。重命名以逐点 [RenEq] 比较，足以推出重命名后项的相等，
    无须断言两个函数本身相等。 *)

Declare Scope stlc_ren_scope.
Delimit Scope stlc_ren_scope with ren.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.

(** A type-preserving assignment of variables to variables. *)

(** 将变量赋值为同类型变量的重命名。 *)

Definition Ren {B : Type} (Δ Γ : Ctx B)
  : Type
  := ∀ A, Var Γ A → Var Δ A.

(** Pointwise equality of renamings in their concrete variable syntax. *)

(** 重命名在具体变量语法上的逐点相等。 *)

Definition RenEq {B : Type} {Δ Γ : Ctx B} (ρ τ : Ren Δ Γ)
  : Type
  := ∀ A x, ρ A x = τ A x.

Infix "≈Ren" := RenEq (at level 50, no associativity) : stlc_ren_scope.
Local Open Scope stlc_ren_scope.

(** Pointwise renaming equality is an equivalence relation. *)

(** 重命名逐点相等构成等价关系。 *)

Global Instance RenEq_Equivalence {B : Type} {Δ Γ : Ctx B}
  : Equivalence (@RenEq B Δ Γ).
Proof.
  split.
  - intros ρ A x. reflexivity.
  - intros ρ τ H A x. symmetry. apply H.
  - intros ρ τ ν H K A x. transitivity (τ A x); auto.
Defined.

(** The identity assignment of variables. *)

(** 变量的恒等赋值。 *)

Definition ren_id {B : Type} {Γ : Ctx B}
  : Ren Γ Γ
  := λ A x, x.

(** The unique variable assignment into the empty context. *)

(** 指向空上下文的唯一变量赋值。 *)

Definition ren_empty {B : Type} {Δ : Ctx B}
  : Ren Δ ctx_empty
  := λ A x, match x with end.

(** Empty-context assignments agree because there are no source variables. *)

(** 空上下文没有待赋值变量，因此所有此类赋值逐点相等。 *)

Lemma ren_empty_unique {B : Type} {Δ : Ctx B} (ρ : Ren Δ ctx_empty)
  : ρ ≈Ren ren_empty.
Proof. intros A x. destruct x. Qed.

(** Compose context maps; variable assignments act in the opposite order. *)

(** 复合上下文映射；变量赋值按反向顺序作用。 *)

Definition ren_comp {B : Type} {Γ Δ Θ : Ctx B}
    (ρ : Ren Δ Γ) (τ : Ren Θ Δ)
  : Ren Θ Γ
  := λ A x, τ A (ρ A x).

Infix "∘Ren" := ren_comp (at level 40, left associativity) : stlc_ren_scope.

(** Weakening embeds all existing variables under one new binder. *)

(** 弱化将所有已有变量嵌入新增一个绑定变量的上下文。 *)

Definition ren_weaken {B : Type} {Γ : Ctx B} {A : Ty B}
  : Ren (Γ ▻ A) Γ
  := λ U x, var_succ x.

(** Lift a renaming across a binder, keeping the newest marker fixed. *)

(** 将重命名提升到绑定变量之下，并保持最新变量标记。 *)

Definition ren_lift {B : Type} {Γ Δ : Ctx B} {A : Ty B} (ρ : Ren Δ Γ)
  : Ren (Δ ▻ A) (Γ ▻ A)
  := λ U x, match x with
  | inl x => inl (ρ U x)
  | inr x => inr x
  end.

Notation "'idRen'" := ren_id : stlc_ren_scope.
Notation "'wkRen'" := ren_weaken : stlc_ren_scope.
Notation "ρ '^↑Ren'" := (ren_lift ρ) (at level 35) : stlc_ren_scope.

(** Composition preserves pointwise equality of both renamings. *)

(** 复合保持两侧重命名的逐点相等。 *)

Global Instance ren_comp_proper {B : Type} {Γ Δ Θ : Ctx B}
  : Proper (RenEq ==> RenEq ==> RenEq) (@ren_comp B Γ Δ Θ).
Proof.
  intros ρ ρ' H τ τ' K A x. unfold ren_comp. rewrite H. apply K.
Qed.

(** Binder lifting preserves pointwise equality. *)

(** 绑定变量提升保持逐点相等。 *)

Global Instance ren_lift_proper {B : Type} {Γ Δ : Ctx B} {A : Ty B}
  : Proper (RenEq ==> RenEq) (@ren_lift B Γ Δ A).
Proof. intros ρ τ H U [x | x]; cbn; [now rewrite H | reflexivity]. Qed.

(** Left identity for context-map composition. *)

(** 上下文映射复合的左单位律。 *)

Lemma ren_comp_id_l {B : Type} {Γ Δ : Ctx B} (ρ : Ren Δ Γ)
  : idRen ∘Ren ρ ≈Ren ρ.
Proof. intros A x. reflexivity. Qed.

(** Right identity for context-map composition. *)

(** 上下文映射复合的右单位律。 *)

Lemma ren_comp_id_r {B : Type} {Γ Δ : Ctx B} (ρ : Ren Δ Γ)
  : ρ ∘Ren idRen ≈Ren ρ.
Proof. intros A x. reflexivity. Qed.

(** Associativity compares assignments pointwise. *)

(** 结合律逐点比较变量赋值。 *)

Lemma ren_comp_assoc {B : Type} {Γ Δ Θ Ξ : Ctx B}
    (ρ : Ren Δ Γ) (τ : Ren Θ Δ) (ν : Ren Ξ Θ)
  : (ρ ∘Ren τ) ∘Ren ν ≈Ren ρ ∘Ren (τ ∘Ren ν).
Proof. intros A x. reflexivity. Qed.

(** Lifting preserves identity. *)

(** 提升保持恒等。 *)

Lemma ren_lift_id {B : Type} {Γ : Ctx B} {A : Ty B}
  : (@ren_id B Γ)^↑Ren ≈Ren @ren_id B (Γ ▻ A).
Proof. intros U [x | x]; reflexivity. Qed.

(** Lifting preserves composition. *)

(** 提升保持复合。 *)

Lemma ren_lift_comp {B : Type} {Γ Δ Θ : Ctx B} {A : Ty B}
    (ρ : Ren Δ Γ) (τ : Ren Θ Δ)
  : (ρ ∘Ren τ)^↑Ren ≈Ren
      (@ren_lift B Γ Δ A ρ) ∘Ren τ^↑Ren.
Proof. intros U [x | x]; reflexivity. Qed.

(** Rename terms recursively, lifting exactly once when entering abstraction. *)

(** 递归重命名项；进入抽象时恰好提升一次。 *)

Fixpoint rename {B : Type} {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
    {Δ : Ctx B} (ρ : Ren Δ Γ)
  : Tm Δ A
  := match t in Tm Γ A return Ren Δ Γ → Tm Δ A with
  | tm_var x => λ ρ, # (ρ _ x)
  | tm_unit => λ _, ⋆
  | tm_pair t u => λ ρ, ⟨rename t ρ, rename u ρ⟩
  | tm_fst t => λ ρ, π₁ (rename t ρ)
  | tm_snd t => λ ρ, π₂ (rename t ρ)
  | tm_lam t => λ ρ, ƛ (rename t (ρ^↑Ren))
  | tm_app t u => λ ρ, rename t ρ · rename u ρ
  end ρ.

Notation "t '⟨' ρ '⟩'" := (rename t ρ)
  (at level 8, left associativity) : stlc_tm_scope.

(** Term renaming depends only on the pointwise assignment. *)

(** 项的重命名仅依赖逐点变量赋值。 *)

Lemma rename_ext {B : Type} {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ Δ (ρ τ : Ren Δ Γ), ρ ≈Ren τ → t⟨ρ⟩ = t⟨τ⟩.
Proof.
  induction t; intros Δ ρ τ H; cbn.
  - f_equal. apply H.
  - reflexivity.
  - f_equal; [apply IHt1 | apply IHt2]; exact H.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. exact H.
  - f_equal. apply IHt. now apply ren_lift_proper.
  - f_equal; [apply IHt1 | apply IHt2]; exact H.
Qed.

(** Renaming preserves structural term equality and pointwise map equality. *)

(** 重命名保持项的结构相等与映射的逐点相等。 *)

Global Instance rename_proper {B : Type} {Γ Δ : Ctx B} {A : Ty B}
  : Proper (eq ==> RenEq ==> eq) (λ t ρ, @rename B Γ A t Δ ρ).
Proof. intros t u H ρ τ K. destruct H. now apply rename_ext. Qed.

(** Identity renaming leaves every raw term unchanged. *)

(** 恒等重命名保持每个原始项。 *)

Lemma rename_id {B : Type} {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : t⟨idRen⟩ = t.
Proof.
  induction t; cbn; try solve [f_equal; auto].
  f_equal. transitivity (t⟨idRen⟩).
  - apply rename_ext. apply ren_lift_id.
  - exact IHt.
Qed.

(** Successive term renamings compose as context maps. *)

(** 连续项重命名按上下文映射复合。 *)

Lemma rename_comp {B : Type} {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ Δ Θ (ρ : Ren Δ Γ) (τ : Ren Θ Δ),
      t⟨ρ⟩⟨τ⟩ = t⟨ρ ∘Ren τ⟩.
Proof.
  induction t; intros Δ Θ ρ τ; cbn; try solve [f_equal; auto].
  f_equal. rewrite IHt. apply rename_ext. symmetry. apply ren_lift_comp.
Qed.

(** Weakening commutes with a renaming lifted under the new binder. *)

(** 弱化与新绑定变量之下的提升重命名交换。 *)

Lemma rename_weaken {B : Type} {Γ Δ : Ctx B} {A U : Ty B}
    (t : Tm Γ U) (ρ : Ren Δ Γ)
  : t⟨@ren_weaken B Γ A⟩⟨ρ^↑Ren⟩ = t⟨ρ⟩⟨wkRen⟩.
Proof. rewrite !rename_comp. reflexivity. Qed.
