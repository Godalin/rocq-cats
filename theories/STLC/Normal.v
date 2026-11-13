From Cats Require Export STLC.Renaming.

(** * Neutral Terms and Long Normal Forms

    This is the syntactic foundation of normalization by evaluation.
    A neutral term is blocked on a variable; its eliminations cannot perform
    beta reduction. A normal form is eta long: at unit, product and function
    types its outer constructor is respectively unit, pairing and abstraction.
    Only a base-type normal form may be a neutral term.

    Neutral applications have normal arguments. Thus neither family contains
    a beta redex, including inside an argument or under a binder. Neutral
    terms at arbitrary types are still needed as intermediate blocked values;
    a neutral function is not itself a long normal form at function type.

    These are indexed syntax trees with native structural equality, like
    [Tm]. No equality decision on base labels, quotient or equality of
    functions is assumed. The embeddings are explicit competing views of
    the trees, rather than coercions. This module only changes contexts by
    renaming: arbitrary substitution need not preserve normality. *)

(** * 中性项与长正规形

    这是求值正规化的语法基础。中性项被变量阻塞，其消去不能进行 β 归约。
    正规形是 η 长的：在单位、积、函数类型处，最外层构造器分别是单位项、
    配对与抽象。只有基类型的正规形可以直接是中性项。

    中性应用要求实参已是正规形。因此两个族都不包含 β 可归约式，包括实参
    内部或绑定之下。仍须保留任意类型处的中性项，作为被阻塞的中间值；中性
    函数本身并不是函数类型的长正规形。

    与 [Tm] 一样，这些是以原生结构相等比较的带索引语法树，不假设基标签的
    可判定相等、商或函数相等。嵌入是显式的另一种观察方式，不注册为强制转换。
    本模块只通过重命名更换上下文：任意替换不一定保持正规性。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_tm_scope.

(** Mutually indexed syntax: neutral heads admit eliminations, while long
    normal forms introduce every non-base type. Both live at the signature
    universe; equational evidence will have its own level in clients. *)

(** 相互索引的语法：中性头允许消去，长正规形则在每个非基类型处使用引入。
    两者位于签名宇宙；客户端的等式见证另有独立层级。 *)

Inductive Ne@{b} {B : Type@{b}}
  : Ctx B → Ty B → Type@{b}
  :=| ne_var {Γ A} : Var Γ A → Ne Γ A
    | ne_app {Γ A U} : Ne Γ (A ⇒ U) → Nf Γ A → Ne Γ U
    | ne_fst {Γ A U} : Ne Γ (A × U) → Ne Γ A
    | ne_snd {Γ A U} : Ne Γ (A × U) → Ne Γ U
with Nf {B : Type@{b}}
  : Ctx B → Ty B → Type@{b}
  :=| nf_base {Γ b} : Ne Γ (ty_base b) → Nf Γ (ty_base b)
    | nf_unit {Γ} : Nf Γ ⊤
    | nf_pair {Γ A U} : Nf Γ A → Nf Γ U → Nf Γ (A × U)
    | nf_lam {Γ A U} : Nf (Γ ▻ A) U → Nf Γ (A ⇒ U).

Arguments ne_var {_ _ _} _.
Arguments ne_app {_ _ _ _} _ _.
Arguments ne_fst {_ _ _ _} _.
Arguments ne_snd {_ _ _ _} _.
Arguments nf_base {_ _ _} _.
Arguments nf_unit {_ _}.
Arguments nf_pair {_ _ _ _} _ _.
Arguments nf_lam {_ _ _ _} _.

(** Forget the neutral/normal invariant, retaining exactly the raw tree. *)

(** 忘却中性或正规不变量，原样保留原始语法树。 *)

Fixpoint embed_ne {B : Type} {Γ : Ctx B} {A : Ty B} (n : Ne Γ A)
  : Tm Γ A
  := match n with
  | ne_var x => # x
  | ne_app n v => embed_ne n · embed_nf v
  | ne_fst n => π₁ (embed_ne n)
  | ne_snd n => π₂ (embed_ne n)
  end
with embed_nf {B : Type} {Γ : Ctx B} {A : Ty B} (v : Nf Γ A)
  : Tm Γ A
  := match v with
  | nf_base n => embed_ne n
  | nf_unit => ⋆
  | nf_pair v w => ⟨embed_nf v, embed_nf w⟩
  | nf_lam v => ƛ (embed_nf v)
  end.

(** Renaming preserves both invariants. The lambda case lifts the renaming
    exactly as raw syntax does; neutral application renames its normal
    argument through the other half of this mutual recursion. *)

(** 重命名保持两个不变量。λ 情形与原始语法一样提升重命名；中性应用通过相互
    递归的另一部分重命名其正规实参。 *)

Fixpoint rename_ne {B : Type} {Γ : Ctx B} {A : Ty B} (n : Ne Γ A)
    {Δ : Ctx B} (ρ : Ren Δ Γ)
  : Ne Δ A
  := match n in Ne Γ A return Ren Δ Γ → Ne Δ A with
  | ne_var x => λ ρ, ne_var (ρ _ x)
  | ne_app n v => λ ρ, ne_app (rename_ne n ρ) (rename_nf v ρ)
  | ne_fst n => λ ρ, ne_fst (rename_ne n ρ)
  | ne_snd n => λ ρ, ne_snd (rename_ne n ρ)
  end ρ
with rename_nf {B : Type} {Γ : Ctx B} {A : Ty B} (v : Nf Γ A)
    {Δ : Ctx B} (ρ : Ren Δ Γ)
  : Nf Δ A
  := match v in Nf Γ A return Ren Δ Γ → Nf Δ A with
  | nf_base n => λ ρ, nf_base (rename_ne n ρ)
  | nf_unit => λ _, nf_unit
  | nf_pair v w => λ ρ, nf_pair (rename_nf v ρ) (rename_nf w ρ)
  | nf_lam v => λ ρ, nf_lam (rename_nf v (ρ^↑Ren))
  end ρ.

Local Set Warnings "-postfix-notation-not-level-1".
Notation "n '⟨' ρ '⟩ne'" := (rename_ne n ρ)
  (at level 8, left associativity) : stlc_ren_scope.
Notation "v '⟨' ρ '⟩nf'" := (rename_nf v ρ)
  (at level 8, left associativity) : stlc_ren_scope.
Local Set Warnings "+postfix-notation-not-level-1".

(** Pointwise equality of variable assignments suffices to compare renamed
    trees; no function extensionality is needed. *)

(** 变量赋值的逐点相等足以比较重命名后的语法树，无须函数外延性。 *)

Fixpoint rename_ne_ext {B : Type} {Γ : Ctx B} {A : Ty B} (n : Ne Γ A)
    {Δ : Ctx B} (ρ τ : Ren Δ Γ) (h : ρ ≈Ren τ)
  : n⟨ρ⟩ne = n⟨τ⟩ne
with rename_nf_ext {B : Type} {Γ : Ctx B} {A : Ty B} (v : Nf Γ A)
    {Δ : Ctx B} (ρ τ : Ren Δ Γ) (h : ρ ≈Ren τ)
  : v⟨ρ⟩nf = v⟨τ⟩nf.
Proof.
  - destruct n; cbn; f_equal.
    + apply h.
    + apply rename_ne_ext. exact h.
    + apply rename_nf_ext. exact h.
    + apply rename_ne_ext. exact h.
    + apply rename_ne_ext. exact h.
  - destruct v; cbn; f_equal.
    + apply rename_ne_ext. exact h.
    + apply rename_nf_ext. exact h.
    + apply rename_nf_ext. exact h.
    + apply rename_nf_ext. now apply ren_lift_proper.
Defined.

(** Renaming is respectful for structural trees and pointwise renamings. *)

(** 重命名尊重语法树的结构相等与重命名的逐点相等。 *)

Global Instance rename_ne_proper {B : Type} {Γ Δ : Ctx B} {A : Ty B}
  : Proper (eq ==> RenEq ==> eq) (λ n ρ, @rename_ne B Γ A n Δ ρ).
Proof. intros n m h ρ τ k. destruct h. now apply rename_ne_ext. Defined.

(** The normal-form action has the same respectfulness. *)

(** 正规形上的作用具有相同的保相等性质。 *)

Global Instance rename_nf_proper {B : Type} {Γ Δ : Ctx B} {A : Ty B}
  : Proper (eq ==> RenEq ==> eq) (λ v ρ, @rename_nf B Γ A v Δ ρ).
Proof. intros v w h ρ τ k. destruct h. now apply rename_nf_ext. Defined.

(** Identity renaming fixes both kinds of trees, including under binders. *)

(** 恒等重命名保持两种语法树，包括绑定之下。 *)

Fixpoint rename_ne_id {B : Type} {Γ : Ctx B} {A : Ty B} (n : Ne Γ A)
  : n⟨idRen⟩ne = n
with rename_nf_id {B : Type} {Γ : Ctx B} {A : Ty B} (v : Nf Γ A)
  : v⟨idRen⟩nf = v.
Proof.
  - destruct n; cbn; f_equal; auto using rename_ne_id, rename_nf_id.
  - destruct v; cbn; f_equal; auto using rename_ne_id, rename_nf_id.
    transitivity (v⟨idRen⟩nf).
    + apply rename_nf_ext. apply ren_lift_id.
    + apply rename_nf_id.
Defined.

(** Successive renamings compose in the existing context-map direction. *)

(** 连续重命名按既有上下文映射的方向复合。 *)

Fixpoint rename_ne_comp {B : Type} {Γ : Ctx B} {A : Ty B} (n : Ne Γ A)
    {Δ Θ : Ctx B} (ρ : Ren Δ Γ) (τ : Ren Θ Δ)
  : n⟨ρ⟩ne⟨τ⟩ne = n⟨ρ ∘Ren τ⟩ne
with rename_nf_comp {B : Type} {Γ : Ctx B} {A : Ty B} (v : Nf Γ A)
    {Δ Θ : Ctx B} (ρ : Ren Δ Γ) (τ : Ren Θ Δ)
  : v⟨ρ⟩nf⟨τ⟩nf = v⟨ρ ∘Ren τ⟩nf.
Proof.
  - destruct n; cbn; f_equal; auto using rename_ne_comp, rename_nf_comp.
  - destruct v; cbn; f_equal; auto using rename_ne_comp, rename_nf_comp.
    rewrite rename_nf_comp. apply rename_nf_ext.
    symmetry. apply ren_lift_comp.
Defined.

(** Weakening a neutral term commutes with a renaming lifted under the
    same new binder. This derived coherence is used by eta expansion. *)

(** 中性项的弱化与同一新绑定之下的提升重命名交换。η 展开将使用这条导出的
    相容律。 *)

Lemma rename_ne_weaken {B : Type} {Γ Δ : Ctx B} {A U : Ty B}
    (n : Ne Γ U) (ρ : Ren Δ Γ)
  : n⟨@ren_weaken B Γ A⟩ne⟨ρ^↑Ren⟩ne = n⟨ρ⟩ne⟨wkRen⟩ne.
Proof. rewrite !rename_ne_comp. reflexivity. Defined.

(** Embedding commutes strictly with renaming. These equations connect the
    new syntax actions to existing raw renaming and later beta/eta proofs. *)

(** 嵌入与重命名严格交换。这些等式将新语法上的作用连接到既有的原始重命名
    以及后续 βη 证明。 *)

Fixpoint embed_rename_ne {B : Type} {Γ : Ctx B} {A : Ty B} (n : Ne Γ A)
    {Δ : Ctx B} (ρ : Ren Δ Γ)
  : embed_ne (n⟨ρ⟩ne) = (embed_ne n)⟨ρ⟩
with embed_rename_nf {B : Type} {Γ : Ctx B} {A : Ty B} (v : Nf Γ A)
    {Δ : Ctx B} (ρ : Ren Δ Γ)
  : embed_nf (v⟨ρ⟩nf) = (embed_nf v)⟨ρ⟩.
Proof.
  - destruct n; cbn; f_equal; auto using embed_rename_ne, embed_rename_nf.
  - destruct v; cbn; try reflexivity;
      try solve [f_equal; auto using embed_rename_ne, embed_rename_nf].
Defined.
