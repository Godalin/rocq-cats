From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Terminal.
From Cats Require Import
  Instance.Set.Fam.Core
  Instance.Set.Fam.Cat.

(** * Categories with Families

    Context homs, types and terms use the same foundational [SetC] and its
    specified equality. A family-valued presheaf carries types, terms and
    coherent conversion; there are no separate type/term equality fields. *)

(** * 带族范畴

    上下文态射、类型与项都使用基础 [SetC] 及其指定相等。族值预层承载类型、项和
    相干转换，不另设平行的类型或项相等字段。 *)

Section TypesAndTerms.
Context {C : Cat} (T : Fct (C^op) FamCat).

(** The setoid of types in a context, extracted from the family-valued
    presheaf. *)

(** 从族值预层提取的上下文中的类型广集。 *)

Definition Ty (Γ : @Ob C)
  : SetC
  := famC_base (T Γ).
(** The coherent family of terms indexed by the context's type setoid. *)

(** 以上下文类型广集为索引的相干项族。 *)

Definition Tm (Γ : @Ob C)
  : FamS (Ty Γ)
  := famC_fam (T Γ).

(** Substitute types along a context morphism. *)

(** 沿上下文态射替换类型。 *)

Definition ty_sub {Δ Γ : @Ob C} (σ : Hom Δ Γ)
  : Ty Γ →r Ty Δ
  := famF_base (fmap T σ).

(** Substitute a term into the correspondingly substituted type. *)

(** 将项替换到对应的替换类型中。 *)

Definition tm_sub {Δ Γ : @Ob C} (σ : Hom Δ Γ) {A : Ty Γ}
  : Tm Γ A →r Tm Δ (ty_sub σ A)
  := famF_fam (fmap T σ) A.

(** Substitution sends designated type equality to designated type equality. *)

(** 替换将指定类型相等送到指定类型相等。 *)

Definition ty_eq_sub {Δ Γ : @Ob C} (σ : Hom Δ Γ) {A B : Ty Γ} (e : A ≈S B)
  : ty_sub σ A ≈S ty_sub σ B
  := @func_proper _ _ (ty_sub σ) _ _ e.

(** Convert terms along the coherent transport of designated type equality. *)

(** 沿指定类型相等的相干运输转换项。 *)

Definition tm_conv {Γ : @Ob C} {A B : Ty Γ} (e : A ≈S B)
  : Tm Γ A →r Tm Γ B
  := transpS (Tm Γ) e.

(** Compatibility with identities for [ty_sub]. *)

(** [ty_sub] 与恒等的相容性。 *)

Definition ty_sub_id {Γ : @Ob C} (A : Ty Γ)
  : ty_sub id A ≈S A
  := (functor_id (C^op) FamCat T).1 A.

(** Compatibility with composition for [ty_sub]. *)

(** [ty_sub] 与复合的相容性。 *)

Definition ty_sub_comp {Γ Δ Θ : @Ob C} (σ : Hom Δ Γ) (τ : Hom Θ Δ)
    (A : Ty Γ)
  : ty_sub τ (ty_sub σ A) ≈S ty_sub (σ ∘ τ) A
  := (symmetry (functor_comp (C^op) FamCat T τ σ)).1 A.

(** Equal context substitutions give equal substituted types. *)

(** 相等的上下文替换给出相等的替换类型。 *)

Definition ty_sub_equiv {Γ Δ : @Ob C} {σ σ' : Hom Δ Γ} (H : σ ≈ σ')
    (A : Ty Γ)
  : ty_sub σ A ≈S ty_sub σ' A
  := (@functor_fmap_proper (C^op) FamCat T Γ Δ σ σ' H).1 A.

(** Combine composition and base equality into the required type comparison. *)

(** 将复合与基底相等组合为所需类型比较。 *)

Definition ty_sub_comm {Γ Δ Θ : @Ob C} (A : Ty Γ)
    (σ : Hom Δ Γ) (τ : Hom Θ Δ) {ρ : Hom Θ Γ} (H : σ ∘ τ ≈ ρ)
  : ty_sub τ (ty_sub σ A) ≈S ty_sub ρ A
  := transitivity (ty_sub_comp σ τ A) (ty_sub_equiv H A).

(** Compatibility with identities for [tm_conv]. *)

(** [tm_conv] 与恒等的相容性。 *)

Theorem tm_conv_id {Γ : @Ob C} {A : Ty Γ} (e : A ≈S A) (t : Tm Γ A)
  : tm_conv e t ≈S t.
Proof. apply transpS_id. Qed.

(** Compatibility with composition for [tm_conv]. *)

(** [tm_conv] 与复合的相容性。 *)

Theorem tm_conv_comp {Γ : @Ob C} {A B D : Ty Γ}
    (e : A ≈S B) (d : B ≈S D) (r : A ≈S D) (t : Tm Γ A)
  : tm_conv r t ≈S tm_conv d (tm_conv e t).
Proof. apply transpS_comp. Qed.

(** Changing equality witnesses leaves the resulting action equal. *)

(** 改变相等见证后，所得作用仍然相等。 *)

Theorem tm_conv_witness_independent {Γ : @Ob C} {A B : Ty Γ}
    (e d : A ≈S B)
  : tm_conv e ≈f tm_conv d.
Proof. apply transpS_witness_independent. Qed.

(** Type conversion reflects term equality because transport is invertible. *)

(** 运输可逆，因而类型转换反映项相等。 *)

Theorem tm_conv_inj {Γ : @Ob C} {A B : Ty Γ} (e : A ≈S B) (t u : Tm Γ A)
  : tm_conv e t ≈S tm_conv e u → t ≈S u.
Proof.
  intros H. pose (d := symmetry e).
  transitivity (tm_conv d (tm_conv e t)).
  - symmetry. apply transpS_inv.
  - transitivity (tm_conv d (tm_conv e u)).
    + apply func_proper. exact H.
    + apply transpS_inv.
Qed.

(** Term substitution commutes with conversion along type equality. *)

(** 项替换与沿类型相等的转换交换。 *)

Theorem tm_sub_conv {Γ Δ : @Ob C} (σ : Hom Δ Γ)
    {A B : Ty Γ} (e : A ≈S B) (t : Tm Γ A)
  : tm_sub σ (tm_conv e t) ≈S
    tm_conv (ty_eq_sub σ e) (tm_sub σ t).
Proof. exact (famF_naturality (fmap T σ) e t). Qed.

(** Compatibility with identities for [tm_sub]. *)

(** [tm_sub] 与恒等的相容性。 *)

Theorem tm_sub_id {Γ : @Ob C} {A : Ty Γ} (t : Tm Γ A)
  : tm_conv (ty_sub_id A) (tm_sub id t) ≈S t.
Proof. exact ((functor_id (C^op) FamCat T).2 A t). Qed.

(** Compatibility with composition for [tm_sub]. *)

(** [tm_sub] 与复合的相容性。 *)

Theorem tm_sub_comp {Γ Δ Θ : @Ob C} (σ : Hom Δ Γ) (τ : Hom Θ Δ)
    {A : Ty Γ} (t : Tm Γ A)
  : tm_conv (ty_sub_comp σ τ A) (tm_sub τ (tm_sub σ t)) ≈S tm_sub (σ ∘ τ) t.
Proof. exact ((symmetry (functor_comp (C^op) FamCat T τ σ)).2 A t). Qed.

(** Equal substitutions act equally after converting their term types. *)

(** 相等替换在对齐项类型后作用相等。 *)

Theorem tm_sub_equiv {Γ Δ : @Ob C} {σ σ' : Hom Δ Γ} (H : σ ≈ σ')
    {A : Ty Γ} (t : Tm Γ A)
  : tm_conv (ty_sub_equiv H A) (tm_sub σ t) ≈S tm_sub σ' t.
Proof. exact ((@functor_fmap_proper (C^op) FamCat T Γ Δ σ σ' H).2 A t). Qed.

End TypesAndTerms.

(** The presheaf is explicit in the notation: its object map need not
    determine it uniquely, and candidate properties do not require a CwF. *)

(** 记号显式包含预层：对象映射未必唯一确定预层，候选性质也不要求完整的带族范畴。 *)

Notation "A '[' σ ']Ty[' T ']'" := (ty_sub T σ A)
  (at level 8, left associativity, format "A [ σ ]Ty[ T ]") : cat_scope.
Notation "t '[' σ ']Tm[' T ']'" := (tm_sub T σ t)
  (at level 8, left associativity, format "t [ σ ]Tm[ T ]") : cat_scope.
Notation "e '[' σ ']Eq[' T ']'" := (ty_eq_sub T σ e)
  (at level 8, left associativity, format "e [ σ ]Eq[ T ]") : cat_scope.
Notation "e '▸[' T ']' t" := (tm_conv T e t)
  (at level 40, left associativity, format "e  ▸[ T ]  t") : cat_scope.

(** ** Candidate Context Extensions

    A pairing equation retains the base equality witness. Its second law
    compares terms after composition and base-equality conversion. *)

(** ** 候选上下文扩张

    配对方程保留基底相等见证；第二条定律在复合与基底相等转换后比较项。 *)

Section ContextExtension.
Context {C : Cat} (T : Fct (C^op) FamCat).

(** A candidate pairing satisfies projection and converted-variable equations. *)

(** 候选配对满足投影方程及转换后的泛变量方程。 *)

Definition is_context_pair {Γ E Δ : @Ob C} (A : Ty T Γ) (p : Hom E Γ)
    (q : Tm T E A[p]Ty[T]) (σ : Hom Δ Γ) (t : Tm T Δ A[σ]Ty[T])
    (h : Hom Δ E)
  := ∃ H : p ∘ h ≈ σ, ty_sub_comm T A p h H ▸[T] q[h]Tm[T] ≈S t.

(** Every substitution with a term has a unique pairing into the candidate
    extension. *)

(** 每个带项的替换到候选扩张都有唯一配对。 *)

Definition is_context_extension {Γ : @Ob C} (A : Ty T Γ) (E : @Ob C)
    (p : Hom E Γ) (q : Tm T E A[p]Ty[T])
  := ∀ Δ (σ : Hom Δ Γ) (t : Tm T Δ A[σ]Ty[T]),
    ∃ h : Hom Δ E, is_unique (is_context_pair A p q σ t) h.

(** Choose context extensions, projections, generic terms and their universal
    properties. *)

(** 选择上下文扩张、投影、泛项及其泛性质。 *)

Class HasContextExtension
  :=
  { Ext {Γ : @Ob C} (A : Ty T Γ) : @Ob C
  ; context_proj {Γ : @Ob C} (A : Ty T Γ) : Hom (Ext A) Γ
  ; context_var {Γ : @Ob C} (A : Ty T Γ) : Tm T (Ext A) A[context_proj A]Ty[T]
  ; context_extension_universal {Γ : @Ob C} (A : Ty T Γ)
    : is_context_extension A (Ext A) (context_proj A) (context_var A)
  }.

Context `{HC : !HasContextExtension}.

(** Extract the universal pairing from the chosen extension property. *)

(** 从选定扩张泛性质提取泛配对。 *)

Definition context_pair {Γ Δ : @Ob C} (A : Ty T Γ) (σ : Hom Δ Γ)
    (t : Tm T Δ A[σ]Ty[T])
  : Hom Δ (Ext A)
  := (context_extension_universal A Δ σ t).1.

(** The selected pairing satisfies the full pairing and uniqueness property. *)

(** 选定配对满足完整配对方程及唯一性。 *)

Theorem context_pair_universal {Γ Δ : @Ob C} (A : Ty T Γ) (σ : Hom Δ Γ)
    (t : Tm T Δ A[σ]Ty[T])
  : is_unique (is_context_pair A (context_proj A) (context_var A) σ t)
      (context_pair A σ t).
Proof. exact (context_extension_universal A Δ σ t).2. Defined.

(** Projection after pairing recovers the base substitution. *)

(** 配对后投影恢复基底替换。 *)

Definition context_pair_β1 {Γ Δ : @Ob C} (A : Ty T Γ) (σ : Hom Δ Γ)
    (t : Tm T Δ A[σ]Ty[T])
  : context_proj A ∘ context_pair A σ t ≈ σ
  := (@this _ _ _ _ _ (context_pair_universal A σ t)).1.

(** The generic variable after pairing recovers the supplied term after type
    conversion. *)

(** 泛变量沿配对替换并转换类型后恢复给定项。 *)

Theorem context_pair_β2 {Γ Δ : @Ob C} (A : Ty T Γ) (σ : Hom Δ Γ)
    (t : Tm T Δ A[σ]Ty[T])
  : ty_sub_comm T A (context_proj A) (context_pair A σ t)
      (context_pair_β1 A σ t) ▸[T]
        (context_var A)[context_pair A σ t]Tm[T] ≈S t.
Proof. exact (@this _ _ _ _ _ (context_pair_universal A σ t)).2. Qed.

(** Any map satisfying both pairing equations equals the selected pairing. *)

(** 满足两条配对方程的映射等于选定配对。 *)

Theorem context_pair_unique {Γ Δ : @Ob C} (A : Ty T Γ) (σ : Hom Δ Γ)
    (t : Tm T Δ A[σ]Ty[T]) (h : Hom Δ (Ext A))
  : is_context_pair A (context_proj A) (context_var A) σ t h
    → h ≈ context_pair A σ t.
Proof. exact (@that _ _ _ _ _ (context_pair_universal A σ t) h). Qed.

(** Every map to an extension is reconstructed by its projected substitution
    and variable. *)

(** 指向扩张的映射由其投影替换和泛变量重构。 *)

Theorem context_pair_η {Γ Δ : @Ob C} (A : Ty T Γ) (h : Hom Δ (Ext A))
  : h ≈ context_pair A (context_proj A ∘ h)
      (ty_sub_comp T (context_proj A) h A ▸[T] (context_var A)[h]Tm[T]).
Proof.
  apply context_pair_unique. exists (reflexivity (context_proj A ∘ h)).
  apply tm_conv_witness_independent.
Qed.

(** The variable equation holds for any witness of the base projection
    equation. *)

(** 泛变量方程对基底投影方程的任意见证成立。 *)

Theorem context_pair_β2_witness {Γ Δ : @Ob C} (A : Ty T Γ) (σ : Hom Δ Γ)
    (t : Tm T Δ A[σ]Ty[T]) (H : context_proj A ∘ context_pair A σ t ≈ σ)
  : ty_sub_comm T A (context_proj A) (context_pair A σ t) H ▸[T]
      (context_var A)[context_pair A σ t]Tm[T] ≈S t.
Proof.
  transitivity (ty_sub_comm T A (context_proj A) (context_pair A σ t)
    (context_pair_β1 A σ t) ▸[T] (context_var A)[context_pair A σ t]Tm[T]).
  - apply tm_conv_witness_independent.
  - apply context_pair_β2.
Qed.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance context_pair_proper {Γ Δ : @Ob C} (A : Ty T Γ) (σ : Hom Δ Γ)
  : Proper (carrier_equiv (Tm T Δ A[σ]Ty[T]) ==> HomEq) (context_pair A σ).
Proof.
  intros t u H. apply context_pair_unique. exists (context_pair_β1 A σ t).
  transitivity t; [apply context_pair_β2 | exact H].
Qed.

(** Equivalent substitutions and converted terms induce equal pairing maps. *)

(** 等价替换及转换后相等的项诱导相等配对映射。 *)

Theorem context_pair_equiv {Γ Δ : @Ob C} (A : Ty T Γ) {σ σ' : Hom Δ Γ}
    (H : σ ≈ σ') (t : Tm T Δ A[σ]Ty[T]) (u : Tm T Δ A[σ']Ty[T])
  : ty_sub_equiv T H A ▸[T] t ≈S u → context_pair A σ t ≈ context_pair A σ' u.
Proof.
  intros Htu. apply context_pair_unique.
  exists (transitivity (context_pair_β1 A σ t) H).
  transitivity (ty_sub_equiv T H A ▸[T] t).
  - transitivity (ty_sub_equiv T H A ▸[T]
      (ty_sub_comm T A (context_proj A) (context_pair A σ t)
        (context_pair_β1 A σ t) ▸[T] (context_var A)[context_pair A σ t]Tm[T])).
    + apply tm_conv_comp.
    + apply func_proper. apply context_pair_β2.
  - exact Htu.
Qed.

End ContextExtension.

Notation "Γ '▹[' T ']' A" := (Ext T (Γ := Γ) A)
  (at level 40, left associativity, format "Γ  ▹[ T ]  A") : cat_scope.
Notation "'⟨' σ ';' t '⟩[' T ',' A ']'" := (context_pair T A σ t)
  (at level 0, format "⟨ σ ;  t ⟩[ T ,  A ]") : cat_scope.

(** Like [CCC] and [ETCS], an enabled bundle supplies its substructures.
    Concrete CwF models still have to be enabled explicitly. Coercion exposes
    the type-and-term functor without selecting a model. *)

(** 与 [CCC]、[ETCS] 一样，启用组合结构后可使用其子结构；具体带族范畴模型仍须
    显式启用。强制转换暴露类型与项函子，不会自动选取模型。 *)

Class CwF (C : Cat)
  :=
  { hasTerminal :: HasTerminal C
  ; TyTmF :> Fct (C^op) FamCat
  ; hasContextExtension :: HasContextExtension TyTmF
  }.

Arguments TyTmF {_} _.
