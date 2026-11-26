From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Pullback
  Cat.Section
  Cat.Terminal
  DTT.CwF
  DTT.Display.Core
  DTT.Display.Section
  DTT.Context.Extension
  DTT.Context.Representation.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Hom
  Instance.Set.Fam.Core
  Instance.Set.Representable.

(** * Display Objects Represent Substitution-Term Pairs

    Fix a type presheaf [P] on [C] with [HasDisplay C P]. Coherent display
    maps supply terms as sections. Their chosen pullbacks
    yield universal substitution-term pairs. The general universal-element
    criterion recovers context extensions; lifted Hom gives the representation.
    A terminal context is separate. *)

(** * 显示对象表示替换与项的配对

    固定 [C] 上的类型预层 [P] 及 [HasDisplay C P]。相干显示映射以截面提供项。
    选定拉回给出泛替换与项配对，由一般泛元素准则恢复上下文扩张，提升 Hom
    给出表示；终上下文仍需独立选择。 *)

Section DisplayRepresentation.
Context {C : Cat} (P : Fct (C^op) SetCat) `{HD : !HasDisplay C P}.

(** A substitution and its section determine an arrow to the display object. *)

(** 替换及其截面确定指向显示对象的箭头。 *)

Program Definition display_pair_resp {Γ : @Ob C} (A : P Γ) (Δ : @Ob C)
  : ContextPairS (DisplayTyTmF P) A Δ →r HomSet Δ (Γ ▹D[P] A)
  :=
  {|func x := x.1^D[P, A] ∘ x.2.1
  |}.
Next Obligation.
  intros [σ s] [τ t] [H Hs].
  change (σ^D[P, A] ∘ s.1 ≈ τ^D[P, A] ∘ t.1).
  rewrite (display_lift_equiv H A), comp_assoc.
  apply comp_l. exact Hs.
Defined.

(** The resulting arrow lies over the supplied substitution. *)

(** 所得箭头位于给定替换之上。 *)

Theorem display_pair_proj {Γ Δ : @Ob C} (A : P Γ)
    (x : ContextPairS (DisplayTyTmF P) A Δ)
  : display_proj P A ∘ display_pair_resp A Δ x ≈ x.1.
Proof.
  destruct x as [σ s].
  change (display_proj P A ∘ (σ^D[P, A] ∘ s.1) ≈ σ).
  rewrite <- comp_assoc, display_lift_proj, comp_assoc, s.2.
  apply comp_id_r.
Defined.

(** Factor an arrow through its display pullback to recover a section. *)

(** 通过显示拉回分解箭头，恢复截面。 *)

Definition display_unpair {Γ Δ : @Ob C} (A : P Γ)
    (h : Hom Δ (Γ ▹D[P] A))
  : ContextPairS (DisplayTyTmF P) A Δ
  := (display_proj P A ∘ h;
      section_of_pullback_factor
        (display_lift_universal (display_proj P A ∘ h) A)
        h (comp_id_r (display_proj P A ∘ h))).

(** Pairing after factorization recovers the original arrow. *)

(** 分解后再配对，恢复原箭头。 *)

Definition display_pair_unpair {Γ Δ : @Ob C} (A : P Γ)
    (h : Hom Δ (Γ ▹D[P] A))
  : display_pair_resp A Δ (display_unpair A h) ≈ h
  := section_of_pullback_factor_β _ _ _.

(** Pairing detects equality of pairs, including the converted section. *)

(** 配对检测配对数据的相等，包括经转换的截面。 *)

Theorem display_pair_injective {Γ Δ : @Ob C} (A : P Γ)
    (x y : ContextPairS (DisplayTyTmF P) A Δ)
    (H : display_pair_resp A Δ x ≈ display_pair_resp A Δ y)
  : x ≈S y.
Proof.
  destruct x as [σ s], y as [τ t].
  pose (K := transitivity (symmetry (display_pair_proj A (σ; s)))
    (transitivity (comp_l (display_proj P A) H)
      (display_pair_proj A (τ; t)))).
  exists K. change (type_sub_equiv P K A ▸D[P] s ≈S t).
  apply (pullback_hom_ext (display_lift_universal τ A)).
  - transitivity (id[Δ]).
    + exact (type_sub_equiv P K A ▸D[P] s).2.
    + symmetry. exact t.2.
  - change (τ^D[P, A] ∘ ((type_sub_equiv P K A)^D[P] ∘ s.1)
      ≈ τ^D[P, A] ∘ t.1).
    rewrite <- comp_assoc, <- display_lift_equiv. exact H.
Defined.

(** Factorization after pairing recovers the section after base conversion. *)

(** 配对后再分解，在基底转换后恢复截面。 *)

Theorem display_unpair_pair {Γ Δ : @Ob C} (A : P Γ)
    (x : ContextPairS (DisplayTyTmF P) A Δ)
  : display_unpair A (display_pair_resp A Δ x) ≈S x.
Proof. apply display_pair_injective. apply display_pair_unpair. Defined.

(** The factorization respects arrows without comparing cone witnesses. *)

(** 分解保持箭头相等，不比较锥见证。 *)

Program Definition display_unpair_resp {Γ : @Ob C} (A : P Γ) (Δ : @Ob C)
  : HomSet Δ (Γ ▹D[P] A) →r ContextPairS (DisplayTyTmF P) A Δ
  :=
  {|func := display_unpair A
  |}.
Next Obligation.
  intros h k H. apply display_pair_injective.
  rewrite !display_pair_unpair. exact H.
Defined.

(** Pairing commutes with substitution of a substitution-term pair. *)

(** 配对与替换、项配对的替换交换。 *)

Theorem display_pair_sub {Γ Δ Θ : @Ob C} (A : P Γ)
    (x : ContextPairS (DisplayTyTmF P) A Δ) (τ : Hom Θ Δ)
  : display_pair_resp A Θ x[τ]Pair[DisplayTyTmF P, A]
      ≈ display_pair_resp A Δ x ∘ τ.
Proof.
  destruct x as [σ s].
  change ((σ ∘ τ)^D[P, A] ∘
    ((ty_sub_comp (DisplayTyTmF P) σ τ A)^D[P] ∘
    (s[τ]TmD[P]).1) ≈ (σ^D[P, A] ∘ s.1) ∘ τ).
  rewrite (display_conv_witness_independent P
    (ty_sub_comp (DisplayTyTmF P) σ τ A) (type_sub_comp P σ τ A)).
  rewrite <- comp_assoc, <- (display_lift_comp σ τ A).
  transitivity (σ^D[P, A] ∘ (τ^D[P, A[σ]TyF[P]] ∘
    (s[τ]TmD[P]).1)).
  - apply comp_assoc.
  - rewrite display_term_sub_β. apply symmetry, comp_assoc.
Defined.

(** Factorization commutes with precomposition and pair substitution. *)

(** 分解与预合成及配对替换交换。 *)

Theorem display_unpair_sub {Γ Δ Θ : @Ob C} (A : P Γ)
    (h : Hom Δ (Γ ▹D[P] A)) (τ : Hom Θ Δ)
  : display_unpair A (h ∘ τ)
      ≈S (display_unpair A h)[τ]Pair[DisplayTyTmF P, A].
Proof.
  apply display_pair_injective.
  rewrite display_pair_unpair, display_pair_sub, display_pair_unpair.
  reflexivity.
Defined.

(** The generic pair is the identity arrow factored through its display
    pullback. Its term is the diagonal section. *)

(** 泛配对由恒等箭头通过显示拉回分解而得，其项为对角截面。 *)

Definition display_generic_pair {Γ : @Ob C} (A : P Γ)
  : ContextPairS (DisplayTyTmF P) A (Γ ▹D[P] A)
  := display_unpair A id.

(** Every factored arrow is substitution of the generic pair. *)

(** 每个分解后的箭头都是泛配对的替换。 *)

Theorem display_unpair_at {Γ Δ : @Ob C} (A : P Γ)
    (h : Hom Δ (Γ ▹D[P] A))
  : display_unpair A h
      ≈S (display_generic_pair A)[h]Pair[DisplayTyTmF P, A].
Proof.
  transitivity (display_unpair A (id ∘ h)).
  - exact (@func_proper _ _ (display_unpair_resp A Δ) _ _
      (symmetry (comp_id_l h))).
  - apply display_unpair_sub.
Defined.

(** The generic pair has a unique mediator for every substitution-term
    pair. The mediator is the transparent display pairing. *)

(** 对每个替换与项配对，泛配对具有唯一中介，即透明的显示配对。 *)

Definition display_pair_universal {Γ : @Ob C} (A : P Γ)
  : (display_generic_pair A) ⦂ Univ(ContextPairF (DisplayTyTmF P) A).
Proof.
  intros Δ x. exists (display_pair_resp A Δ x).
  refine {|this := _
          ; that := _
          |}.
  - transitivity (display_unpair A (display_pair_resp A Δ x)).
    + symmetry. apply display_unpair_at.
    + apply display_unpair_pair.
  - intros h Hh.
    transitivity (display_pair_resp A Δ (display_unpair A h)).
    + exact (symmetry (display_pair_unpair A h)).
    + apply (@func_proper _ _ (display_pair_resp A Δ)).
      transitivity ((display_generic_pair A)[h]Pair[DisplayTyTmF P, A]).
      * apply display_unpair_at.
      * exact Hh.
Defined.

(** Represent the pair presheaf using lifted Hom in the opposite category.
    This reuses the general theory without identifying native hom sizes. *)

(** 使用反范畴中的提升 Hom 表示配对预层，复用一般理论，不合并原生 Hom 大小。 *)

Definition display_representation {Γ : @Ob C} (A : P Γ)
  : (Γ ▹D[P] A) ⦂ Rep↑ ContextPairF (DisplayTyTmF P) A
  := universal_element_lifted_representation
      (ContextPairF (DisplayTyTmF P) A) (display_pair_universal A).

(** Recover context extensions from the generic pairs. The chosen structure
    must be enabled explicitly; import selects no model. *)

(** 从泛配对恢复上下文扩张；选定结构须显式启用，导入不自动选择模型。 *)

Program Definition Display_HasContextExtension
  : HasContextExtension (DisplayTyTmF P)
  :=
  {|Ext Γ := Display P
  ; context_proj Γ A := (display_generic_pair A).1
  ; context_var Γ A := (display_generic_pair A).2
  ; context_extension_universal Γ A :=
      context_extension_of_universal_element (DisplayTyTmF P) A
        (display_generic_pair A) (display_pair_universal A)
  |}.

(** The recovered projection is the supplied display projection. *)

(** 恢复的投影等于给定显示投影。 *)

Theorem display_context_proj {Γ : @Ob C} (A : P Γ)
  : @context_proj C (DisplayTyTmF P) Display_HasContextExtension Γ A
      ≈ display_proj P A.
Proof.
  change (display_proj P A ∘ id ≈ display_proj P A).
  apply comp_id_r.
Defined.

(** The recovered universal mediator retains the original display pairing. *)

(** 恢复的泛中介保留原显示配对。 *)

Theorem display_context_pair {Γ Δ : @Ob C} (A : P Γ)
    (σ : Hom Δ Γ) (s : DisplayTerms P Δ A[σ]TyF[P])
  : @context_pair C (DisplayTyTmF P) Display_HasContextExtension Γ Δ A σ s
      ≈ σ^D[P, A] ∘ s.1.
Proof. reflexivity. Defined.

(** Adding an independently chosen terminal context gives a CwF. *)

(** 加入独立选定的终上下文，得到带族范畴。 *)

Program Definition DisplayCwF `{HT : !HasTerminal C}
  : CwF C
  := MakeCwF C (DisplayTyTmF P) HT Display_HasContextExtension.

End DisplayRepresentation.

From Cats Require Import
  DTT.Context.Conversion
  DTT.Context.Pullback.

(** ** Recovering Display Conversion and Substitution Lifts

    Fix the supplied display structure. The context operations derived from
    its generic pairs agree with its original conversion and lift maps.
    Pairing and display coherence suffice; no terminal context is needed. *)

(** ** 恢复显示转换与替换提升

    固定给定显示结构，由其泛配对导出的上下文操作与原转换、提升映射一致。
    证明仅用配对和显示相干律，不需要终上下文。 *)

Section DisplayContextActions.
Context {C : Cat} (P : Fct (C^op) SetCat) `{HD : !HasDisplay C P}.

Let R := DisplayTyTmF P.
Let HR := Display_HasContextExtension P.

(** Recovered context conversion is the given display conversion, in
    specified hom equality rather than equality of witnesses. *)

(** 恢复的上下文转换按指定态射相等等于给定显示转换，而不比较见证的原生相等。 *)

Theorem display_context_conv {Γ : @Ob C} {A B : P Γ} (e : A ≈S B)
  : @context_conv C R HR Γ A B e ≈ e^D[P].
Proof.
  change ((display_proj P A ∘ id)^D[P, B] ∘
    ((e[display_proj P A ∘ id]EqF[P])^D[P] ∘
      (display_generic_pair P A).2.1) ≈ e^D[P]).
  rewrite <- comp_assoc, display_lift_conv, comp_assoc.
  change (e^D[P] ∘ display_pair_resp P A _
    (display_generic_pair P A) ≈ e^D[P]).
  unfold display_generic_pair.
  rewrite display_pair_unpair. apply comp_id_r.
Defined.

(** Recovered context substitution lifts are the given display lifts.
    The proof uses composition coherence and the generic factorization. *)

(** 恢复的上下文替换提升等于给定显示提升；证明复用复合相干性与泛分解。 *)

Theorem display_context_lift {Γ Δ : @Ob C} (σ : Hom Δ Γ) (A : P Γ)
  : @context_lift C R HR Γ Δ σ A ≈ σ^D[P, A].
Proof.
  change ((σ ∘ (display_proj P A[σ]TyF[P] ∘ id))^D[P, A] ∘
    ((ty_sub_comp R σ (display_proj P A[σ]TyF[P] ∘ id) A)^D[P] ∘
      (display_generic_pair P A[σ]TyF[P]).2.1) ≈ σ^D[P, A]).
  rewrite (display_conv_witness_independent P
    (ty_sub_comp R σ (display_proj P A[σ]TyF[P] ∘ id) A)
    (type_sub_comp P σ (display_proj P A[σ]TyF[P] ∘ id) A)).
  transitivity (((σ ∘ (display_proj P A[σ]TyF[P] ∘ id))^D[P, A] ∘
    (type_sub_comp P σ (display_proj P A[σ]TyF[P] ∘ id) A)^D[P]) ∘
      (display_generic_pair P A[σ]TyF[P]).2.1).
  - apply symmetry, comp_assoc.
  - transitivity ((σ^D[P, A] ∘
        (display_proj P A[σ]TyF[P] ∘ id)^D[P, A[σ]TyF[P]]) ∘
        (display_generic_pair P A[σ]TyF[P]).2.1).
    + apply comp_r. symmetry. apply display_lift_comp.
    + transitivity (σ^D[P, A] ∘
        ((display_proj P A[σ]TyF[P] ∘ id)^D[P, A[σ]TyF[P]] ∘
          (display_generic_pair P A[σ]TyF[P]).2.1)).
      * apply comp_assoc.
      * change (σ^D[P, A] ∘ display_pair_resp P A[σ]TyF[P] _
          (display_generic_pair P A[σ]TyF[P]) ≈ σ^D[P, A]).
        unfold display_generic_pair.
        rewrite display_pair_unpair. apply comp_id_r.
Defined.

End DisplayContextActions.
