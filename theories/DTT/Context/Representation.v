From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Terminal.
From Cats Require Import
  DTT.CwF
  DTT.Context.Extension.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Hom
  Instance.Set.Fam.Core
  Instance.Set.Fam.Cat.
From Cats Require Import Instance.Set.Representable.

(** * Recovering Context Extensions from Representations

    The family-valued presheaf already supplies designated type/term equality
    and coherent substitution. A chosen representation supplies the extension. *)

(** * 从表示恢复上下文扩张

    族值预层已经提供指定类型相等、项相等和相干替换，选定表示提供扩张。 *)

Section ContextRepresentation.
Context {C : Cat} (T : Fct (C^op) FamCat).

(** Equality of substituted generic pairs is equivalent to the two
    context-pairing equations. *)

(** 替换后泛配对的数据相等，等价于两个上下文配对方程。 *)

Theorem context_pair_data_iff {Γ E Δ : @Ob C} (A : Ty T Γ) (p : Hom E Γ)
    (q : Tm T E A[p]Ty[T]) (σ : Hom Δ Γ) (t : Tm T Δ A[σ]Ty[T])
    (h : Hom Δ E)
  : (p; q)[h]Pair[T, A] ≈S ((σ; t) : ContextPairS T A Δ)
    ↔ is_context_pair T A p q σ t h.
Proof.
  split; intros [H Ht]; exists H.
  - transitivity (ty_sub_equiv T H A ▸[T]
      (ty_sub_comp T p h A ▸[T] q[h]Tm[T])).
    + apply tm_conv_comp.
    + exact Ht.
  - change (ty_sub_equiv T H A ▸[T]
      (ty_sub_comp T p h A ▸[T] q[h]Tm[T]) ≈S t).
    transitivity (ty_sub_comm T A p h H ▸[T] q[h]Tm[T]).
    + symmetry. apply tm_conv_comp.
    + exact Ht.
Defined.

(** Evaluate a representation at identity to obtain its generic
    substitution-term pair. *)

(** 在恒等处求值表示，得到泛替换与项的配对。 *)

Definition context_representation_generic {Γ : @Ob C} (A : Ty T Γ) {E : @Ob C}
    (R : E ⦂ Repᵒᵖ ContextPairF T A)
  : ContextPairS T A E
  := representation_op_generic R.

(** Naturality determines every component from the generic pair. *)

(** 自然性使每个分量均由泛配对确定。 *)

Theorem context_representation_at {Γ : @Ob C} (A : Ty T Γ) {E : @Ob C}
    (R : E ⦂ Repᵒᵖ ContextPairF T A) {Δ : @Ob C} (h : Hom Δ E)
  : R.1 Δ h ≈S (context_representation_generic A R)[h]Pair[T, A].
Proof. exact (representation_op_at R h). Defined.

(** A universal substitution-term pair supplies a candidate context extension
    directly, independently of native hom and term carrier sizes. *)

(** 泛替换与项配对直接提供候选上下文扩张，不依赖原生 Hom 与项载体的大小关系。 *)

Definition context_extension_of_universal_element {Γ E : @Ob C}
    (A : Ty T Γ) (u : ContextPairS T A E)
    (Hu : u ⦂ Univ(ContextPairF T A))
  : is_context_extension T A E u.1 u.2.
Proof.
  intros Δ σ t.
  destruct (Hu Δ (σ; t)) as [h Hh].
  exists h. refine {|this := _
                   ; that := _
                   |}.
  - apply (fst (context_pair_data_iff A _ _ σ t h)).
    exact (@this _ _ _ _ _ Hh).
  - intros k Hk.
    apply (@that _ _ _ _ _ Hh).
    exact (snd (context_pair_data_iff A _ _ σ t k) Hk).
Defined.

(** A candidate context extension supplies a universal substitution-term
    pair without choosing extensions for other types. *)

(** 候选上下文扩张提供泛替换与项配对，不需要选择其他类型的扩张。 *)

Definition context_extension_universal_element {Γ E : @Ob C}
    (A : Ty T Γ) (u : ContextPairS T A E)
    (Hu : is_context_extension T A E u.1 u.2)
  : u ⦂ Univ(ContextPairF T A).
Proof.
  intros Δ [σ t]. destruct (Hu Δ σ t) as [h Hh].
  exists h. refine {|this := _
                   ; that := _
                   |}.
  - exact (snd (context_pair_data_iff A u.1 u.2 σ t h)
      (@this _ _ _ _ _ Hh)).
  - intros k Hk. apply (@that _ _ _ _ _ Hh).
    exact (fst (context_pair_data_iff A u.1 u.2 σ t k) Hk).
Defined.

(** The context-extension property is exactly universality of its pair.
    This criterion does not package native hom-sets in a common SetCat. *)

(** 上下文扩张性质恰好是其配对的泛性；此准则不把原生 Hom 广集包装进共同集合范畴。 *)

Theorem context_extension_iff_universal_element {Γ E : @Ob C}
    (A : Ty T Γ) (u : ContextPairS T A E)
  : is_context_extension T A E u.1 u.2
      ↔ u ⦂ Univ(ContextPairF T A).
Proof.
  split.
  - apply context_extension_universal_element.
  - apply context_extension_of_universal_element.
Defined.

(** A candidate extension represents its pair presheaf using lifted Hom in
    the opposite category. Only upward size bounds are required. *)

(** 候选扩张通过反范畴中的提升 Hom 表示配对预层，只需要向上的大小约束。 *)

Definition context_extension_lifted_representation {Γ E : @Ob C}
    (A : Ty T Γ) (u : ContextPairS T A E)
    (Hu : is_context_extension T A E u.1 u.2)
  : E ⦂ Rep↑ ContextPairF T A
  := universal_element_lifted_representation (ContextPairF T A)
      (context_extension_universal_element A u Hu).

(** The universal-element round trip retains the original mediator. *)

(** 泛元素往返保留原中介。 *)

Theorem context_extension_universal_mediator {Γ E Δ : @Ob C}
    (A : Ty T Γ) (u : ContextPairS T A E)
    (Hu : is_context_extension T A E u.1 u.2)
    (σ : Hom Δ Γ) (t : Tm T Δ A[σ]Ty[T])
  : (context_extension_of_universal_element A u
      (context_extension_universal_element A u Hu) Δ σ t).1
      ≈ (Hu Δ σ t).1.
Proof.
  unfold context_extension_of_universal_element,
    context_extension_universal_element.
  destruct (Hu Δ σ t) as [h Hh]. reflexivity.
Defined.

(** A representation supplies its universal pair; reuse the candidate-level
    criterion to recover the extension with the same transparent mediator. *)

(** 表示提供泛配对，复用候选层级准则恢复扩张，并保留同一个透明中介。 *)

Definition context_extension_of_representation {Γ : @Ob C} (A : Ty T Γ)
    {E : @Ob C} (R : E ⦂ Repᵒᵖ ContextPairF T A)
  : is_context_extension T A E (context_representation_generic A R).1
      (context_representation_generic A R).2
  := context_extension_of_universal_element A
      (context_representation_generic A R) (representation_op_universal R).

(** Choose a representing object and natural representation for every context
    type. *)

(** 为每个上下文类型选择表示对象及自然表示。 *)

Class HasContextRepresentation
  :=
  { ContextRep {Γ : @Ob C} (A : Ty T Γ) : @Ob C
  ; context_representation {Γ : @Ob C} (A : Ty T Γ)
    : ContextRep A ⦂ Repᵒᵖ ContextPairF T A
  }.

(** Both conversions are explicit choices, never selected by import. *)

(** 两个转换都是显式选取，导入模块不会自动启用。 *)

Program Definition ContextRepresentation_HasContextExtension
    `{HR : !HasContextRepresentation}
  : HasContextExtension T
  :=
  {|Ext Γ := ContextRep
  ; context_proj Γ A := (context_representation_generic A (context_representation A)).1
  ; context_var Γ A := (context_representation_generic A (context_representation A)).2
  ; context_extension_universal Γ A :=
      context_extension_of_representation A (context_representation A)
  |}.

(** Chosen context extensions give chosen representations of substitution-term
    pairs. *)

(** 选定上下文扩张给出替换与项配对的选定表示。 *)

Program Definition ContextExtension_HasContextRepresentation
    `{HC : !HasContextExtension T}
  : HasContextRepresentation
  :=
  {|ContextRep Γ := Ext T
  ; context_representation Γ := context_extension_nat_iso T
  |}.

(** Choosing context extensions and choosing these representations are
    constructively interconvertible. *)

(** 选取上下文扩张与选取上述表示可构造性地相互转换。 *)

Theorem context_extension_iff_representation
  : HasContextExtension T ↔ HasContextRepresentation.
Proof.
  split.
  - intros HC. exact (@ContextExtension_HasContextRepresentation HC).
  - intros HR. exact (@ContextRepresentation_HasContextExtension HR).
Defined.

(** Combine a terminal object and context-pair representations into a CwF. *)

(** 将终对象与上下文配对表示组合为带族范畴。 *)

Program Definition RepresentedCwF `{HT : !HasTerminal C}
    `{HR : !HasContextRepresentation}
  : CwF C
  :=
  {|hasTerminal := HT
  ; TyTmF := T
  ; hasContextExtension := ContextRepresentation_HasContextExtension
  |}.

(** ** Recovering the Original Context Extension

    Within the fixed presheaf [T], assume chosen context extensions. Pass to
    their representing objects and back, comparing the recovered projection,
    generic term and pairing with the originals. *)

(** ** 恢复原来的上下文扩张

    在固定预层 [T] 下假定选定上下文扩张，先转为表示对象再转回，比较恢复后的投影、泛项和配对与原构造。 *)

Section ExtensionRoundTrip.
Context `{HC : !HasContextExtension T}.
(** The representation structure obtained from the current context extensions. *)

(** 从当前上下文扩张获得的表示结构。 *)

Let HR
  := ContextExtension_HasContextRepresentation.
(** The context-extension structure recovered from those representations. *)

(** 从上述表示恢复的上下文扩张结构。 *)

Let HC'
  := @ContextRepresentation_HasContextExtension HR.

(** The recovered extension projection equals the original projection. *)

(** 恢复的扩张投影等于原投影。 *)

Theorem context_representation_proj_round_trip {Γ : @Ob C} (A : Ty T Γ)
  : @context_proj C T HC' Γ A ≈ @context_proj C T HC Γ A.
Proof. cbn. apply comp_id_r. Defined.

(** The recovered generic term equals the original after aligning projection
    types. *)

(** 恢复的泛项在对齐投影类型后等于原泛项。 *)

Theorem context_representation_var_round_trip {Γ : @Ob C} (A : Ty T Γ)
  : ty_sub_equiv T (context_representation_proj_round_trip A) A
      ▸[T] (@context_var C T HC' Γ A) ≈S @context_var C T HC Γ A.
Proof.
  transitivity (ty_sub_id T A[@context_proj C T HC Γ A]Ty[T]
    ▸[T] (@context_var C T HC Γ A)[id]Tm[T]).
  - symmetry. apply tm_conv_comp.
  - apply tm_sub_id.
Defined.

(** The recovered extension retains the original pairing operation. *)

(** 恢复的扩张保留原配对运算。 *)

Theorem context_representation_pair_round_trip {Γ Δ : @Ob C} (A : Ty T Γ)
    (σ : Hom Δ Γ) (t : Tm T Δ A[σ]Ty[T])
  : @context_pair C T HC' Γ Δ A σ t ≈ @context_pair C T HC Γ Δ A σ t.
Proof. reflexivity. Defined.

End ExtensionRoundTrip.

(** Recovering an extension and its representation preserves the original
    natural map. *)

(** 恢复扩张及其表示后保持原自然映射。 *)

Theorem context_representation_round_trip `{HR : !HasContextRepresentation}
    {Γ : @Ob C} (A : Ty T Γ)
  : @context_extensionN C T ContextRepresentation_HasContextExtension Γ A
      ≈N (context_representation A).1.
Proof. intros Δ h. symmetry. apply context_representation_at. Defined.

End ContextRepresentation.
