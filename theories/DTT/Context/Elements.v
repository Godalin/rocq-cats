From Cats Require Import
  Cat.Core
  Cat.Arrow.Core
  Cat.Functor.Core
  Cat.Isomorphism
  Cat.Natural
  Cat.Fibration
  Cat.Comprehension
  Cat.Section
  Cat.Terminal
  Instance.Set.Core
  Instance.Set.Elements
  Instance.Set.Fam.Core
  Instance.Set.Fam.Cat
  DTT.CwF
  DTT.Comprehension
  DTT.Context.Conversion
  DTT.Context.Pullback
  DTT.Context.Display
  DTT.Context.Section
  DTT.Display.Core
  DTT.Display.Section
  DTT.Display.Comprehension
  DTT.Display.Interpretation.

(** * Context Extensions Interpret Their Type Elements

    Fix a family-valued presheaf with chosen context extensions. Its existing
    coherent display action interprets type elements as commuting context
    squares. Reuse the display pullbacks to prove cartesian preservation,
    then apply the conditional interpretation theorem. No terminal context
    is needed until the final CwF is assembled. *)

(** * 上下文扩张解释自身的类型元素

    固定带选定上下文扩张的族值预层。既有相干显示作用将类型元素解释为交换的
    上下文方形；复用显示拉回证明笛卡尔保持，再应用带条件的解释定理。
    仅在最后组装 CwF 时需要终上下文。 *)

Section ContextElements.
Context {C : Cat} (T : Fct (C^op) FamCat)
    `{HC : !HasContextExtension T}.
Let P := FamBaseF ∘F T.
Let HD := @ContextExtension_HasDisplay C T HC.
Local Existing Instance HD.

(** Interpret the designated element witness through the existing display
    action. Equality compares the base and extension maps, not law fields. *)

(** 通过既有显示作用解释指定元素见证；相等比较基底与扩张映射，不比较律字段。 *)

Program Definition ContextElementsF
  : Fct (ElementsCat P) (ContextTypeCat T)
  :=
  {|fobj X := X
  ; fmap X Y f :=
      MakeContextMap T X Y
        {|arrow_bottom := element_map_base P f
        ; arrow_top := display_element_map P f
        ; arrow_comm := display_element_map_proj P f
        |}
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation.
  intros f g H. split; [exact H |].
  exact (display_element_map_proper P f g H).
Qed.
Next Obligation.
  split; [reflexivity | exact (@display_element_map_id C P HD X)].
Qed.
Next Obligation.
  split; [reflexivity | exact (@display_element_map_comp C P HD X Y Z f g)].
Qed.

(** The interpreted base is compared with the element projection by
    identity components, without equating functor records. *)

(** 解释后的基底通过恒等分量与元素投影比较，不令函子记录相等。 *)

Program Definition ContextElementsBaseN
  : (CwFBaseF T ∘F ContextElementsF) ⇒ ElementsBaseF P
  := {|nt X := id|}.
Next Obligation. rewrite comp_id_l, comp_id_r. reflexivity. Defined.

(** The base comparison has transparent identity inverse data. *)

(** 基底比较具有透明的恒等逆数据。 *)

Definition context_elements_base_iso
  : (CwFBaseF T ∘F ContextElementsF) ≅N ElementsBaseF P.
Proof.
  exists ContextElementsBaseN. intros X.
  exists id. split; apply comp_id_l.
Defined.

(** Every interpreted element map is cartesian by its existing display
    pullback. No global pullback or source-lift choice is introduced. *)

(** 每条解释后的元素映射由既有显示拉回给出笛卡尔性，不引入全局拉回或源提升选择。 *)

Definition context_elements_cartesian {X Y : PshElement P}
    (f : ElementMap P X Y)
  : (fmap ContextElementsF f) ⦂ Cart(CwFBaseF T).
Proof.
  apply context_map_pullback_cartesian.
  exact (display_elements_comprehension_universal P X Y f
    (element_map_cartesian P f)).
Defined.

(** Restrict the supplied context comprehension to its interpreted type
    elements using the already accepted conditional construction. *)

(** 使用已有带条件构造，将给定上下文理解结构限制到其解释后的类型元素。 *)

Definition ContextElementsComprehension
  : Comprehension (ElementsBaseF P)
  := InterpretedElementsComprehension P ContextElementsF
    context_elements_base_iso (CwFProjectionN T)
    (cwf_comprehension_universal T)
    (λ X Y f, context_elements_cartesian f).

(** Displays recovered through the context interpretation, with no model
    instance registration. *)

(** 经上下文解释恢复显示结构，不注册模型实例。 *)

Definition ContextElements_HasDisplay
  : HasDisplay C P
  := Comprehension_HasDisplay P ContextElementsComprehension.

(** The terminal-context choice is independent of the interpretation. *)

(** 终上下文选择独立于解释。 *)

Definition ContextElementsCwF `{HT : !HasTerminal C}
  : CwF C
  := @ComprehensionCwF C P ContextElementsComprehension HT.

(** The recovered projection agrees with the original context projection
    in the specified hom equality. *)

(** 恢复投影在指定 Hom 相等下与原上下文投影一致。 *)

Theorem context_elements_proj {Γ : @Ob C} (A : Ty T Γ)
  : @display_proj C P ContextElements_HasDisplay Γ A
      ≈ context_proj T A.
Proof. apply comp_id_l. Defined.

(** Recovery retains the original conversion action up to hom equality. *)

(** 恢复在 Hom 相等下保留原转换作用。 *)

Theorem context_elements_conv {Γ : @Ob C} {A B : Ty T Γ}
    (e : A ≈S B)
  : @display_conv C P ContextElements_HasDisplay Γ A B e ≈ e^Ext[T].
Proof. exact (@display_elements_conv C P HD Γ A B e). Defined.

(** Recovery retains the original chosen substitution lift up to hom
    equality; its proof and lift records need not be natively equal. *)

(** 恢复在 Hom 相等下保留原选定替换提升，不要求证明或提升记录原生相等。 *)

Theorem context_elements_lift {Γ Δ : @Ob C} (σ : Hom Δ Γ) (A : Ty T Γ)
  : @display_lift C P ContextElements_HasDisplay Γ Δ σ A ≈ σ^+[T, A].
Proof. exact (@display_elements_lift C P HD Γ Δ σ A). Defined.

(** The recovered total-space functor is naturally isomorphic to the
    interpreted extension functor, with transparent inverse components. *)

(** 恢复的全空间函子自然同构于解释后的扩张函子，逆分量保持透明。 *)

Definition context_elements_display_iso
  : @DisplayElementsF C P ContextElements_HasDisplay ≅N
      (CwFExtF T ∘F ContextElementsF)
  := comprehension_display_iso P ContextElementsComprehension.

(** Retain the section map and transport only its right-inverse witness
    across the recovered projection equality. *)

(** 保留截面映射，仅沿恢复投影相等运输其右逆见证。 *)

Program Definition context_elements_section_resp {Γ : @Ob C}
    (A : Ty T Γ)
  : @DisplayTerms C P ContextElements_HasDisplay Γ A →r
      Sec(context_proj T A)
  := {|func s := (s.1; _)|}.
Next Obligation.
  transitivity (@display_proj C P ContextElements_HasDisplay Γ A ∘ s.1).
  - apply comp_r. symmetry. apply context_elements_proj.
  - exact s.2.
Defined.
Next Obligation. intros s t H. exact H. Defined.

(** Send an original term to its section of the recovered projection.
    The section map is the existing transparent term-to-section map. *)

(** 将原项送到恢复投影的截面；其截面映射使用已有透明的项到截面映射。 *)

Program Definition context_elements_term_resp {Γ : @Ob C} (A : Ty T Γ)
  : Tm T Γ A →r @DisplayTerms C P ContextElements_HasDisplay Γ A
  := {|func t := ((term_to_section_resp T A t).1; _)|}.
Next Obligation.
  transitivity (context_proj T A ∘ (term_to_section_resp T A t).1).
  - apply comp_r. apply context_elements_proj.
  - exact (term_to_section_resp T A t).2.
Defined.
Next Obligation.
  intros t u H. exact (@func_proper _ _ (term_to_section_resp T A) t u H).
Defined.

(** Recover an original term from a recovered section, using the existing
    section-to-term map after the projection boundary. *)

(** 跨投影边界后使用已有截面到项映射，从恢复截面得到原项。 *)

Definition context_elements_term_inv_resp {Γ : @Ob C} (A : Ty T Γ)
  : @DisplayTerms C P ContextElements_HasDisplay Γ A →r Tm T Γ A
  := section_to_term_resp T A ∘r context_elements_section_resp A.

(** The backward map recovers the original term in its specified equality,
    with no common carrier or equality bound for the two term setoids. *)

(** 逆映射在原项的指定相等下恢复原项，不要求两个项广集共享载体或相等大小界。 *)

Theorem context_elements_term_β {Γ : @Ob C} (A : Ty T Γ) (t : Tm T Γ A)
  : context_elements_term_inv_resp A (context_elements_term_resp A t) ≈S t.
Proof.
  transitivity (section_to_term_resp T A (term_to_section_resp T A t)).
  - exact (@func_proper (Sec(context_proj T A)) (Tm T Γ A)
      (section_to_term_resp T A)
      (context_elements_section_resp A (context_elements_term_resp A t))
      (term_to_section_resp T A t)
      (reflexivity (term_to_section_resp T A t).1)).
  - apply term_section_β.
Defined.

(** The forward map recovers a section up to equality of its underlying
    map, without identifying its right-inverse witness. *)

(** 前向映射在底层映射相等下恢复截面，不识别其右逆见证。 *)

Theorem context_elements_term_η {Γ : @Ob C} (A : Ty T Γ)
    (s : @DisplayTerms C P ContextElements_HasDisplay Γ A)
  : context_elements_term_resp A (context_elements_term_inv_resp A s) ≈S s.
Proof. exact (term_section_η T A (context_elements_section_resp A s)). Defined.

(** Lift both carriers and equality witnesses to independent common bounds
    before packaging the fiber isomorphism in one SetCat. The unlifted maps
    and inverse laws above retain their distinct sizes. *)

(** 在打包到同一个 SetCat 前，独立提升两侧载体与相等见证至共同上界。
    上方未提升的映射及互逆律仍保留不同大小。 *)

Definition context_elements_term_iso@{s q +} {Γ : @Ob C} (A : Ty T Γ)
  : LiftS@{_ _ s q} (Tm T Γ A) ≅[SetCat]
      LiftS@{_ _ s q} (@DisplayTerms C P ContextElements_HasDisplay Γ A).
Proof.
  exists ((context_elements_term_resp A)^↑S),
    ((context_elements_term_inv_resp A)^↑S).
  split.
  - intros [t]. exact {|lower := context_elements_term_β A t|}.
  - intros [t]. exact {|lower := context_elements_term_η A t|}.
Defined.

(** The forward fiber comparison also commutes with designated type
    conversion; coherent transport compares the composite witnesses. *)

(** 前向纤维比较也与指定类型转换交换，由相干运输比较复合见证。 *)

Theorem context_elements_term_conv {Γ : @Ob C} {A B : Ty T Γ}
    (e : A ≈S B) (t : Tm T Γ A)
  : context_elements_term_resp B (e ▸[T] t) ≈S
      @display_term_conv_resp C P ContextElements_HasDisplay Γ A B e
        (context_elements_term_resp A t).
Proof.
  change ((term_to_section_resp T B (e ▸[T] t)).1 ≈
    @display_conv C P ContextElements_HasDisplay Γ A B e ∘
      (term_to_section_resp T A t).1).
  rewrite context_elements_conv. symmetry.
  transitivity ⟨id; e[id]Eq[T] ▸[T]
    (symmetry (ty_sub_id T A) ▸[T] t)⟩[T, B].
  - apply context_conv_pair.
  - apply context_pair_proper.
    transitivity (transitivity (symmetry (ty_sub_id T A)) e[id]Eq[T]
      ▸[T] t).
    + symmetry. apply tm_conv_comp.
    + apply tm_conv_comp.
Defined.

(** The forward fiber comparison commutes with substitution in the
    recovered section equality, by the existing section pullback uniqueness. *)

(** 前向纤维比较由已有截面拉回唯一性，在恢复截面相等下与替换交换。 *)

Theorem context_elements_term_sub {Γ Δ : @Ob C} (σ : Hom Δ Γ)
    (A : Ty T Γ) (t : Tm T Γ A)
  : context_elements_term_resp A[σ]Ty[T] t[σ]Tm[T] ≈S
      @display_term_sub_resp C P ContextElements_HasDisplay Γ Δ σ A
        (context_elements_term_resp A t).
Proof.
  apply (section_of_pullback_unique
    (@display_lift_universal C P ContextElements_HasDisplay Γ Δ σ A)).
  change (@display_lift C P ContextElements_HasDisplay Γ Δ σ A ∘
    (term_to_section_resp T A[σ]Ty[T] t[σ]Tm[T]).1 ≈
    (term_to_section_resp T A t).1 ∘ σ).
  rewrite context_elements_lift. apply term_section_sub.
Defined.

End ContextElements.

(** ** Inverse Coherence of the Fiber Comparison

    Keep the supplied family-valued presheaf and chosen extensions fixed.
    Apply the general inverse-square theorem to independently lifted fibers,
    then recover pointwise conversion and substitution laws by lowering the
    resulting equality witness. No terminal context is required. *)

(** ** 纤维比较的逆向相干性

    固定给定族值预层和选定扩张，对独立提升的纤维应用一般逆方形定理，
    再解包相等见证，得到逐点的转换及替换律；无需终上下文。 *)

Section ContextElementsInverse.
Context {C : Cat} (T : Fct (C^op) FamCat)
    `{HC : !HasContextExtension T}.
Let P := FamBaseF ∘F T.
Let HD := @ContextElements_HasDisplay C T HC.

(** Invert any square commuting with the forward fiber comparison.
    Lifting supplies common bounds only inside the proof; the unlifted
    maps and the resulting equality retain their independent sizes. *)

(** 对与前向纤维比较交换的任意方形取逆。提升仅在证明内部提供共同大小界，
    原映射和所得相等仍保留独立大小。 *)

Theorem context_elements_term_square_inv {Γ Δ : @Ob C}
    (A : Ty T Γ) (B : Ty T Δ)
    (f : Tm T Γ A →r Tm T Δ B)
    (g : @DisplayTerms C P HD Γ A →r @DisplayTerms C P HD Δ B)
    (H : ∀ t, context_elements_term_resp T B (f t)
      ≈S g (context_elements_term_resp T A t))
    (s : @DisplayTerms C P HD Γ A)
  : context_elements_term_inv_resp T B (g s)
      ≈S f (context_elements_term_inv_resp T A s).
Proof.
  pose (i := context_elements_term_iso T A).
  pose (j := context_elements_term_iso T B).
  assert (Hlift : (j.1 ∘r f^↑S) ≈f (g^↑S ∘r i.1)).
  { intros [t]. exact {|lower := H t|}. }
  exact (lower (@iso_square_inv SetCat _ _ _ _ i j (f^↑S) (g^↑S) Hlift
    {|lower := s|})).
Defined.

(** The backward comparison commutes with designated type conversion. *)

(** 逆向比较与指定类型转换交换。 *)

Theorem context_elements_term_inv_conv {Γ : @Ob C} {A B : Ty T Γ}
    (e : A ≈S B) (s : @DisplayTerms C P HD Γ A)
  : context_elements_term_inv_resp T B
      (@display_term_conv_resp C P HD Γ A B e s)
      ≈S e ▸[T] context_elements_term_inv_resp T A s.
Proof.
  apply (context_elements_term_square_inv A B (tm_conv T e)
    (@display_term_conv_resp C P HD Γ A B e)).
  intros t. apply context_elements_term_conv.
Defined.

(** The backward comparison commutes with substitution, using only the
    accepted forward square and its pointwise inverse laws. *)

(** 逆向比较与替换交换，仅使用已接收的正向方形及逐点互逆律。 *)

Theorem context_elements_term_inv_sub {Γ Δ : @Ob C} (σ : Hom Δ Γ)
    (A : Ty T Γ) (s : @DisplayTerms C P HD Γ A)
  : context_elements_term_inv_resp T A[σ]Ty[T]
      (@display_term_sub_resp C P HD Γ Δ σ A s)
      ≈S (context_elements_term_inv_resp T A s)[σ]Tm[T].
Proof.
  apply (context_elements_term_square_inv A A[σ]Ty[T] (tm_sub T σ)
    (@display_term_sub_resp C P HD Γ Δ σ A)).
  intros t. apply context_elements_term_sub.
Defined.

End ContextElementsInverse.

From Cats Require Import
  DTT.Context.Extension
  DTT.Display.Representation.

(** ** Canonical Pairing and Generic Terms

    Keep the supplied context extensions and their interpreted displays.
    Reuse the general section/pairing bridge for both term comparisons.
    Generic terms are compared after aligning the actual recovered context
    projection with the original projection. No terminal context is used. *)

(** ** 规范配对与泛项

    固定给定上下文扩张及其解释后的显示结构，复用一般截面／配对桥梁，
    比较两个方向的项映射。先对齐实际恢复的上下文投影与原投影，再比较泛项；
    无需终上下文。 *)

Section ContextElementsPairing.
Context {C : Cat} (T : Fct (C^op) FamCat)
    `{HC : !HasContextExtension T}.
Let P := FamBaseF ∘F T.
Let HD := @ContextElements_HasDisplay C T HC.
Let R := @DisplayTyTmF C P HD.
Let HR := @Display_HasContextExtension C P HD.

(** The context projection recovered from the interpreted display has
    the original boundary in hom equality, retaining the chosen witness. *)

(** 从解释后的显示恢复的上下文投影，在 Hom 相等下具有原边界，并保留选定见证。 *)

Theorem context_elements_context_proj {Γ : @Ob C} (A : Ty T Γ)
  : @context_proj C R HR Γ A ≈ context_proj T A.
Proof.
  transitivity (@display_proj C P HD Γ A).
  - apply display_context_proj.
  - apply context_elements_proj.
Defined.

(** Pairing the forward image of any substituted-type term gives the
    original pairing map. The term need not be a substitution image. *)

(** 对任意替换类型中项的前向像配对，得到原配对映射；该项不必是替换像。 *)

Theorem context_elements_pair {Γ Δ : @Ob C} (A : Ty T Γ)
    (σ : Hom Δ Γ) (t : Tm T Δ A[σ]Ty[T])
  : @context_pair C R HR Γ Δ A σ
      (context_elements_term_resp T A[σ]Ty[T] t) ≈ ⟨σ; t⟩[T, A].
Proof.
  transitivity (@display_lift C P HD Γ Δ σ A ∘
    (term_to_section_resp T A[σ]Ty[T] t).1).
  - apply display_context_pair.
  - transitivity (σ^+[T, A] ∘ (term_to_section_resp T A[σ]Ty[T] t).1).
    + apply comp_r. apply context_elements_lift.
    + exact (@context_lift_term_section C T HC Γ Δ σ A t).
Defined.

(** Pairing an arbitrary recovered section agrees with pairing its
    backward term. Only the section's right-inverse witness is retargeted. *)

(** 任意恢复截面的配对等于其逆向项的配对，仅重定向截面的右逆见证。 *)

Theorem context_elements_pair_inv {Γ Δ : @Ob C} (A : Ty T Γ)
    (σ : Hom Δ Γ) (s : @DisplayTerms C P HD Δ A[σ]Ty[T])
  : @context_pair C R HR Γ Δ A σ s ≈
      ⟨σ; context_elements_term_inv_resp T A[σ]Ty[T] s⟩[T, A].
Proof.
  transitivity (@display_lift C P HD Γ Δ σ A ∘ s.1).
  - apply display_context_pair.
  - transitivity (σ^+[T, A] ∘ s.1).
    + apply comp_r. apply context_elements_lift.
    + exact (@context_lift_section_term C T HC Γ Δ σ A
        (context_elements_section_resp T A[σ]Ty[T] s)).
Defined.

(** Align the recovered generic term by any supplied projection equality
    before comparing it with the forward image of the original generic term.
    Pairing injectivity compares values without identifying law witnesses. *)

(** 先沿任意给定投影相等对齐恢复泛项，再与原泛项的前向像比较；
    配对单射性比较值，不识别律见证。 *)

Theorem context_elements_var {Γ : @Ob C} (A : Ty T Γ)
    (H : @context_proj C R HR Γ A ≈ context_proj T A)
  : ty_sub_equiv T H A
      ▸[R] (@context_var C R HR Γ A) ≈S
      context_elements_term_resp T A[context_proj T A]Ty[T]
        (context_var T A).
Proof.
  apply (@context_pair_inj C R HR Γ (Γ ▹[T] A) A (context_proj T A)).
  transitivity (@context_pair C R HR Γ (Γ ▹[T] A) A
    (@context_proj C R HR Γ A) (@context_var C R HR Γ A)).
  - symmetry. apply (@context_pair_equiv C R HR Γ (Γ ▹[T] A) A
      _ _ H).
    apply tm_conv_witness_independent.
  - transitivity (id[Γ ▹[T] A]).
    + exact (@display_pair_unpair C P HD Γ (Γ ▹[T] A) A id).
    + symmetry. transitivity ⟨context_proj T A; context_var T A⟩[T, A].
      * apply context_elements_pair.
      * symmetry. apply (@context_pair_unique C T HC).
        exists (comp_id_r (context_proj T A)).
        transitivity (ty_sub_id T A[context_proj T A]Ty[T]
          ▸[T] (context_var T A)[id]Tm[T]).
        -- apply tm_conv_witness_independent.
        -- apply tm_sub_id.
Defined.

(** The inverse comparison sends the recovered generic term to the
    original after the same explicit projection conversion. *)

(** 逆向比较沿同一显式投影转换，将恢复泛项送回原泛项。 *)

Theorem context_elements_var_inv {Γ : @Ob C} (A : Ty T Γ)
    (H : @context_proj C R HR Γ A ≈ context_proj T A)
  : ty_sub_equiv T H A ▸[T]
      context_elements_term_inv_resp T A[@context_proj C R HR Γ A]Ty[T]
        (@context_var C R HR Γ A) ≈S context_var T A.
Proof.
  transitivity (context_elements_term_inv_resp T A[context_proj T A]Ty[T]
    (ty_sub_equiv T H A
      ▸[R] (@context_var C R HR Γ A))).
  - symmetry. apply context_elements_term_inv_conv.
  - transitivity (context_elements_term_inv_resp T A[context_proj T A]Ty[T]
      (context_elements_term_resp T A[context_proj T A]Ty[T]
        (context_var T A))).
    + apply func_proper. exact (context_elements_var A H).
    + apply context_elements_term_β.
Defined.

End ContextElementsPairing.

(** ** Canonical Context Conversion and Substitution Lifts

    Keep the chosen original extensions and their interpreted displays.
    Compose the general display-to-context comparison with the canonical
    display comparison. Only specified hom equality is asserted; no terminal
    context or equality of chosen structure records is required. *)

(** ** 规范上下文转换与替换提升

    固定选定的原上下文扩张及其解释后的显示结构，将一般显示到上下文比较与
    规范显示比较复合。结论仅为指定 Hom 相等，不需要终上下文或选定结构记录相等。 *)

Section ContextElementsActions.
Context {C : Cat} (T : Fct (C^op) FamCat)
    `{HC : !HasContextExtension T}.
Let P := FamBaseF ∘F T.
Let HD := @ContextElements_HasDisplay C T HC.
Let R := @DisplayTyTmF C P HD.
Let HR := @Display_HasContextExtension C P HD.

(** The actual recovered context conversion retains the original action
    of each supplied Type-valued type-equality witness, up to hom equality. *)

(** 实际恢复的上下文转换，在 Hom 相等下保留每个给定 Type 值类型相等见证的原作用。 *)

Theorem context_elements_context_conv {Γ : @Ob C} {A B : Ty T Γ}
    (e : A ≈S B)
  : @context_conv C R HR Γ A B e ≈ e^Ext[T].
Proof.
  transitivity (@display_conv C P HD Γ A B e).
  - exact (@display_context_conv C P HD Γ A B e).
  - exact (@context_elements_conv C T HC Γ A B e).
Defined.

(** The actual recovered context substitution lift retains the original
    chosen lift, without identifying their pullback-law witnesses. *)

(** 实际恢复的上下文替换提升保留原选定提升，不识别它们的拉回定律见证。 *)

Theorem context_elements_context_lift {Γ Δ : @Ob C} (σ : Hom Δ Γ)
    (A : Ty T Γ)
  : @context_lift C R HR Γ Δ σ A ≈ σ^+[T, A].
Proof.
  transitivity (@display_lift C P HD Γ Δ σ A).
  - exact (@display_context_lift C P HD Γ Δ σ A).
  - exact (@context_elements_lift C T HC Γ Δ σ A).
Defined.

End ContextElementsActions.

(** ** Canonical Pullback Factors

    Keep the chosen context extensions and their canonical recovery.
    Transport a commuting cone across the projection boundary. The existing
    pullback-factor uniqueness then compares the two universal mediators,
    for arbitrary supplied cone witnesses, without a terminal context. *)

(** ** 规范拉回分解

    固定选定上下文扩张及其规范恢复，跨投影边界运输交换锥，再由已有拉回分解
    唯一性比较两个泛中介。锥见证可任意给定，不需要终上下文。 *)

Section ContextElementsFactors.
Context {C : Cat} (T : Fct (C^op) FamCat)
    `{HC : !HasContextExtension T}.
Let P := FamBaseF ∘F T.
Let HD := @ContextElements_HasDisplay C T HC.
Let R := @DisplayTyTmF C P HD.
Let HR := @Display_HasContextExtension C P HD.

(** A cone over the original projection gives a cone over the recovered
    projection in the specified Type-valued hom equality. *)

(** 原投影上的交换锥按指定 Type 值 Hom 相等给出恢复投影上的交换锥。 *)

Definition context_elements_lift_cone {Γ Δ Θ : @Ob C} (σ : Hom Δ Γ)
    (A : Ty T Γ) (u : Hom Θ Δ) (v : Hom Θ (Γ ▹[T] A))
    (H : σ ∘ u ≈ context_proj T A ∘ v)
  : σ ∘ u ≈ @context_proj C R HR Γ A ∘ v.
Proof.
  transitivity (context_proj T A ∘ v).
  - exact H.
  - apply comp_r. symmetry. apply context_elements_context_proj.
Defined.

(** Recovered and original pullback factors agree for any two supplied
    cone witnesses; no equality of these witnesses or chosen laws is used. *)

(** 对任意两份给定锥见证，恢复与原拉回分解一致，不要求锥见证或选定定律相等。 *)

Theorem context_elements_context_factor {Γ Δ Θ : @Ob C}
    (σ : Hom Δ Γ) (A : Ty T Γ) (u : Hom Θ Δ)
    (v : Hom Θ (Γ ▹[T] A))
    (H : σ ∘ u ≈ context_proj T A ∘ v)
    (K : σ ∘ u ≈ @context_proj C R HR Γ A ∘ v)
  : @context_lift_factor C R HR Γ Δ Θ σ A u v K ≈
      @context_lift_factor C T HC Γ Δ Θ σ A u v H.
Proof.
  apply (@context_lift_factor_η C T HC Γ Δ Θ σ A u v H).
  - transitivity (@context_proj C R HR Δ A[σ]Ty[T] ∘
      @context_lift_factor C R HR Γ Δ Θ σ A u v K).
    + apply comp_r. symmetry. apply context_elements_context_proj.
    + exact (@context_lift_factor_β1 C R HR Γ Δ Θ σ A u v K).
  - transitivity (@context_lift C R HR Γ Δ σ A ∘
      @context_lift_factor C R HR Γ Δ Θ σ A u v K).
    + apply comp_r. symmetry. apply context_elements_context_lift.
    + exact (@context_lift_factor_β2 C R HR Γ Δ Θ σ A u v K).
Defined.

End ContextElementsFactors.
