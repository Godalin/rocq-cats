From Cats Require Import
  Cat.Core
  Cat.Functor.Core
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
  {|F0 X := X
  ; F1 X Y f :=
      {|context_map_base := element_map_base P f
      ; context_map_ext := display_element_map P f
      ; context_map_comm := display_element_map_proj P f
      |}
  |}.
Next Obligation.
  intros f g H. split; [exact H |].
  exact (display_element_map_proper P f g H).
Defined.
Next Obligation.
  split; [reflexivity | exact (@display_element_map_id C P HD X)].
Defined.
Next Obligation.
  split; [reflexivity | exact (@display_element_map_comp C P HD X Y Z f g)].
Defined.

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
  : fmap ContextElementsF f ⦂ Cart(CwFBaseF T).
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
