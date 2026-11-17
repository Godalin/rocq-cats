From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Fibration
  Cat.Comprehension
  Cat.Pullback
  Cat.Terminal
  Instance.Set.Core
  Instance.Set.Elements
  DTT.CwF
  DTT.Display.Core
  DTT.Display.Representation.

(** * Comprehension over a Type Presheaf's Elements

    A comprehension over [ElementsBaseF P] already has a specified type
    presheaf. Its total-space functor acts on designated type equalities
    and restrictions. Functor laws supply their coherence; cartesianness
    supplies display pullbacks. A terminal context is still separate. *)

(** * 类型预层元素上的理解结构

    [ElementsBaseF P] 上的理解结构已给定类型预层。全空间函子作用于指定类型
    相等及限制，函子律给出其相干性，笛卡尔性提供显示拉回；终上下文仍独立选择。 *)

Section ComprehensionDisplay.
Context {C : Cat} (P : Fct (C^op) SetCat)
    (K : Comprehension (ElementsBaseF P)).

(** Recover displays from this specified comprehension presentation. The
    comprehension's own chosen lifts are not needed: canonical element
    restrictions are already cartesian. Import enables no chosen model. *)

(** 从指定的理解表述恢复显示结构。不需要其自带的选定提升，因为标准元素限制
    已为笛卡尔态射；导入不会启用选定模型。 *)

Program Definition Comprehension_HasDisplay
  : HasDisplay C P
  :=
  {|Display Γ A := (Γ; A)^ext[K]
  ; display_proj Γ A := π[K] (Γ; A)
  ; display_conv Γ A B e := fmap (ExtF K) (element_conv P e)
  ; display_lift Γ Δ σ A := fmap (ExtF K) (element_lift P σ A)
  |}.
Next Obligation.
  transitivity (id ∘ π[K] (Γ; A)).
  - exact (comprehension_comm K (element_conv P e)).
  - apply comp_id_l.
Defined.
Next Obligation.
  transitivity (fmap (ExtF K) (element_map_id P (Γ; A))).
  - apply (@fct_fmap_proper (ElementsCat P) C (ExtF K)).
    change (@id Γ ≈ id). reflexivity.
  - apply fct_id.
Defined.
Next Obligation.
  transitivity (fmap (ExtF K)
    (element_map_comp P (element_conv P d) (element_conv P e))).
  - apply (@fct_fmap_proper (ElementsCat P) C (ExtF K)).
    change (@id Γ ≈ id ∘ id). symmetry. apply comp_id_l.
  - exact (fct_comp (ElementsCat P) C (ExtF K)
      (element_conv P d) (element_conv P e)).
Defined.
Next Obligation.
  exact (comprehension_universal K (element_lift P σ A)
    (element_map_cartesian P (element_lift P σ A))).
Defined.
Next Obligation.
  apply (@fct_fmap_proper (ElementsCat P) C (ExtF K)).
  change (@id Γ ≈ id). reflexivity.
Defined.
Next Obligation.
  rewrite <- !(fct_comp (ElementsCat P) C (ExtF K)).
  apply (@fct_fmap_proper (ElementsCat P) C (ExtF K)).
  change (σ ∘ τ ≈ (σ ∘ τ) ∘ id).
  symmetry. apply comp_id_r.
Defined.
Next Obligation.
  rewrite <- (fct_comp (ElementsCat P) C (ExtF K)).
  apply (@fct_fmap_proper (ElementsCat P) C (ExtF K)).
  change (σ ≈ σ' ∘ id).
  transitivity σ'; [exact H | symmetry; apply comp_id_r].
Defined.
Next Obligation.
  rewrite <- !(fct_comp (ElementsCat P) C (ExtF K)).
  apply (@fct_fmap_proper (ElementsCat P) C (ExtF K)).
  change (σ ∘ id ≈ id ∘ σ).
  transitivity σ; [apply comp_id_r | symmetry; apply comp_id_l].
Defined.

(** Reuse display recovery, adding only the independent terminal choice. *)

(** 复用显示恢复，只增加独立的终上下文选择。 *)

Definition ComprehensionCwF `{HT : !HasTerminal C}
  : CwF C
  := @DisplayCwF C P Comprehension_HasDisplay HT.

End ComprehensionDisplay.

(** ** Comprehension Supplied by Displays

    Conversely, fix coherent displays for [P]. Their equality action and
    restriction lifts extend to all element maps. The resulting functor
    and natural projection provide an actual comprehension input. *)

(** ** 显示结构提供的理解结构

    反向固定 [P] 的相干显示结构。其相等作用与限制提升扩展到全部元素映射，
    所得函子及自然投影给出实际的理解结构输入。 *)

Section DisplayComprehension.
Context {C : Cat} (P : Fct (C^op) SetCat) `{HD : !HasDisplay C P}.

(** An element map acts by conversion followed by the display lift. *)

(** 元素映射先作转换，再作显示提升。 *)

Definition display_element_map {X Y : PshElement P}
    (f : ElementMap P X Y)
  : Hom (Display P X.2) (Display P Y.2)
  := (element_map_base P f)^D[P, Y.2] ∘ (element_map_eq P f)^D[P].

(** This action lies over the element map's base arrow. *)

(** 此作用位于元素映射的基底箭头之上。 *)

Theorem display_element_map_proj {X Y : PshElement P}
    (f : ElementMap P X Y)
  : display_proj P Y.2 ∘ display_element_map f
      ≈ element_map_base P f ∘ display_proj P X.2.
Proof.
  unfold display_element_map.
  rewrite <- comp_assoc, display_lift_proj, comp_assoc, display_conv_proj.
  reflexivity.
Defined.

(** The action respects base equality independently of element witnesses. *)

(** 此作用保持基底相等，不依赖元素相等见证。 *)

Theorem display_element_map_proper {X Y : PshElement P}
    (f g : ElementMap P X Y) (H : ElementMapEq P f g)
  : display_element_map f ≈ display_element_map g.
Proof.
  unfold display_element_map.
  rewrite (display_lift_equiv H Y.2), comp_assoc.
  apply comp_l. symmetry. apply display_conv_comp.
Defined.

(** Identity element maps act as identity display arrows. *)

(** 恒等元素映射作用为恒等显示箭头。 *)

Theorem display_element_map_id (X : PshElement P)
  : display_element_map (element_map_id P X) ≈ id.
Proof.
  unfold display_element_map. cbn [element_map_base].
  rewrite display_lift_id.
  transitivity ((reflexivity X.2)^D[P]).
  - symmetry. apply display_conv_comp.
  - apply display_conv_id.
Defined.

(** Composition follows from lift composition and conversion compatibility. *)

(** 由提升复合及转换相容性导出复合作用。 *)

Theorem display_element_map_comp {X Y Z : PshElement P}
    (g : ElementMap P Y Z) (f : ElementMap P X Y)
  : display_element_map (element_map_comp P g f)
      ≈ display_element_map g ∘ display_element_map f.
Proof.
  pose (e := transitivity (element_map_eq P f)
    ((element_map_eq P g)[element_map_base P f]EqF[P])).
  symmetry. unfold display_element_map. cbn [element_map_base].
  rewrite comp_assoc.
  rewrite <- (comp_assoc ((element_map_eq P g)^D[P])
    ((element_map_base P f)^D[P, Y.2]) ((element_map_eq P f)^D[P])).
  rewrite <- (display_lift_conv (element_map_base P f)
    (element_map_eq P g)).
  rewrite <- !comp_assoc.
  rewrite (display_lift_comp (element_map_base P g)
    (element_map_base P f) Z.2), !comp_assoc.
  apply comp_l.
  transitivity ((type_sub_comp P (element_map_base P g)
    (element_map_base P f) Z.2)^D[P] ∘ e^D[P]).
  - apply comp_l. symmetry. apply display_conv_comp.
  - symmetry. apply display_conv_comp.
Defined.

(** The display object and arrow actions form a functor on elements. *)

(** 显示对象及箭头作用组成元素范畴上的函子。 *)

Program Definition DisplayElementsF
  : Fct (ElementsCat P) C
  :=
  {|F0 X := Display P X.2
  ; F1 X Y := display_element_map
  |}.
Next Obligation.
  intros f g H. exact (display_element_map_proper f g H).
Defined.
Next Obligation. apply display_element_map_id. Defined.
Next Obligation. apply display_element_map_comp. Defined.

(** Display projections are natural over the element-base projection. *)

(** 显示投影对元素基底投影满足自然性。 *)

Program Definition DisplayElementsProjectionN
  : DisplayElementsF ⇒ ElementsBaseF P
  :=
  {|nt X := display_proj P X.2
  |}.
Next Obligation. apply display_element_map_proj. Defined.

(** Every element square is a display pullback transported by a conversion
    isomorphism. No additional pullback choice is made. *)

(** 每个元素方形都是沿转换同构运输的显示拉回，不另作拉回选择。 *)

Definition display_elements_comprehension_universal
  : is_comprehension DisplayElementsProjectionN.
Proof.
  intros X Y f _.
  exact (pullback_iso ((element_map_eq P f)^D[P])
    (display_conv_is_iso P (element_map_eq P f))
    (display_conv_proj (element_map_eq P f))
    (reflexivity (display_element_map f))
    (display_lift_universal (element_map_base P f) Y.2)).
Defined.

(** Coherent displays supply comprehension on the specified type elements.
    Its canonical cartesian lifts must be enabled explicitly. *)

(** 相干显示结构给出指定类型元素上的理解结构；标准笛卡尔提升须显式启用。 *)

Definition DisplayElementsComprehension
  : Comprehension (ElementsBaseF P)
  := ElementsComprehension P DisplayElementsProjectionN
      display_elements_comprehension_universal.

(** The display round trip preserves conversion in the specified hom
    equality, independently of the intermediate equality witnesses. *)

(** 显示结构往返在指定 Hom 相等下保持转换，不依赖中间相等见证。 *)

Theorem display_elements_conv {Γ : @Ob C} {A B : P Γ} (e : A ≈S B)
  : @display_conv C P
      (Comprehension_HasDisplay P DisplayElementsComprehension) Γ A B e
      ≈ @display_conv C P HD Γ A B e.
Proof.
  change (@display_lift C P HD Γ Γ id B ∘
    @display_conv C P HD Γ A (fmap P id B)
      (element_map_eq P (element_conv P e))
      ≈ @display_conv C P HD Γ A B e).
  rewrite (@display_lift_id C P HD Γ B).
  symmetry. apply (@display_conv_comp C P HD).
Defined.

(** The display round trip preserves every chosen substitution lift. *)

(** 显示结构往返保持每个选定替换提升。 *)

Theorem display_elements_lift {Γ Δ : @Ob C} (σ : Hom Δ Γ) (A : P Γ)
  : @display_lift C P
      (Comprehension_HasDisplay P DisplayElementsComprehension) Γ Δ σ A
      ≈ @display_lift C P HD Γ Δ σ A.
Proof.
  change (@display_lift C P HD Γ Δ σ A ∘
    @display_conv C P HD Δ (fmap P σ A) (fmap P σ A)
      (reflexivity (fmap P σ A))
      ≈ @display_lift C P HD Γ Δ σ A).
  rewrite (@display_conv_id C P HD). apply comp_id_r.
Defined.

End DisplayComprehension.

(** ** Comparing the Two Presentations

    Keep the type presheaf fixed. Both presentations construct each other;
    compare their actual arrows, without equality of records or lift choices.
    No fullness, resizing or terminal-context assumption is needed here. *)

(** ** 比较两种表述

    固定类型预层，两种表述互相构造，并比较实际箭头，不要求记录或提升选择相等。
    此处不需要满性、resizing 或终上下文假设。 *)

Section ComprehensionDisplayComparison.
Context {C : Cat} (P : Fct (C^op) SetCat).

(** The comprehension round trip preserves the total-space arrow action. *)

(** 理解结构往返保持全空间上的箭头作用。 *)

Theorem comprehension_display_map
    (K : Comprehension (ElementsBaseF P))
    {Γ Δ : @Ob C} {A : P Γ} {B : P Δ}
    (f : ElementMap P (Γ; A) (Δ; B))
  : @display_element_map C P (Comprehension_HasDisplay P K)
      (Γ; A) (Δ; B) f ≈ fmap (ExtF K) f.
Proof.
  change (fmap (ExtF K) (element_lift P (element_map_base P f) B) ∘
    fmap (ExtF K) (element_conv P (element_map_eq P f))
      ≈ fmap (ExtF K) f).
  rewrite <- (fct_comp (ElementsCat P) C (ExtF K)).
  apply (@fct_fmap_proper (ElementsCat P) C (ExtF K)).
  change (element_map_base P f ∘ id ≈ element_map_base P f).
  apply comp_id_r.
Defined.

(** On an explicit base-element pair the total objects coincide. Pattern
    matching supplies this identity boundary for every element object. *)

(** 对显式基底与元素配对，全空间对象一致；模式匹配为每个元素对象提供恒等边界。 *)

Definition comprehension_display_component
    (K : Comprehension (ElementsBaseF P)) (X : PshElement P)
  : Hom (@DisplayElementsF C P (Comprehension_HasDisplay P K) X)
      (ExtF K X).
Proof. destruct X as [Γ A]. exact id. Defined.

(** These boundaries are natural, so the comparison is a functor comparison
    rather than unrelated objectwise identities. *)

(** 这些边界满足自然性，故所得比较是函子比较，而非无关的逐对象恒等。 *)

Program Definition ComprehensionDisplayN
    (K : Comprehension (ElementsBaseF P))
  : @DisplayElementsF C P (Comprehension_HasDisplay P K) ⇒ ExtF K
  :=
  {|nt := comprehension_display_component K
  |}.
Next Obligation.
  destruct X as [Γ A], Y as [Δ B].
  cbn [comprehension_display_component].
  rewrite comp_id_l, comp_id_r. apply comprehension_display_map.
Defined.

(** The total-space functors are naturally isomorphic, with transparent
    inverse components. No equality of functor or proof records is used. *)

(** 全空间函子自然同构，逆分量透明，不使用函子或证明记录的相等。 *)

Program Definition comprehension_display_iso
    (K : Comprehension (ElementsBaseF P))
  : @DisplayElementsF C P (Comprehension_HasDisplay P K) ≅N ExtF K
  := (ComprehensionDisplayN K; _).
Next Obligation.
  intros [Γ A]. exists id. split; apply comp_id_l.
Defined.

(** The natural comparison also preserves the given display projection. *)

(** 自然比较同时保持给定显示投影。 *)

Theorem comprehension_display_projection
    (K : Comprehension (ElementsBaseF P)) (X : PshElement P)
  : π[K] X ∘ ComprehensionDisplayN K X
      ≈ @display_proj C P (Comprehension_HasDisplay P K) X.1 X.2.
Proof. destruct X as [Γ A]. apply comp_id_r. Defined.

(** Chosen displays and comprehension over these type elements are
    mutually constructible. This does not classify arbitrary comprehension. *)

(** 选定显示结构与这些类型元素上的理解结构互相可构造；此准则不分类任意理解结构。 *)

Definition display_iff_elements_comprehension
  : HasDisplay C P ↔ Comprehension (ElementsBaseF P).
Proof.
  split.
  - intros HD. exact (@DisplayElementsComprehension C P HD).
  - intros K. exact (Comprehension_HasDisplay P K).
Defined.

End ComprehensionDisplayComparison.
