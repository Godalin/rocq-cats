From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Fibration
  Cat.Comprehension
  Cat.Terminal
  Instance.Set.Core
  Instance.Set.Elements
  DTT.CwF
  DTT.Display.Core
  DTT.Display.Comprehension.

(** * Interpreting Type Elements in a Comprehension Category

    Fix a type presheaf [P] and interpret its elements through [S]. The
    supplied natural isomorphism compares interpreted bases with contexts;
    cartesian preservation and the source comprehension property remain
    explicit. No type interpretation is inferred from arbitrary comprehension.
    Canonical element lifts and the existing display recovery do the rest. *)

(** * 在理解范畴中解释类型元素

    固定类型预层 [P]，通过 [S] 解释其元素。给定自然同构比较解释后的基底与
    上下文；笛卡尔保持及源理解泛性质仍为显式输入。不从任意理解结构推断类型
    解释，其余部分复用标准元素提升及既有显示恢复。 *)

Section InterpretedElements.
Context {C E : Cat} (P : Fct (C^op) SetCat)
    {R T : Fct E C} (S : Fct (ElementsCat P) E)
    (β : (R ∘F S) ≅N ElementsBaseF P) (π : T ⇒ R)
    (Hπ : is_comprehension π)
    (HS : ∀ X Y (f : ElementMap P X Y), (fmap S f) ⦂ Cart(R)).

(** Restrict the candidate source comprehension. Every element arrow is
    cartesian, and canonical element lifts supply the target choice; no
    source cleavage or additional target lift data are needed. *)

(** 限制源候选理解结构。每条元素箭头均为笛卡尔的，标准元素提升提供目标选择；
    不需要源 cleavage 或额外目标提升数据。 *)

Definition InterpretedElementsComprehension
  : Comprehension (ElementsBaseF P)
  := RestrictedComprehension S β π Hπ
    (λ X Y f _, HS X Y f) (ElementsBaseF_HasCartesianLift P).

(** The restricted comprehension supplies coherent displays for the given
    type presheaf. This definition registers no chosen model. *)

(** 限制后的理解结构为给定类型预层提供相干显示结构；此定义不注册选定模型。 *)

Definition InterpretedElements_HasDisplay
  : HasDisplay C P
  := Comprehension_HasDisplay P InterpretedElementsComprehension.

(** Recover the type-and-term functor and context extensions by the existing
    display theorem, adding only the independent terminal-context choice. *)

(** 复用既有显示定理恢复类型—项函子及上下文扩张，只另加独立的终上下文选择。 *)

Definition InterpretedCwF `{HT : !HasTerminal C}
  : CwF C
  := @ComprehensionCwF C P InterpretedElementsComprehension HT.

(** The display projection includes the supplied base comparison; it does
    not identify interpreted base objects with contexts by native equality. *)

(** 显示投影包含给定基底比较，不以原生相等识别解释后的基底对象与上下文。 *)

Theorem interpreted_display_proj {Γ : @Ob C} (A : P Γ)
  : @display_proj C P InterpretedElements_HasDisplay Γ A
      ≈ β.1 (Γ; A) ∘ π (S (Γ; A)).
Proof. reflexivity. Defined.

(** Conversion uses the interpretation of the designated equality arrow,
    retaining the supplied Type-valued equality witness as data. *)

(** 转换使用指定相等箭头的解释，并将给定 Type 值相等见证保留为数据。 *)

Theorem interpreted_display_conv {Γ : @Ob C} {A B : P Γ} (e : A ≈S B)
  : @display_conv C P InterpretedElements_HasDisplay Γ A B e
      ≈ fmap T (fmap S (element_conv P e)).
Proof. reflexivity. Defined.

(** Substitution uses the interpreted canonical restriction, without
    selecting another cartesian lift in the source category. *)

(** 替换使用标准限制的解释，不在源范畴中另选笛卡尔提升。 *)

Theorem interpreted_display_lift {Γ Δ : @Ob C} (σ : Hom Δ Γ) (A : P Γ)
  : @display_lift C P InterpretedElements_HasDisplay Γ Δ σ A
      ≈ fmap T (fmap S (element_lift P σ A)).
Proof. reflexivity. Defined.

(** The recovered total-space functor is naturally isomorphic to the
    interpreted source total-space functor. The existing comparison keeps
    its transparent components and inverse maps. *)

(** 恢复的全空间函子自然同构于解释后的源全空间函子；既有比较保留透明分量及
    逆映射。 *)

Definition interpreted_display_iso
  : @DisplayElementsF C P InterpretedElements_HasDisplay ≅N (T ∘F S)
  := comprehension_display_iso P InterpretedElementsComprehension.

(** The natural comparison preserves projections across the specified base
    boundary. No equality of functor records or chosen lifts is asserted. *)

(** 自然比较跨指定基底边界保持投影，不断言函子记录或选定提升的相等。 *)

Theorem interpreted_display_projection (X : PshElement P)
  : (β.1 X ∘ π (S X)) ∘
      ComprehensionDisplayN P InterpretedElementsComprehension X
      ≈ @display_proj C P InterpretedElements_HasDisplay X.1 X.2.
Proof.
  exact (comprehension_display_projection P
    InterpretedElementsComprehension X).
Defined.

End InterpretedElements.
