From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Fibration
  Cat.Natural
  Cat.Comprehension
  Instance.Set.Core.

(** * Elements of a Setoid-Valued Presheaf

    Fix a presheaf [P] on [C]. An arrow retains a base map and a witness
    that its source element is the restriction of its target. Equality
    compares base maps, without identifying element-equality witnesses. *)

(** * 广集值预层的元素

    固定 [C] 上的预层 [P]。态射保留基底映射及源元素等于目标限制的见证；
    相等比较基底映射，不等同元素相等见证。 *)

Section Elements.
Context {C : Cat} (P : Fct (C^op) SetCat).

(** A base object with an element of its presheaf value. *)

(** 基底对象及其预层值中的元素。 *)

Definition PshElement
  := ∃ Γ : @Ob C, P Γ.

(** An element-preserving base arrow, retaining its Type-valued witness. *)

(** 保持元素的基底箭头，保留 Type 值见证。 *)

Record ElementMap (X Y : PshElement)
  :=
  { element_map_base : Hom X.1 Y.1
  ; element_map_eq : X.2 ≈S fmap P element_map_base Y.2
  }.

Arguments element_map_base {_ _} _.
Arguments element_map_eq {_ _} _.

(** Equality compares the supplied base maps. *)

(** 相等比较给定的基底映射。 *)

Definition ElementMapEq {X Y : PshElement} (f g : ElementMap X Y)
  := element_map_base f ≈ element_map_base g.

(** The inherited base equality is an equivalence relation. *)

(** 继承的基底相等构成等价关系。 *)

Global Instance ElementMapEq_Equivalence {X Y : PshElement}
  : Equivalence (@ElementMapEq X Y).
Proof.
  split; unfold ElementMapEq.
  - intros f. reflexivity.
  - intros f g H. symmetry. exact H.
  - intros f g h H K. transitivity (element_map_base g); assumption.
Defined.

(** Identity uses the presheaf identity law. *)

(** 恒等使用预层的恒等律。 *)

Program Definition element_map_id (X : PshElement)
  : ElementMap X X
  :=
  {|element_map_base := id
  |}.
Next Obligation. exact (symmetry (functor_id (C^op) SetCat P X.2)). Defined.

(** Composition uses restriction respectfulness and the presheaf law. *)

(** 复合使用限制的尊重性及预层函子律。 *)

Program Definition element_map_comp {X Y Z : PshElement}
    (g : ElementMap Y Z) (f : ElementMap X Y)
  : ElementMap X Z
  :=
  {|element_map_base := element_map_base g ∘ element_map_base f
  |}.
Next Obligation.
  transitivity (fmap P (element_map_base f) Y.2).
  - exact (element_map_eq f).
  - transitivity (fmap P (element_map_base f)
      (fmap P (element_map_base g) Z.2)).
    + apply func_proper. exact (element_map_eq g).
    + exact (symmetry (functor_comp (C^op) SetCat P
        (element_map_base f) (element_map_base g) Z.2)).
Defined.

(** The category retains actual elements, rather than maps from a unit set. *)

(** 此范畴直接保留元素，不把它们替换为从单位广集出发的映射。 *)

Program Definition ElementsCat
  : Cat
  :=
  {|Ob := PshElement
  ; HomSet X Y :=
      {|carrier := ElementMap X Y
      ; carrier_equiv := ElementMapEq
      ; carrier_setoid := ElementMapEq_Equivalence
      |}
  ; id := element_map_id
  ; comp X Y Z := element_map_comp
  |}.
Next Obligation.
  intros g g' H f f' K. apply comp_proper; assumption.
Defined.
Next Obligation. apply comp_id_r. Defined.
Next Obligation. apply comp_id_l. Defined.
Next Obligation. apply comp_assoc. Defined.

(** Forget the element, retaining the base object and arrow. *)

(** 忘却元素，保留基底对象与箭头。 *)

Program Definition ElementsBaseF
  : Fct ElementsCat C
  :=
  {|F0 X := X.1
  ; F1 X Y := element_map_base
  |}.
Next Obligation. intros f g H. exact H. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** Designated element equality gives a vertical arrow over identity. *)

(** 指定元素相等给出恒等基底上的垂直箭头。 *)

Program Definition element_conv {Γ : @Ob C} {A B : P Γ} (e : A ≈S B)
  : ElementMap (Γ; A) (Γ; B)
  :=
  {|element_map_base := id
  |}.
Next Obligation.
  transitivity B; [exact e |].
  exact (symmetry (functor_id (C^op) SetCat P B)).
Defined.

(** Restriction gives the canonical arrow over a supplied substitution. *)

(** 限制给出给定替换上的标准箭头。 *)

Program Definition element_lift {Γ Δ : @Ob C} (σ : Hom Δ Γ) (A : P Γ)
  : ElementMap (Δ; fmap P σ A) (Γ; A)
  :=
  {|element_map_base := σ
  ; element_map_eq := reflexivity _
  |}.

End Elements.

Arguments element_map_base {_} _ {_ _} _.
Arguments element_map_eq {_} _ {_ _} _.

(** ** Cartesian Element Maps

    Keep [P] fixed. Every element map is cartesian: its element witness
    determines the factor's witness, while the base factor determines its
    equality class. No element witness is discarded or compared natively. *)

(** ** 笛卡尔元素映射

    保持 [P] 固定。每条元素映射均为笛卡尔态射：其元素见证确定分解的见证，
    基底分解确定其相等类；不丢弃元素见证，也不比较它们的原生相等。 *)

Section ElementsFibration.
Context {C : Cat} (P : Fct (C^op) SetCat).

(** The cartesian factor retains the prescribed base arrow transparently. *)

(** 笛卡尔分解透明地保留指定基底箭头。 *)

Program Definition element_factor {X Y Z : PshElement P}
    (f : ElementMap P X Y) (g : ElementMap P Z Y)
    (u : Hom Z.1 X.1)
    (H : element_map_base P f ∘ u ≈ element_map_base P g)
  : ElementMap P Z X
  :=
  {|element_map_base := u
  |}.
Next Obligation.
  transitivity (fmap P (element_map_base P g) Y.2).
  - exact (element_map_eq P g).
  - transitivity (fmap P (element_map_base P f ∘ u) Y.2).
    + exact (@functor_fmap_proper (C^op) SetCat P _ _ _ _
        (symmetry H) Y.2).
    + transitivity (fmap P u (fmap P (element_map_base P f) Y.2)).
      * exact (functor_comp (C^op) SetCat P
          u (element_map_base P f) Y.2).
      * apply func_proper. symmetry. exact (element_map_eq P f).
Defined.

(** Every element map is cartesian, using the supplied equality witness. *)

(** 每条元素映射均为笛卡尔态射，使用给定的相等见证。 *)

Definition element_map_cartesian {X Y : PshElement P}
    (f : ElementMap P X Y)
  : f ⦂ Cart(ElementsBaseF P).
Proof.
  intros Z g u H. exists (element_factor f g u H).
  refine {|this := _
          ; that := _
          |}.
  - split; [reflexivity | exact H].
  - intros h [Hb _]. exact Hb.
Defined.

(** Canonical restriction chooses cartesian lifts with reflexive base
    identification. The chosen structure must be enabled explicitly. *)

(** 标准限制选择基底识别为自反的笛卡尔提升；选定结构须显式启用。 *)

Program Definition ElementsBaseF_HasCartesianLift
  : HasCartesianLift (ElementsBaseF P)
  :=
  {|CartesianLift Y Γ σ := (Γ; fmap P σ Y.2)
  ; cartesian_lift_base Y Γ σ := eq_refl
  ; cartesian_lift Y Γ σ :=
      {|element_map_base := σ
      ; element_map_eq := reflexivity _
      |}
  |}.
Next Obligation. symmetry. apply comp_id_r. Defined.
Next Obligation. apply element_map_cartesian. Defined.

(** A total-space functor and a cartesian-to-pullback natural projection
    suffice for comprehension; the element projection supplies its lifts. *)

(** 全空间函子及把笛卡尔箭头送到拉回的自然投影已足够提供理解结构；
    元素投影提供其选定提升。 *)

Definition ElementsComprehension {T : Fct (ElementsCat P) C}
    (π : T ⇒ ElementsBaseF P) (Hπ : is_comprehension π)
  : Comprehension (ElementsBaseF P)
  :=
  {|comprehension_lifts := ElementsBaseF_HasCartesianLift
  ; ExtF := T
  ; projectionN := π
  ; comprehension_universal := Hπ
  |}.

End ElementsFibration.
