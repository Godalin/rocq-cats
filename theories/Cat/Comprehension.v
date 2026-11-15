From Cats Require Import
  Cat.Core
  Cat.Morphism
  Cat.Functor.Core
  Cat.Natural
  Cat.Fibration
  Cat.Pullback.
From Cats Require Import Cat.Arrow.Core.

(** * Comprehension

    A natural projection from total spaces to bases sends cartesian morphisms
    to pullback squares. This property is separate from the choice of lifts. *)

(** * 理解结构

    从全空间到基底的自然投影把笛卡尔态射送到拉回方形；此性质与提升的选取分开。 *)

Definition is_comprehension {E B : Cat} {P T : Fct E B} (π : T ⇒ P)
  := ∀ X Y (f : Hom X Y), f ⦂ Cart(P)
    → is_pullback (fmap P f) (π Y) (T X) (π X) (fmap T f).

(** A fibration projection and a natural display projection preserving
    cartesian squares as pullbacks. *)

(** 纤维化投影及自然显示投影，把笛卡尔方形送到拉回。 *)

Record Comprehension {E B : Cat} (P : Fct E B)
  :=
  { comprehension_lifts : HasCartLift P
  ; ExtF : Fct E B
  ; projectionN : ExtF ⇒ P
  ; comprehension_universal : is_comprehension projectionN
  }.

Arguments comprehension_lifts {_ _ _} _.
Arguments ExtF {_ _ _} _.
Arguments projectionN {_ _ _} _.
Arguments comprehension_universal {_ _ _} _ {_ _} _ _.

Notation "A '^ext[' K ']'" := (ExtF K A)
  (at level 35, no associativity, format "A ^ext[ K ]") : cat_scope.
Notation "'π[' K ']' A" := (projectionN K A)
  (at level 35, format "π[ K ]  A") : cat_scope.

(** The display projection commutes with every total-category morphism. *)

(** 显示投影与全范畴的每条态射交换。 *)

Theorem comprehension_comm {E B : Cat} {P : Fct E B} (K : Comprehension P)
    {X Y : @Ob E} (f : Hom X Y)
  : π[K] Y ∘ fmap (ExtF K) f ≈ fmap P f ∘ π[K] X.
Proof. apply nt_naturality. Qed.

(** The arrow-category presentation is available for every comprehension.
    Fullness and faithfulness are separate properties, not fields of [K]. *)

(** 每个理解结构都可表示为取值于箭头范畴的函子。满性与忠实性是独立性质，不是
    [K] 的字段。 *)

Definition ComprehensionF {E B : Cat} {P : Fct E B} (K : Comprehension P)
  : Fct E (Arr B)
  := NatArrowF (projectionN K).

(** ** Restriction with a Coherent Base Comparison

    Interpret objects of [D] in [E] through [S]. A natural isomorphism
    compares the interpreted projection [P ∘F S] with the supplied [Q];
    it does not identify their object maps. Cartesian preservation is a
    separate hypothesis. Source comprehension needs only its candidate
    universal property, while chosen target lifts are supplied separately. *)

(** ** 带相干基底比较的限制

    通过 [S] 将 [D] 的对象解释到 [E]。自然同构比较解释后的投影 [P ∘F S]
    与给定 [Q]，不等同它们的对象映射；笛卡尔保持是独立假设。源理解结构只需
    候选泛性质，目标选定提升另行提供。 *)

Section Restriction.
Context {D E B : Cat} {P T : Fct E B} {Q : Fct D B}
    (S : Fct D E) (β : (P ∘F S) ≅N Q) (π : T ⇒ P).

(** Evaluate the source projection along the interpretation, then apply the
    given base comparison. Naturality follows by whiskering and composition. *)

(** 沿解释求值源投影，再作用给定的基底比较；须化与复合给出自然性。 *)

Definition ComprehensionRestrictionN
  : (T ∘F S) ⇒ Q
  := β.1 ∘Nv (π ∘Nr S).

(** Each preserved cartesian arrow gives a pullback across the natural
    base boundary. No equality of functors or chosen lifts is used. *)

(** 每条保持的笛卡尔箭头跨自然基底边界给出拉回，不使用函子或选定提升的相等。 *)

Definition comprehension_restrict_universal (Hπ : is_comprehension π)
    (HS : ∀ X Y (f : (@Hom D) X Y),
      f ⦂ Cart(Q) → fmap S f ⦂ Cart(P))
  : is_comprehension ComprehensionRestrictionN.
Proof.
  intros X Y f Hf.
  exact (pullback_base_boundary (β.1 X) (β.2 X)
    (β.1 Y) (iso_mono (β.1 Y) (β.2 Y))
    (nt_naturality β.1 f) (Hπ _ _ (fmap S f) (HS _ _ f Hf))).
Defined.

(** Assemble a chosen comprehension using exactly the supplied target
    lifts. Source lifts, fullness and object equality are not required;
    importing the construction enables no chosen model. *)

(** 使用给定的目标提升组装选定理解结构。不要求源提升、满性或对象相等；
    导入此构造不会启用选定模型。 *)

Program Definition RestrictedComprehension (Hπ : is_comprehension π)
    (HS : ∀ X Y (f : (@Hom D) X Y),
      f ⦂ Cart(Q) → fmap S f ⦂ Cart(P))
    (HQ : HasCartLift Q)
  : Comprehension Q
  :=
  {|comprehension_lifts := HQ
  ; ExtF := T ∘F S
  ; projectionN := ComprehensionRestrictionN
  ; comprehension_universal := comprehension_restrict_universal Hπ HS
  |}.

End Restriction.
