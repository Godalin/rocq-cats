From Cats Require Import Cat.Core.



(** * Pullbacks *)

Class HasPullback `(C : Cat) :=
  { Pb {X Y Z} : Hom X Z → Hom Y Z → Ob
  ; pb1 {X Y Z} (f : Hom X Z) (g : Hom Y Z) : Hom (Pb f g) X
  ; pb2 {X Y Z} (f : Hom X Z) (g : Hom Y Z) : Hom (Pb f g) Y
  ; pb {X Y Z} {f : Hom X Z} {g : Hom Y Z} {P}
      (p1 : Hom P X) (p2 : Hom P Y)
      (HP : f ∘ p1 ≈ g ∘ p2) : Hom P (Pb f g)

  ; axiom_pb_cond {X Y Z} {f : Hom X Z} {g : Hom Y Z}
    : f ∘ pb1 f g ≈ g ∘ pb2 f g

  ; axiom_pb_unique {X Y Z} {f : Hom X Z} {g : Hom Y Z}
      {P} {p1 : Hom P X} {p2 : Hom P Y} (HP : f ∘ p1 ≈ g ∘ p2)
    : is_unique (λ h, pb1 f g ∘ h ≈ p1 ∧ pb2 f g ∘ h ≈ p2)
        (pb p1 p2 HP)
  }.

Notation "X '×[' f ',' g ']' Y" := (@Pb _ _ X Y _ f g)
  (at level 52, no associativity,
    format "X '×[' f ',' g ] Y") : ob_scope.

Notation "'@×[' f ',' g ']'" := (@Pb _ _ _ _ _ f g)
  (at level 52, no associativity,
    format "'@×[' f ',' g ]") : ob_scope.

Notation "X '×[' f '→' Z '←' g ']' Y" := (@Pb _ _ X Y Z f g)
  (at level 52, no associativity,
    format "X  '×[' f  '→'  Z  '←'  g ]  Y") : ob_scope.

Notation "#pb1" := (pb1 _ _) : hom_scope.
Notation "#pb2" := (pb2 _ _) : hom_scope.

Notation "@pb1 f g" := (pb1 f g)
  (at level 60) : hom_scope.
Notation "@pb2 f g" := (pb2 f g)
  (at level 60) : hom_scope.

Hint Resolve axiom_pb_cond : cat.



Section Pullback.
Context `{C : Cat}.

Definition is_pullback {X Y Z : Ob} (f : Hom X Z) (g : Hom Y Z)
  := λ P : Ob, λ p1 : Hom P X, λ p2 : Hom P Y,
    f ∘ p1 ≈ g ∘ p2 ∧
      ∀ Q, ∀ q1 : Hom Q X, ∀ q2 : Hom Q Y, f ∘ q1 ≈ g ∘ q2
      → ∃ h, is_unique (λ h, p1 ∘ h ≈ q1 ∧ p2 ∘ h ≈ q2) h.

Theorem pullback_unique {X Y Z : Ob} {f : Hom X Z} {g : Hom Y Z}
    {P : Ob} {p1 : Hom P X} {p2 : Hom P Y}
    {Q : Ob} {q1 : Hom Q X} {q2 : Hom Q Y}
  : is_pullback f g P p1 p2 → is_pullback f g Q q1 q2
  → P ≅ Q.
Proof.
  intros [HP HP'] [HQ HQ'].
  destruct (HP' Q q1 q2 HQ) as [h1 [[Hh11 Hh12] Hh1_unique]].
  destruct (HQ' P p1 p2 HP) as [h2 [[Hh21 Hh22] Hh2_unique]].
  exists h2, h1; split; simpl.
  - destruct (HP' P p1 p2 HP) as [hPu [_ HPu]].
    assert (HPuEq1 : id ≈ hPu).
    { apply HPu; split; rewrite axiom_id_r; reflexivity. }
    assert (HPuEq2 : h1 ∘ h2 ≈ hPu).
    { apply HPu; split; rewrite <-axiom_comp_assoc.
      - rewrite Hh11, Hh21. cato.
      - rewrite Hh12, Hh22. cato. }
    rewrite HPuEq1. cato.
  - destruct (HQ' Q q1 q2 HQ) as [hQu [_ HQu]].
    assert (HQuEq1 : id ≈ hQu).
    { apply HQu; split; rewrite axiom_id_r; reflexivity. }
    assert (HQuEq2 : h2 ∘ h1 ≈ hQu).
    { apply HQu; split; rewrite <-axiom_comp_assoc.
      - rewrite Hh21, Hh11. cato.
      - rewrite Hh22, Hh12. cato. }
    rewrite HQuEq1. cato.
Qed.

End Pullback.



Section Pullback.
Context `{C : Cat} `{H : !HasPullback C}.
Context {X Y Z : Ob} {f : Hom X Z} {g : Hom Y Z}.

Theorem pb_pullback
  : is_pullback f g (X ×[f,g] Y) (pb1 f g) (pb2 f g).
Proof.
  split. cato. intros Q q1 q2 HQ. exists (pb q1 q2 HQ).
  apply axiom_pb_unique.
Qed.

Context {P : Ob} {p1 : Hom P X} {p2 : Hom P Y}.
Context (HP : f ∘ p1 ≈ g ∘ p2).

Theorem pb_β1 : pb1 f g ∘ pb p1 p2 HP ≈ p1.
Proof. apply axiom_pb_unique. Qed.

Theorem pb_β2 : pb2 f g ∘ pb p1 p2 HP ≈ p2.
Proof. apply axiom_pb_unique. Qed.

Theorem pb_η h
  : pb1 f g ∘ h ≈ p1 ∧ pb2 f g ∘ h ≈ p2 → h ≈ pb p1 p2 HP.
Proof. apply axiom_pb_unique. Qed.

(** Respectfulness follows from uniqueness, including independence of the
    commutativity witness. No equality between witnesses is required. *)
Theorem pb_proper {q1 : Hom P X} {q2 : Hom P Y}
    (HQ : f ∘ q1 ≈ g ∘ q2)
  : p1 ≈ q1 → p2 ≈ q2 → pb p1 p2 HP ≈ pb q1 q2 HQ.
Proof.
  intros H1 H2. apply (axiom_pb_unique HQ). split.
  - rewrite pb_β1. exact H1.
  - rewrite pb_β2. exact H2.
Qed.

Corollary pb_witness_independent (HQ : f ∘ p1 ≈ g ∘ p2)
  : pb p1 p2 HP ≈ pb p1 p2 HQ.
Proof. apply pb_proper; reflexivity. Qed.

End Pullback.

Hint Resolve pb_pullback : cat.
Hint Resolve pb_β1 : cat.
Hint Resolve pb_β2 : cat.

Hint Rewrite @pb_β1 : cat.
Hint Rewrite @pb_β2 : cat.



(** ** Pullback Properties *)

Section Pullback.
Context `{C : Cat}.
Context {X Y Z W} {f : Hom X Z} {g : Hom Y Z} {h : Hom W X}.

(** Pullback alone [id]. *)

Theorem pullback_id : is_pullback id g _ g id.
Proof. split. carw. intros Q q1 q2 H1. exists q2. split.
  split. rewrite <- H1. carw. carw.
  intros y. intros [H2 H3]. rewrite <- H3. carw.
Qed.

(** Pasting two pullback squares along their common edge. *)

Theorem pullback_comp {P Q : Ob}
    {p1 : Hom P X} {p2 : Hom P Y} {q1 : Hom Q W} {q2 : Hom Q P}
  : is_pullback f g P p1 p2
  → is_pullback h p1 Q q1 q2
  → is_pullback (f ∘ h) g Q q1 (p2 ∘ q2).
Proof.
  intros [HP HPu] [HQ HQu]. split.
  - rewrite axiom_comp_assoc, HQ.
    rewrite <- axiom_comp_assoc, HP, axiom_comp_assoc. reflexivity.
  - intros R r1 r2 Hr.
    assert (Hr' : f ∘ (h ∘ r1) ≈ g ∘ r2).
    { rewrite <- axiom_comp_assoc. exact Hr. }
    destruct (HPu R (h ∘ r1) r2 Hr') as [u [[Hu1 Hu2] Hu_unique]].
    assert (Hcone : h ∘ r1 ≈ p1 ∘ u) by (symmetry; exact Hu1).
    destruct (HQu R r1 u Hcone) as [v [[Hv1 Hv2] Hv_unique]].
    exists v. split.
    + split. exact Hv1.
      rewrite axiom_comp_assoc, Hv2. exact Hu2.
    + intros i [Hi1 Hi2].
      apply Hv_unique. split. exact Hi1.
      apply Hu_unique. split.
      * rewrite <- axiom_comp_assoc, <- HQ.
        rewrite axiom_comp_assoc, Hi1. reflexivity.
      * rewrite <- axiom_comp_assoc. exact Hi2.
Qed.

Context `{H : !HasPullback C}.

Theorem pullback_comp_iso
  : W ×[h, pb1 f g] (X ×[f,g] Y) ≅ W ×[f ∘ h, g] Y.
Proof. eapply pullback_unique.
  - eapply pullback_comp; apply pb_pullback.
  - apply pb_pullback.
Qed.

End Pullback.



Section Product.
Context `{C : Cat}.
Context `{HT : !HasTerminal C} `{HPb : !HasPullback C}.
Context {X Y : Ob}.

(** If a category has a terminal object and all pullbacks,
    it has all product objects. *)

Theorem pullback_product
  : is_product X Y (X ×[!,!] Y) (pb1 ! !) (pb2 ! !).
Proof. intros Z p q.
  assert (Hpq : ! ∘ p ≈ ! ∘ q).
  { repeat rewrite term_comp_l. reflexivity. }
  exists (pb p q Hpq). split.
  - split; [apply pb_β1 | apply pb_β2].
  - intros h Hh. apply pb_η. exact Hh.
Qed.

Context `{HP : !HasProduct C}.

(** Then it is isomorphic to the product object. *)

Theorem pullback_product_iso
  : (X ×[!,!] Y) ≅ X × Y.
Proof. eapply product_unique.
  apply pullback_product. cato.
Qed.

End Product.
