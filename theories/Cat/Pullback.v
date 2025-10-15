From Cats Require Import Cat.Core.



(** Pullbacks *)

Class HasPullback `(C : Cat) :=
  { Pb {X Y Z} : Hom X Z → Hom Y Z → Ob
  ; pb1 {X Y Z} (f : Hom X Z) (g : Hom Y Z) : Hom (Pb f g) X
  ; pb2 {X Y Z} (f : Hom X Z) (g : Hom Y Z) : Hom (Pb f g) Y
  ; pb {X Y Z} {f : Hom X Z} {g : Hom Y Z} {P} (p1 : Hom P X) (p2 : Hom P Y) : Hom P (Pb f g)

  ; axiom_pb_proper {X Y Z} {f : Hom X Z} {g : Hom Y Z} {P}
    :: Proper (@HomEq[P, X] ==> @HomEq[P, Y] ==> @HomEq[P, Pb f g]) (pb)

  ; axiom_pb_cond {X Y Z} {f : Hom X Z} {g : Hom Y Z}
    : f ∘ pb1 f g ≈ g ∘ pb2 f g

  ; axiom_pb_unique {X Y Z} {f : Hom X Z} {g : Hom Y Z}
      {P} {p1 : Hom P X} {p2 : Hom P Y}
    : f ∘ p1 ≈ g ∘ p2
      → is_unique (λ h, pb1 f g ∘ h ≈ p1 ∧ pb2 f g ∘ h ≈ p2) (pb p1 p2)
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

(* Notation "X '×[' Z ']' Y" := (@Pb _ _ X Y Z _ _)
  (at level 51, right associativity,
    format "X  '×[' Z ]  Y") : ob_scope. *)

(* Notation "'@pb' f g p1 p2" := (@pb _ _ _ _ _ f g _ p1 p2)
  (at level 30) : hom_scope. *)



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
  split.
  - apply axiom_pb_cond.
  - intros Q q1 q2. exists (pb q1 q2).
    apply axiom_pb_unique. auto.
Qed.

Context {P : Ob} {p1 : Hom P X} {p2 : Hom P Y}.
Context (HP : f ∘ p1 ≈ g ∘ p2).

Theorem pb_β1 : pb1 f g ∘ pb p1 p2 ≈ p1.
Proof. apply axiom_pb_unique. auto. Qed.

Theorem pb_β2 : pb2 f g ∘ pb p1 p2 ≈ p2.
Proof. apply axiom_pb_unique. auto. Qed.

Theorem pb_η {h} : pb1 f g ∘ h ≈ p1 ∧ pb2 f g ∘ h ≈ p2 → h ≈ pb p1 p2.
Proof. apply axiom_pb_unique. auto. Qed.

End Pullback.



Section Pullback.
Context `{C : Cat} `{H : !HasPullback C}.
Context {X Y Z W} {f : Hom X Z} {g : Hom Y Z} {h : Hom W X}.

Theorem pullback_trans'
  : is_pullback (f ∘ h) g _
    (pb1 h (pb1 f g)) (pb2 f g ∘ pb2 h (pb1 f g)).
Proof.
  unfold is_pullback. split.
  - rewrite axiom_comp_assoc.
    rewrite axiom_pb_cond.
    rewrite <- axiom_comp_assoc.
    rewrite axiom_pb_cond.
    rewrite axiom_comp_assoc.
    reflexivity.
  - intros Q q1 q2 Hq.
    set (h1 := pb (h ∘ q1) q2 : Hom Q (X ×[f,g] Y)).
    set (h2 := pb q1 h1 : Hom Q (W ×[h,pb1 f g] (X ×[f,g] Y))).
    exists h2.
    split.
    + split; unfold h2; unfold h1.
      rewrite pb_β1. cato.
      rewrite pb_β1. cato. rewrite <- axiom_comp_assoc. cato.
      rewrite axiom_comp_assoc.
      rewrite pb_β2. rewrite pb_β2; cato.
      rewrite <- axiom_comp_assoc. cato.
      rewrite pb_β1. cato. rewrite <- axiom_comp_assoc. cato.
    + intros i [Hi1 Hi2].
      unfold h2, h1. rewrite <- Hi1, <- Hi2.
      apply pb_η.
      rewrite pb_β1. reflexivity.
      rewrite Hi1. rewrite Hi2.
      rewrite <- axiom_comp_assoc. apply Hq.
      split. reflexivity.
      apply pb_η.
      rewrite Hi1, Hi2.
      rewrite <- axiom_comp_assoc. cato.
      split.
      rewrite <- axiom_comp_assoc.
      rewrite <- axiom_comp_assoc.
      rewrite axiom_pb_cond. reflexivity.
      rewrite axiom_comp_assoc. reflexivity.
Qed.

Theorem pullback_trans
  : W ×[h, pb1 f g] (X ×[f,g] Y) ≅ W ×[f ∘ h, g] Y.
Proof.
  apply (pullback_unique (pullback_trans') (pb_pullback)).
Qed.

End Pullback.
