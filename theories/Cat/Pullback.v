From Cats Require Import Cat.Core Cat.Terminal Cat.Product.



(** * Pullbacks *)

Definition is_pullback {C : Cat} {X Y Z : Ob} (f : Hom X Z) (g : Hom Y Z)
  := λ P : Ob, λ p1 : Hom P X, λ p2 : Hom P Y,
    f ∘ p1 ≈ g ∘ p2 ∧
      ∀ Q, ∀ q1 : Hom Q X, ∀ q2 : Hom Q Y, f ∘ q1 ≈ g ∘ q2
      → ∃ h, is_unique (λ h, p1 ∘ h ≈ q1 ∧ p2 ∘ h ≈ q2) h.

Class HasPullback (C : Cat) :=
  { Pb {X Y Z} : Hom X Z → Hom Y Z → Ob
  ; pb1 {X Y Z} (f : Hom X Z) (g : Hom Y Z) : Hom (Pb f g) X
  ; pb2 {X Y Z} (f : Hom X Z) (g : Hom Y Z) : Hom (Pb f g) Y
  ; pullback_universal {X Y Z} {f : Hom X Z} {g : Hom Y Z}
    : is_pullback f g (Pb f g) (pb1 f g) (pb2 f g)
  }.

Definition pb {C : Cat} `{HPb : !HasPullback C} {X Y Z}
    {f : Hom X Z} {g : Hom Y Z} {P}
    (p1 : Hom P X) (p2 : Hom P Y) (HP : f ∘ p1 ≈ g ∘ p2)
  : Hom P (Pb f g) :=
  (snd (pullback_universal (f := f) (g := g)) P p1 p2 HP).1.

Theorem pullback_comm {C : Cat} `{HPb : !HasPullback C}
    {X Y Z} {f : Hom X Z} {g : Hom Y Z}
  : f ∘ pb1 f g ≈ g ∘ pb2 f g.
Proof. exact (fst (pullback_universal (f := f) (g := g))). Qed.

Theorem pullback_mediator_unique {C : Cat} `{HPb : !HasPullback C}
    {X Y Z} {f : Hom X Z} {g : Hom Y Z}
    {P} {p1 : Hom P X} {p2 : Hom P Y} (HP : f ∘ p1 ≈ g ∘ p2)
  : is_unique (λ h, pb1 f g ∘ h ≈ p1 ∧ pb2 f g ∘ h ≈ p2)
      (pb p1 p2 HP).
Proof. exact (snd (pullback_universal (f := f) (g := g)) P p1 p2 HP).2. Qed.

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

Hint Resolve pullback_comm : cat.

(** Two arrows into a pullback agree when both projections agree. *)
Theorem pullback_hom_ext {C : Cat} {X Y Z P Q : @Ob C}
    {f : Hom X Z} {g : Hom Y Z} {p1 : Hom P X} {p2 : Hom P Y}
    (HP : is_pullback f g P p1 p2) (u v : Hom Q P)
    (H1 : p1 ∘ u ≈ p1 ∘ v) (H2 : p2 ∘ u ≈ p2 ∘ v) : u ≈ v.
Proof.
  assert (Hv : f ∘ (p1 ∘ v) ≈ g ∘ (p2 ∘ v)).
  { rewrite <- !comp_assoc, (fst HP). reflexivity. }
  destruct (snd HP Q (p1 ∘ v) (p2 ∘ v) Hv) as [w [_ Hw]].
  transitivity w.
  - apply Hw. split; assumption.
  - symmetry. apply Hw. split; reflexivity.
Qed.



Section Pullback.
Context {C : Cat}.

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
    { apply HPu; split; rewrite comp_id_r; reflexivity. }
    assert (HPuEq2 : h1 ∘ h2 ≈ hPu).
    { apply HPu; split; rewrite <-comp_assoc.
      - rewrite Hh11, Hh21. cato.
      - rewrite Hh12, Hh22. cato. }
    rewrite HPuEq1. cato.
  - destruct (HQ' Q q1 q2 HQ) as [hQu [_ HQu]].
    assert (HQuEq1 : id ≈ hQu).
    { apply HQu; split; rewrite comp_id_r; reflexivity. }
    assert (HQuEq2 : h2 ∘ h1 ≈ hQu).
    { apply HQu; split; rewrite <-comp_assoc.
      - rewrite Hh21, Hh11. cato.
      - rewrite Hh22, Hh12. cato. }
    rewrite HQuEq1. cato.
Qed.

End Pullback.

(** Transfer the universal property along an isomorphism of the pullback vertex. *)
Definition pullback_iso {C : Cat} {X Y Z : @Ob C} {f : Hom X Z} {g : Hom Y Z}
    {P Q : @Ob C} {p1 : Hom P X} {p2 : Hom P Y}
    {q1 : Hom Q X} {q2 : Hom Q Y} (i : Hom Q P) (Hi : is_iso i)
    (H1 : p1 ∘ i ≈ q1) (H2 : p2 ∘ i ≈ q2)
    (HP : is_pullback f g P p1 p2) : is_pullback f g Q q1 q2.
Proof.
  destruct Hi as [ii [Hii Hi]]. destruct HP as [Hcomm Hu]. split.
  - rewrite <- H1, <- H2, <- !comp_assoc, Hcomm. reflexivity.
  - intros R r1 r2 Hr. destruct (Hu R r1 r2 Hr) as [h [[Hh1 Hh2] Hh_unique]].
    exists (ii ∘ h). split.
    + split.
      * rewrite <- H1, comp_assoc, <- (comp_assoc i), Hi, comp_id_l. exact Hh1.
      * rewrite <- H2, comp_assoc, <- (comp_assoc i), Hi, comp_id_l. exact Hh2.
    + intros k [Hk1 Hk2]. transitivity (ii ∘ (i ∘ k)).
      * symmetry. rewrite <- comp_assoc, Hii, comp_id_l. reflexivity.
      * apply comp_l. apply Hh_unique. split;
          rewrite <- comp_assoc; [rewrite H1 | rewrite H2]; assumption.
Defined.



Section Pullback.
Context {C : Cat} `{H : !HasPullback C}.
Context {X Y Z : Ob} {f : Hom X Z} {g : Hom Y Z}.

Context {P : Ob} {p1 : Hom P X} {p2 : Hom P Y}.
Context (HP : f ∘ p1 ≈ g ∘ p2).

Theorem pb_β1 : pb1 f g ∘ pb p1 p2 HP ≈ p1.
Proof. apply pullback_mediator_unique. Qed.

Theorem pb_β2 : pb2 f g ∘ pb p1 p2 HP ≈ p2.
Proof. apply pullback_mediator_unique. Qed.

Theorem pb_η h
  : pb1 f g ∘ h ≈ p1 ∧ pb2 f g ∘ h ≈ p2 → h ≈ pb p1 p2 HP.
Proof. apply pullback_mediator_unique. Qed.

(** Respectfulness follows from uniqueness, including independence of the
    commutativity witness. No equality between witnesses is required. *)
Theorem pb_proper {q1 : Hom P X} {q2 : Hom P Y}
    (HQ : f ∘ q1 ≈ g ∘ q2)
  : p1 ≈ q1 → p2 ≈ q2 → pb p1 p2 HP ≈ pb q1 q2 HQ.
Proof.
  intros H1 H2. apply (pullback_mediator_unique HQ). split.
  - rewrite pb_β1. exact H1.
  - rewrite pb_β2. exact H2.
Qed.

Corollary pb_witness_independent (HQ : f ∘ p1 ≈ g ∘ p2)
  : pb p1 p2 HP ≈ pb p1 p2 HQ.
Proof. apply pb_proper; reflexivity. Qed.

End Pullback.

Hint Resolve pullback_universal : cat.
Hint Resolve pb_β1 : cat.
Hint Resolve pb_β2 : cat.

Hint Rewrite @pb_β1 : cat.
Hint Rewrite @pb_β2 : cat.



(** ** Pullback Properties *)

Section Pullback.
Context {C : Cat}.
Context {X Y Z W} {f : Hom X Z} {g : Hom Y Z} {h : Hom W X}.

(** Pullback alone [id]. *)

Theorem pullback_id : is_pullback id g _ g id.
Proof. split. carw. intros Q q1 q2 H1. exists q2. split.
  split. rewrite <- H1. carw. carw.
  intros y. intros [H2 H3]. rewrite <- H3. carw.
Defined.

(** Pasting two pullback squares along their common edge. *)

Theorem pullback_comp {P Q : Ob}
    {p1 : Hom P X} {p2 : Hom P Y} {q1 : Hom Q W} {q2 : Hom Q P}
  : is_pullback f g P p1 p2
  → is_pullback h p1 Q q1 q2
  → is_pullback (f ∘ h) g Q q1 (p2 ∘ q2).
Proof.
  intros [HP HPu] [HQ HQu]. split.
  - rewrite comp_assoc, HQ.
    rewrite <- comp_assoc, HP, comp_assoc. reflexivity.
  - intros R r1 r2 Hr.
    assert (Hr' : f ∘ (h ∘ r1) ≈ g ∘ r2).
    { rewrite <- comp_assoc. exact Hr. }
    destruct (HPu R (h ∘ r1) r2 Hr') as [u [[Hu1 Hu2] Hu_unique]].
    assert (Hcone : h ∘ r1 ≈ p1 ∘ u) by (symmetry; exact Hu1).
    destruct (HQu R r1 u Hcone) as [v [[Hv1 Hv2] Hv_unique]].
    exists v. split.
    + split. exact Hv1.
      rewrite comp_assoc, Hv2. exact Hu2.
    + intros i [Hi1 Hi2].
      apply Hv_unique. split. exact Hi1.
      apply Hu_unique. split.
      * rewrite <- comp_assoc, <- HQ.
        rewrite comp_assoc, Hi1. reflexivity.
      * rewrite <- comp_assoc. exact Hi2.
Defined.

Context `{H : !HasPullback C}.

Theorem pullback_comp_iso
  : W ×[h, pb1 f g] (X ×[f,g] Y) ≅ W ×[f ∘ h, g] Y.
Proof. eapply pullback_unique.
  - eapply pullback_comp; apply pullback_universal.
  - apply pullback_universal.
Qed.

End Pullback.



Section Product.
Context {C : Cat}.
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
