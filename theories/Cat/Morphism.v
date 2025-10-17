From Cats Require Import Cat.Core.



(** * Morphisms *)

Section Morphism.
Context `{C : Cat}.



(** ** Monomorphisms

    In Rocq, law of exclude middle (lem) is not admitted as default,
    thus the law of contraposition. Since our aim is to build a
    constructive theory of categories, we provide both versions of
    the definition of being a [monomorphism]. From the theorem proving
    perspective, it is best practice to assume the weaker version
    (i.e., [is_mono']) as input, and producing the stronger version
    (i.e., [is_mono]) as output.
    
    Similar situation for [is_epi] and [is_epi']. *)

Definition is_mono {Y Z} (f : Hom Y Z) : Prop
  := ∀ X, ∀ x y : Hom X Y, f ∘ x ≈ f ∘ y → x ≈ y.

Definition is_mono' {Y Z} (f : Hom Y Z) : Prop
  := ∀ X, ∀ x y : Hom X Y, x ≉ y → f ∘ x ≉ f ∘ y.

Proposition mono_mono' {Y Z} (f : Hom Y Z)
  : is_mono f → is_mono' f.
Proof. firstorder. Qed.

Proposition mono_id {X} : is_mono (@id X).
Proof. intros Y x y Heq.
  rewrite axiom_id_l in Heq.
  rewrite axiom_id_l in Heq. auto.
Qed.

Proposition mono_comp {X Y Z} (f : Hom X Y) (g : Hom Y Z)
  : is_mono f → is_mono g → is_mono (g ∘ f).
Proof. intros Hf Hg W x y Heq.
  apply Hf. apply Hg.
  repeat rewrite <- axiom_comp_assoc. auto.
Qed.

Proposition mono'_comp {X Y Z} (f : Hom X Y) (g : Hom Y Z)
  : is_mono' f → is_mono' g → is_mono' (g ∘ f).
Proof. intros Hf Hg W x y Hneq.
  repeat rewrite axiom_comp_assoc.
  apply Hg. apply Hf. auto.
Qed.

(* TODO mono' version *)

Proposition mono_cancel_l {X Y Z} (f : Hom X Y) (g : Hom Y Z)
  : is_mono (g ∘ f) → is_mono f.
Proof. intros Hgf W x y Hf.
  apply (comp_l g) in Hf. apply Hgf.
  repeat rewrite axiom_comp_assoc. auto.
Qed.

Proposition iso_mono {X Y} (f : Hom X Y)
  : is_iso f → is_mono f.
Proof. intros [fi [H1 H2]] Z x y H.
  apply (comp_l fi) in H.
  repeat rewrite <- axiom_comp_assoc in H.
  repeat rewrite H1 in H.
  repeat rewrite axiom_id_l in H. auto.
Qed.



Record Mono (X Y : Ob) :=
  { mor :> Hom X Y
  ; mor_mono : is_mono mor
  }.

Notation "X ↣ Y" := (Mono X Y)
  (at level 35, no associativity) : cat_scope.

Program Canonical Structure Mono_id {X} :=
  {|mor := @id X |}.
Next Obligation. apply mono_id. Qed.

Program Canonical Structure Mono_comp {X Y Z} (f : Y ↣ Z) (g : X ↣ Y) :=
  {|mor := f ∘ g |}.
Next Obligation. apply mono_comp.
  apply mor_mono. apply mor_mono.
Qed.

Program Canonical Structure Mono_term
    `{!HasTerminal C} {X} (f : Hom 1 X) :=
  {|mor := f |}.
Next Obligation. intros Y x y _.
  rewrite term_η. rewrite (term_η y). reflexivity.
Qed.

(* Definition is_factored_through_by {X Y Z}
    (g : Hom Y Z) (f : Hom X Z) (h : Hom X Y)
  := f ≈ g ∘ h. *)

Definition is_factored_through {X Y Z} (g : Hom Y Z) (f : Hom X Z)
  := ∃ h, f ≈ g ∘ h.

Proposition iso_by_factor {X Y Z} {f : X ↣ Z} {g : Y ↣ Z}
  : is_factored_through g f → is_factored_through f g
  → X ≅ Y.
Proof. intros [h1 H1] [h2 H2].
  exists h1, h2. split; simpl.
  assert (f ∘ (h2 ∘ h1) ≈ f ∘ id).
  { cacl. rewrite <- H2, H1. cato. }
  eapply mor_mono. eauto.
  assert (g ∘ (h1 ∘ h2) ≈ g ∘ id).
  { cacl. rewrite <- H1, H2. cato. }
  eapply mor_mono. eauto.
Qed.



Record Sub (X : Ob) :=
  { sub : Ob
  ; sub_mono :> sub ↣ X
  }.

Definition object_of_Sub {X Y} (f : X ↣ Y) := X.

Coercion object_of_Sub : Mono >-> Ob.

Program Canonical Structure id_Sub {X : Ob} : Sub X :=
  {|sub := X; sub_mono := Mono_id |}.

Program Canonical Structure term_Sub
    `{!HasTerminal C} {X : Ob} (f : Hom 1 X) : Sub X :=
  {|sub := 1; sub_mono := f |}.

Definition Sub_le Z (i j : Sub Z) : Prop
  := is_factored_through j i.

Infix "≲Sub" := (Sub_le _)
  (at level 50, no associativity) : cat_scope.

Infix "≲Sub[ Z  ]" := (Sub_le Z)
  (at level 50, no associativity) : cat_scope.

Definition Sub_eq Z (i j : Sub Z) : Prop
  := i ≲Sub j ∧ j ≲Sub i.

Infix "~Sub" := (Sub_eq _)
  (at level 50, no associativity) : cat_scope.

Infix "~Sub[ Z  ]" := (Sub_eq Z)
  (at level 50, no associativity) : cat_scope.

Program Instance Sub_le_Reflexive {Z} : Reflexive (Sub_le Z).
Next Obligation. exists id. cato. Qed.

Program Instance Sub_le_Transitive {Z} : Transitive (Sub_le Z).
Next Obligation. destruct H as [g Hg]. destruct H0 as [h Hh].
  exists (h ∘ g).
  rewrite <- axiom_comp_assoc.
  rewrite Hg. rewrite Hh. cato.
Qed.

Program Instance Sub_le_PreOrder {Z} : PreOrder (Sub_le Z).

Program Instance Sub_eq_Reflexive {Z} : Reflexive (Sub_eq Z).
Next Obligation. split; reflexivity. Qed.

Program Instance Sub_eq_Symmetric {Z} : Symmetric (Sub_eq Z).
Next Obligation. destruct H. split; auto. Qed.

Program Instance Sub_eq_Transitive {Z} : Transitive (Sub_eq Z).
Next Obligation. destruct H, H0. split; transitivity y; auto. Qed.

Program Instance Sub_eq_Equivalence {Z} : Equivalence (Sub_eq Z).

Proposition Sub_le_Mono {Z} {i j : Sub Z}
  : i ≲Sub j → ∃ k : i ↣ j, True.
Proof. intros [h H].
  assert (Hmi : is_mono (j ∘ h)).
  { intros W x y H1. rewrite <- H in H1.
    apply sub_mono. auto. }
  assert (Hmh : is_mono h).
  { eapply mono_cancel_l. eauto. }
  exists {| sub := i; sub_mono := {| mor := h; mor_mono := Hmh |} |}.
  auto.
Qed.

Proposition iso_by_Sub_eq {Z} {i j : Sub Z}
  : i ~Sub j → i ≅ j .
Proof. intros [H1 H2]. eapply iso_by_factor; eauto. Qed.



(** ** Epimorphisms

    Similar situation as [is_mono] and [is_mono']. *)

Definition is_epi {X Y} (f : Hom X Y) : Prop
  := ∀ Z, ∀ x y : Hom Y Z, x ∘ f ≈ y ∘ f → x ≈ y.

Definition is_epi' {X Y} (f : Hom X Y) : Prop
  := ∀ Z, ∀ x y : Hom Y Z, x ≉ y → x ∘ f ≉ y ∘ f.

Proposition epi_epi' {X Y} (f : Hom X Y)
  : is_epi f → is_epi' f.
Proof. firstorder. Qed.

End Morphism.



Arguments is_factored_through {_ _ _ _} _ _ /.
Arguments sub {_ _} _.

Notation "X '↣' Y" := (Mono X Y)
  (at level 35, no associativity) : cat_scope.

Notation "X '⊆' Z" := (X : Sub Z)
  (at level 50) : cat_scope.

Infix "≲Sub" := (Sub_le _)
  (at level 50, no associativity) : cat_scope.

Infix "≲Sub[ Z  ]" := (Sub_le Z)
  (at level 50, no associativity) : cat_scope.

Infix "~Sub" := (Sub_eq _)
  (at level 50, no associativity) : cat_scope.

Infix "~Sub[ Z  ]" := (Sub_eq Z)
  (at level 50, no associativity) : cat_scope.
