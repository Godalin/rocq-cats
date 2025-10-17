From Cats Require Import Cat.Core.
From Cats Require Import Cat.Pullback.
From Cats Require Import Cat.Morphism.
From Cats Require Import Cat.Functor.
From Cats Require Import Cat.Set.



(** * Sub-object Functor

    The type of all sub-objects of a given object in a category
    is naturally equipped with a equivalence the [Sub_eq], in our
    setoid setting, this structure fits well as an contravariant
    functor. *)

Section Sub.
Context `{C : Cat} `{H : !HasPullback C}.

Program Canonical Structure SubObject Z : SetC :=
  {|carrier := Sub Z
  ; carrier_equiv := Sub_eq Z
  |}.
Next Obligation. apply Sub_eq_Equivalence. Qed.

(** sX ------> sY
    v          v
    |          |
    |          s
    |          |
    v          v
    X ---f---> Y *)

Program Definition Sub_fmap {X Y : Ob}
    (f : Hom X Y) (sY : Sub Y) : Sub X :=
  {|sub := Pb f sY
  ; sub_mono := {| mor := pb1 f sY |}
  |}.
Next Obligation.
  intros W x y H1.
  assert (Hx : f ∘ (pb1 f sY ∘ x) ≈ sY ∘ (pb2 f sY ∘ x)).
  { rewrite <- axiom_comp_assoc.
    rewrite <- axiom_comp_assoc.
    rewrite axiom_pb_cond. cato. }
  assert (Hy : f ∘ (pb1 f sY ∘ y) ≈ sY ∘ (pb2 f sY ∘ y)).
  { rewrite <- axiom_comp_assoc.
    rewrite <- axiom_comp_assoc.
    rewrite axiom_pb_cond. cato. }
  destruct (axiom_pb_unique Hx) as [[Hx11 Hx12] Hx2].
  specialize (Hx2 y).
  assert (Hxη : x ≈ pb (pb1 f sY ∘ x) (pb2 f sY ∘ x)).
  { apply pb_η. auto. split; cato. }
  assert (Hyη : y ≈ pb (pb1 f sY ∘ y) (pb2 f sY ∘ y)).
  { apply pb_η. auto. split; cato. }
  rewrite <- Hxη in Hx2.
  symmetry. apply Hx2.
  split. symmetry. auto.
  assert (sY ∘ (pb2 f sY ∘ x) ≈ sY ∘ (pb2 f sY ∘ y)).
  { rewrite <- Hx, <- Hy. apply comp_l. auto. }
  apply sub_mono in H0. symmetry. auto.
Qed.

Proposition Sub_fmap_Ob {X Y} {f : Hom X Y} {r : Sub Y}
  : sub (Sub_fmap f r) = X ×[f,r] (sub r).
Proof. simpl. auto. Qed.

Program Canonical Structure SubF : Functor (op C) SetCat :=
  {|F0 Z := SubObject Z
  ; F1 Y X f := {| func := Sub_fmap f |}
  |}.
Next Obligation. intros r s [[rs Hrs] [sr Hsr]].
  split.
  - exists (pb (pb1 f r) (rs ∘ pb2 f r)). simpl. carw.
    rewrite <- axiom_comp_assoc, <- Hrs. cato.
  - exists (pb (pb1 f s) (sr ∘ pb2 f s)). simpl. carw.
    rewrite <- axiom_comp_assoc, <- Hsr. cato.
Qed.
Next Obligation. intros f g Hfg s. simpl. split.
  exists (pb (Sub_fmap f s) (pb2 f s)). simpl.
  carw. rewrite <- Hfg. cato.
  exists (pb (Sub_fmap g s) (pb2 g s)). simpl.
  carw. rewrite Hfg. cato.
Qed.
Next Obligation.
  intros s. simpl. split.
  exists (pb2 id s). simpl.
  rewrite <- (axiom_id_l (pb1 _ _)). cato.
  exists (pb s id). simpl. carw.
Qed.
Next Obligation.
  intros s. simpl. split.
  - exists (pb #pb1 (pb (f ∘ #pb1) #pb2)). simpl.
    carw. rewrite <- axiom_pb_cond. cacr.
  - exists (pb #pb1 (#pb2 ∘ #pb2)). simpl.
    carw. cacr. rewrite axiom_pb_cond.
    cacl. cacl. rewrite axiom_pb_cond. cato.
Qed.

End Sub.



(** * Sub-object Classifier

   sX ------> s0
    v          v
    |          |
    |          |
    |          |
    v          v
    X ------> SubOC *)

Class HasSubObjectClassifier `(C : Cat) `(!HasTerminal C) :=
  { SubOC : Ob
  ; truth : Hom 1 SubOC
  ; char {X Y} : X ↣ Y → Hom Y SubOC

  ; axiom_sub {X Y} {m : Mono X Y}
    : is_unique (λ c, is_pullback (char m) truth X m !) (char m)
  }.

Notation Ω := SubOC.
Notation χ := char.

Section SubObjectClassifier.
Context `{C : Cat}.

Definition is_subobject_classifier (Ω : Ob) (Ω0 : Sub Ω)
  := ∀ A (A0 : Sub A), ∃ χ,
    is_unique (λ χ, ∃ a, is_pullback χ Ω0 A0 A0 a) χ.

Proposition sub_subobject_1 {Ω : Ob} {Ω0 : Sub Ω}
  : is_subobject_classifier Ω Ω0
    → is_terminal Ω0.
Proof. unfold is_subobject_classifier. intros HSubOC.
  intro A. specialize (HSubOC A id).
  destruct HSubOC as [χ [[v H1] H2]].
  exists v. split. auto. intros u _.
  destruct H1 as [H1 H3].
  assert (H4 : ∃ a, is_pullback (Ω0 ∘ u) Ω0 A id a).
  { exists u. split. cato. intros. exists q1.
    rewrite axiom_comp_assoc in H.
    apply sub_mono in H. split; cato.
    intros h [H4 H5]. rewrite axiom_id_l in H4. cato. }
  specialize (H2 (Ω0 ∘ u) H4).
  apply (sub_mono _ Ω0).
  rewrite H2. rewrite axiom_id_r in H1. rewrite H1.
  reflexivity.
Qed.



Context `{!HasTerminal C}.
Context `{!HasSubObjectClassifier C _}.

Theorem SubOC_subobject_classifier
  : is_subobject_classifier Ω truth.
Proof. intros A A0. exists (χ A0). split.
  exists !. apply axiom_sub.
  intros. apply axiom_sub. apply axiom_sub.
Qed.

End SubObjectClassifier.
