From Cats Require Import Cat.Core Cat.Functor Cat.Arrow Cat.Pullback Cat.Fibration.

(** * Cartesian Squares and Pullbacks *)

Section CartesianSquares.
Context {C : Cat}.

Definition arrow_pullback_cartesian {A B : ArrowOb C} (f : ArrowHom A B)
    (HP : is_pullback (arrow_bottom f) (arrow_map B)
      (arrow_dom A) (arrow_map A) (arrow_top f))
  : f ⦂ cartesian(ArrowCodF C).
Proof.
  intros D g u H.
  assert (Hcone : arrow_bottom f ∘ (u ∘ arrow_map D) ≈
      arrow_map B ∘ arrow_top g).
  { rewrite <- comp_assoc, H. symmetry. apply arrow_comm. }
  destruct (snd HP (arrow_dom D) (u ∘ arrow_map D) (arrow_top g) Hcone)
    as [h [[Hh1 Hh2] Hhu]].
  pose (k := ({| arrow_top := h; arrow_bottom := u; arrow_comm := Hh1 |}
    : ArrowHom D A)).
  exists k. refine {| this := _; that := _ |}.
  - split; [reflexivity | split; [exact Hh2 | exact H]].
  - intros l [Hlbase [Hltop _]]. split; [| exact Hlbase].
    apply Hhu. split.
    + transitivity (arrow_bottom l ∘ arrow_map D).
      * apply arrow_comm.
      * rewrite Hlbase. reflexivity.
    + exact Hltop.
Defined.

(** Test cartesianness on the identity arrow of each cone's vertex. *)
Definition arrow_cartesian_pullback {A B : ArrowOb C} (f : ArrowHom A B)
    (Hf : f ⦂ cartesian(ArrowCodF C))
  : is_pullback (arrow_bottom f) (arrow_map B)
      (arrow_dom A) (arrow_map A) (arrow_top f).
Proof.
  split; [symmetry; apply arrow_comm |].
  intros Q q1 q2 Hq.
  pose (g := arrow_from_identity B (arrow_bottom f ∘ q1) q2 (symmetry Hq)).
  destruct (Hf (IdentityArrow Q) g q1 (reflexivity (arrow_bottom f ∘ q1)))
    as [k [[Hkb [Hkt _]] Hku]].
  exists (arrow_top k). refine {| this := _; that := _ |}.
  - split.
    + transitivity (arrow_bottom k ∘ id).
      * exact (arrow_comm k).
      * rewrite comp_id_r. exact Hkb.
    + exact Hkt.
  - intros l [Hl1 Hl2].
    pose (j := arrow_from_identity A q1 l Hl1).
    exact (fst (Hku j (reflexivity q1, (Hl2, reflexivity (arrow_bottom f ∘ q1))))).
Defined.

Theorem arrow_cartesian_iff_pullback {A B : ArrowOb C} (f : ArrowHom A B)
  : f ⦂ cartesian(ArrowCodF C) ↔
    is_pullback (arrow_bottom f) (arrow_map B)
      (arrow_dom A) (arrow_map A) (arrow_top f).
Proof. split; [apply arrow_cartesian_pullback | apply arrow_pullback_cartesian]. Defined.

End CartesianSquares.

(** ** From Chosen Pullbacks to Chosen Cartesian Lifts *)

Section PullbackLifts.
Context {C : Cat} `{HPb : !HasPullback C}.

Program Definition ArrowReindexOb (B : ArrowOb C) {X : @Ob C}
    (σ : Hom X (arrow_cod B)) : ArrowOb C :=
  {| arrow_dom := Pb σ (arrow_map B)
   ; arrow_cod := X
   ; arrow_map := pb1 σ (arrow_map B) |}.

Program Definition arrow_reindex (B : ArrowOb C) {X : @Ob C}
    (σ : Hom X (arrow_cod B)) : ArrowHom (ArrowReindexOb B σ) B :=
  {| arrow_top := pb2 σ (arrow_map B); arrow_bottom := σ |}.
Next Obligation. symmetry. apply pullback_comm. Defined.

Definition arrow_reindex_cartesian (B : ArrowOb C) {X : @Ob C}
    (σ : Hom X (arrow_cod B)) : arrow_reindex B σ ⦂ cartesian(ArrowCodF C) :=
  arrow_pullback_cartesian (arrow_reindex B σ) pullback_universal.

(** This choice is enabled explicitly, not registered by import. *)
Program Definition ArrowCodF_HasCartesianLift : HasCartesianLift (ArrowCodF C) :=
  {| CartesianLift B X σ := ArrowReindexOb B σ
   ; cartesian_lift_base B X σ := eq_refl
   ; cartesian_lift B X σ := arrow_reindex B σ |}.
Next Obligation. symmetry. apply comp_id_r. Defined.
Next Obligation. apply arrow_reindex_cartesian. Defined.

End PullbackLifts.

Notation "B '[' σ ']Arr'" := (ArrowReindexOb B σ)
  (at level 8, left associativity, format "B [ σ ]Arr") : cat_scope.

(** ** From Chosen Cartesian Lifts to Chosen Pullbacks *)

Section LiftPullbacks.
Context {C : Cat} `{HL : !HasCartesianLift (ArrowCodF C)}.

Definition ArrowPullback {X Y Z : @Ob C} (f : Hom X Z) (g : Hom Y Z) : ArrowOb C :=
  f^*[ArrowCodF C] {| arrow_dom := Y; arrow_cod := Z; arrow_map := g |}.

Definition arrow_pullback_pr1 {X Y Z : @Ob C} (f : Hom X Z) (g : Hom Y Z)
  : Hom (arrow_dom (ArrowPullback f g)) X :=
  eq_to_hom (cartesian_lift_base (P := ArrowCodF C)
      (Y := {| arrow_dom := Y; arrow_cod := Z; arrow_map := g |}) f)
    ∘ arrow_map (ArrowPullback f g).

Definition arrow_pullback_pr2 {X Y Z : @Ob C} (f : Hom X Z) (g : Hom Y Z)
  : Hom (arrow_dom (ArrowPullback f g)) Y :=
  arrow_top (cartesian_lift (P := ArrowCodF C)
    (Y := {| arrow_dom := Y; arrow_cod := Z; arrow_map := g |}) f).

Definition arrow_pullback_universal {X Y Z : @Ob C} (f : Hom X Z) (g : Hom Y Z)
  : is_pullback f g (arrow_dom (ArrowPullback f g))
      (arrow_pullback_pr1 f g) (arrow_pullback_pr2 f g).
Proof.
  pose (B := {| arrow_dom := Y; arrow_cod := Z; arrow_map := g |}).
  pose (e := cartesian_lift_base (P := ArrowCodF C) (Y := B) f).
  eapply (pullback_base_iso (eq_to_hom e)).
  - exists (eq_to_hom (eq_sym e)). split.
    + apply eq_to_hom_inv_l.
    + apply eq_to_hom_inv_r.
  - exact (cartesian_lift_comm (P := ArrowCodF C) (Y := B) f).
  - exact (arrow_cartesian_pullback (cartesian_lift (P := ArrowCodF C) (Y := B) f)
      (cartesian_lift_universal (P := ArrowCodF C) (Y := B) f)).
Defined.

(** The recovered pullback structure is also an explicit choice. *)
Program Definition ArrowCodF_HasPullback : HasPullback C :=
  {| Pb X Y Z f g := arrow_dom (ArrowPullback f g)
   ; pb1 X Y Z := arrow_pullback_pr1
   ; pb2 X Y Z := arrow_pullback_pr2
   ; pullback_universal X Y Z := arrow_pullback_universal |}.

End LiftPullbacks.

(** A constructive equivalence of availability of chosen structures.
    No equality of the choices, their objects or their proof fields is asserted. *)
Theorem pullbacks_iff_arrow_cartesian_lifts (C : Cat)
  : HasPullback C ↔ HasCartesianLift (ArrowCodF C).
Proof.
  split.
  - intros HPb. exact (@ArrowCodF_HasCartesianLift C HPb).
  - intros HL. exact (@ArrowCodF_HasPullback C HL).
Defined.
