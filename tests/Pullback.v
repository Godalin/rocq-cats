From Cats Require Import Cat.Core Cat.Set Cat.Pullback.

(** A concrete fixture: equality compares the two legs, not the proofs that
    the square commutes. In particular, no proof irrelevance is needed. *)
Definition pullback_setoid {X Y Z : SetC} (f : X →r Z) (g : Y →r Z) : SetC.
Proof.
  refine {| carrier := ∃ x : X, ∃ y : Y, f x ≈S g y
          ; carrier_equiv u v := u.1 ≈S v.1 ∧ u.2.1 ≈S v.2.1 |}.
  split.
  - intros u. split; reflexivity.
  - intros u v [H1 H2]. split; symmetry; assumption.
  - intros u v w [H1 H2] [H3 H4]. split; etransitivity; eassumption.
Defined.

Definition set_pb1 {X Y Z : SetC} (f : X →r Z) (g : Y →r Z)
    : pullback_setoid f g →r X.
Proof.
  unshelve refine (@Build_FunS_resp (pullback_setoid f g) X (fun u => u.1) _).
  intros u v [H1 H2]. exact H1.
Defined.

Definition set_pb2 {X Y Z : SetC} (f : X →r Z) (g : Y →r Z)
    : pullback_setoid f g →r Y.
Proof.
  unshelve refine (@Build_FunS_resp (pullback_setoid f g) Y (fun u => u.2.1) _).
  intros u v [H1 H2]. exact H2.
Defined.

Definition set_pb {X Y Z P : SetC} {f : X →r Z} {g : Y →r Z}
    (p1 : P →r X) (p2 : P →r Y) (HP : f ∘ p1 ≈ g ∘ p2)
    : P →r pullback_setoid f g.
Proof.
  unshelve refine (@Build_FunS_resp P (pullback_setoid f g)
    (fun u => existT _ (p1 u) (existT _ (p2 u) (HP u))) _).
  intros u v Huv. split; apply func_proper; exact Huv.
Defined.

Definition set_pullbacks : HasPullback SetCat.
Proof.
  refine {| Pb := fun X Y Z f g => pullback_setoid f g
          ; pb1 := fun X Y Z f g => set_pb1 f g
          ; pb2 := fun X Y Z f g => set_pb2 f g
          ; pb := fun X Y Z f g P p1 p2 HP => set_pb p1 p2 HP |}.
  - intros X Y Z f g u. exact u.2.2.
  - intros X Y Z f g P p1 p2 HP. split.
    + split; intros u; reflexivity.
    + intros k [H1 H2] u. split; [exact (H1 u) | exact (H2 u)].
Defined.

Definition unit_setoid : SetC :=
  {| carrier := unit; carrier_equiv := @eq unit |}.

Definition bool_setoid : SetC :=
  {| carrier := bool; carrier_equiv := @eq bool |}.

Definition true_map : unit_setoid →r bool_setoid.
Proof. refine (@Build_FunS_resp unit_setoid bool_setoid (fun _ => true) _). Defined.

Definition false_map : unit_setoid →r bool_setoid.
Proof. refine (@Build_FunS_resp unit_setoid bool_setoid (fun _ => false) _). Defined.

(** The legs of this cone do not commute. *)
Example noncommuting_cone
  : true_map ∘ id_resp ≈ false_map ∘ id_resp → Empty_set.
Proof. intros H. specialize (H tt). discriminate H. Qed.

Example empty_pullback
  : @Pb SetCat set_pullbacks unit_setoid unit_setoid bool_setoid
      true_map false_map → Empty_set.
Proof. intros [x [y H]]. discriminate H. Qed.

Example no_mediator_from_unit
  : (unit_setoid →r @Pb SetCat set_pullbacks unit_setoid unit_setoid
      bool_setoid true_map false_map) → Empty_set.
Proof. intros k. exact (empty_pullback (k tt)). Qed.

(** Previously, the application below had the declared morphism type and
    supplied a point of the empty pullback. Now it still needs a witness. *)
Fail Definition mediator_without_commutativity
    : unit_setoid →r @Pb SetCat set_pullbacks unit_setoid unit_setoid
        bool_setoid true_map false_map :=
  @pb SetCat set_pullbacks unit_setoid unit_setoid bool_setoid
    true_map false_map unit_setoid id_resp id_resp.

(** Changing the commutativity witness requires no equality of proofs. *)
Example mediator_witness_independence
    {X Y Z P : SetC} {f : X →r Z} {g : Y →r Z}
    (p1 : P →r X) (p2 : P →r Y)
    (HP HQ : f ∘ p1 ≈ g ∘ p2)
  : @pb SetCat set_pullbacks X Y Z f g P p1 p2 HP
      ≈ @pb SetCat set_pullbacks X Y Z f g P p1 p2 HQ.
Proof. apply pb_witness_independent. Qed.

Print Assumptions set_pullbacks.
Print Assumptions no_mediator_from_unit.
Print Assumptions mediator_witness_independence.
