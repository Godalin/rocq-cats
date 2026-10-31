From Cats Require Import Cat.Core Cat.Slice Cat.Pullback Cat.Functor Cat.Natural.

(** * Base Change in Slice Categories

    Chosen pullbacks supply the objects. Their universal property supplies
    morphisms and comparisons, without equating commutativity witnesses. *)

Section SliceReindex.
Context {C : Cat} `{HP : !HasPullback C}.

Definition SliceReindexOb {X Y : @Ob C} (f : Hom X Y) (A : SliceOb C Y)
  : SliceOb C X :=
  {| slice_dom := Pb f (slice_arrow A)
   ; slice_arrow := pb1 f (slice_arrow A) |}.

Notation "A '[' f ']C'" := (SliceReindexOb f A)
  (at level 8, left associativity) : cat_scope.

Program Definition slice_reindex_lift {X Y : @Ob C} (f : Hom X Y)
    (A : SliceOb C Y) {B : SliceOb C X}
    (h : Hom (slice_dom B) (slice_dom A))
    (Hh : f ∘ slice_arrow B ≈ slice_arrow A ∘ h) : SliceHom B A[f]C :=
  {| slice_map := pb (slice_arrow B) h Hh |}.
Next Obligation. apply pb_β1. Defined.

Theorem slice_reindex_lift_β2 {X Y : @Ob C} (f : Hom X Y)
    (A : SliceOb C Y) {B : SliceOb C X}
    (h : Hom (slice_dom B) (slice_dom A))
    (Hh : f ∘ slice_arrow B ≈ slice_arrow A ∘ h)
  : pb2 f (slice_arrow A) ∘ slice_map (slice_reindex_lift f A h Hh) ≈ h.
Proof. apply pb_β2. Qed.

Theorem slice_reindex_lift_unique {X Y : @Ob C} (f : Hom X Y)
    (A : SliceOb C Y) {B : SliceOb C X}
    (h : Hom (slice_dom B) (slice_dom A))
    (Hh : f ∘ slice_arrow B ≈ slice_arrow A ∘ h) (k : SliceHom B A[f]C)
  : pb2 f (slice_arrow A) ∘ slice_map k ≈ h
    → slice_map k ≈ slice_map (slice_reindex_lift f A h Hh).
Proof. intros Hk. apply pb_η. split; [exact (slice_comm k) | exact Hk]. Qed.

Program Definition slice_reindex_map {X Y : @Ob C} (f : Hom X Y)
    {A B : SliceOb C Y} (h : SliceHom A B) : SliceHom A[f]C B[f]C :=
  slice_reindex_lift f B (B := A[f]C) (slice_map h ∘ pb2 f (slice_arrow A)) _.
Next Obligation.
  rewrite <- comp_assoc, (slice_comm h). apply pullback_comm.
Defined.

Theorem slice_reindex_map_β2 {X Y : @Ob C} (f : Hom X Y)
    {A B : SliceOb C Y} (h : SliceHom A B)
  : pb2 f (slice_arrow B) ∘ slice_map (slice_reindex_map f h)
      ≈ slice_map h ∘ pb2 f (slice_arrow A).
Proof. apply slice_reindex_lift_β2. Qed.

Program Definition SliceReindexF {X Y : @Ob C} (f : Hom X Y)
  : Functor (C /C Y) (C /C X) :=
  {| F0 := SliceReindexOb f
   ; F1 A B := slice_reindex_map f |}.
Next Obligation.
  intros h k H. unfold slice_reindex_map. cbn.
  apply pb_proper; [reflexivity | rewrite H; reflexivity].
Defined.
Next Obligation.
  unfold slice_reindex_map. cbn. symmetry. apply pb_η. split.
  - rewrite comp_id_r. reflexivity.
  - rewrite comp_id_r, comp_id_l. reflexivity.
Defined.
Next Obligation.
  unfold slice_reindex_map. cbn. symmetry. apply pb_η. split.
  - rewrite <- comp_assoc, !pb_β1. reflexivity.
  - rewrite <- comp_assoc, pb_β2, comp_assoc, pb_β2, <- comp_assoc. reflexivity.
Defined.

(** Any other pullback gives a specified isomorphism to the chosen one. *)
Definition slice_reindex_lift_iso {X Y : @Ob C} (f : Hom X Y)
    (A : SliceOb C Y) {B : SliceOb C X}
    (h : Hom (slice_dom B) (slice_dom A))
    (Hh : f ∘ slice_arrow B ≈ slice_arrow A ∘ h)
    (HB : is_pullback f (slice_arrow A) (slice_dom B) (slice_arrow B) h)
  : @is_iso (C /C X) _ _ (slice_reindex_lift f A h Hh).
Proof.
  destruct (snd HB _ (pb1 f (slice_arrow A)) (pb2 f (slice_arrow A))
    (pullback_comm (f := f) (g := slice_arrow A))) as [k [[Hk1 Hk2] Hku]].
  unshelve notypeclasses refine (({| slice_map := _; slice_comm := _ |}); _).
  - exact k.
  - exact Hk1.
  - split.
    + apply (pullback_hom_ext HB).
      * cbn. rewrite <- comp_assoc, Hk1, pb_β1, comp_id_r. reflexivity.
      * cbn. rewrite <- comp_assoc, Hk2, pb_β2, comp_id_r. reflexivity.
    + apply (pullback_hom_ext (pullback_universal (f := f) (g := slice_arrow A))).
      * cbn. rewrite <- comp_assoc, pb_β1, Hk1, comp_id_r. reflexivity.
      * cbn. rewrite <- comp_assoc, pb_β2, Hk2, comp_id_r. reflexivity.
Defined.

(** Identity and iterated base change are compared by specified isomorphisms. *)
Program Definition slice_reindex_id {X : @Ob C} (A : SliceOb C X)
  : SliceHom A A[id]C :=
  slice_reindex_lift id A (B := A) id _.
Next Obligation. carw. Defined.

Definition slice_reindex_id_iso {X : @Ob C} (A : SliceOb C X)
  : @is_iso (C /C X) _ _ (slice_reindex_id A) :=
  slice_reindex_lift_iso id A (B := A) id _ pullback_id.

Program Definition SliceReindexIdN (X : @Ob C)
  : (@IdF (C /C X)) => (SliceReindexF (@id X)) :=
  {| nt := slice_reindex_id |}.
Next Obligation.
  apply (pullback_hom_ext (pullback_universal (f := @id X) (g := slice_arrow Y))).
  - cbn. rewrite <- !comp_assoc, !pb_β1. apply slice_comm.
  - cbn. rewrite <- !comp_assoc, !pb_β2, comp_assoc, pb_β2. carw.
Defined.

Definition slice_reindex_id_nat_iso (X : @Ob C)
  : (@IdF (C /C X)) ≅N (SliceReindexF (@id X)) :=
  (SliceReindexIdN X; slice_reindex_id_iso).

Definition slice_reindex_comp_pullback {X Y Z : @Ob C}
    (f : Hom Y Z) (g : Hom X Y) (A : SliceOb C Z)
  : is_pullback (f ∘ g) (slice_arrow A) (slice_dom A[f]C[g]C)
      (slice_arrow A[f]C[g]C) (pb2 f (slice_arrow A) ∘ pb2 g (slice_arrow A[f]C)).
Proof.
  apply (pullback_comp (p1 := pb1 f (slice_arrow A))); apply pullback_universal.
Defined.

Definition slice_reindex_comp {X Y Z : @Ob C}
    (f : Hom Y Z) (g : Hom X Y) (A : SliceOb C Z)
  : SliceHom A[f]C[g]C A[f ∘ g]C :=
  slice_reindex_lift (f ∘ g) A (B := A[f]C[g]C)
    (pb2 f (slice_arrow A) ∘ pb2 g (slice_arrow A[f]C))
    (fst (slice_reindex_comp_pullback f g A)).

Definition slice_reindex_comp_iso {X Y Z : @Ob C}
    (f : Hom Y Z) (g : Hom X Y) (A : SliceOb C Z)
  : @is_iso (C /C X) _ _ (slice_reindex_comp f g A) :=
  slice_reindex_lift_iso (f ∘ g) A (B := A[f]C[g]C)
    (pb2 f (slice_arrow A) ∘ pb2 g (slice_arrow A[f]C))
    (fst (slice_reindex_comp_pullback f g A)) (slice_reindex_comp_pullback f g A).

Program Definition SliceReindexCompN {X Y Z : @Ob C} (f : Hom Y Z) (g : Hom X Y)
  : (SliceReindexF g ∘F SliceReindexF f)
      => (SliceReindexF (f ∘ g)) :=
  {| nt := slice_reindex_comp f g |}.
Next Obligation.
  apply (pullback_hom_ext (pullback_universal (f := f ∘ g) (g := slice_arrow Y0))).
  - cbn. repeat first [rewrite <- comp_assoc | rewrite pb_β1]. reflexivity.
  - cbn. repeat first [rewrite <- comp_assoc | rewrite pb_β2].
    rewrite !comp_assoc, pb_β2, <- !comp_assoc, pb_β2.
    rewrite !comp_assoc, pb_β2. reflexivity.
Defined.

Definition slice_reindex_comp_nat_iso {X Y Z : @Ob C} (f : Hom Y Z) (g : Hom X Y)
  : (SliceReindexF g ∘F SliceReindexF f)
      ≅N (SliceReindexF (f ∘ g)) :=
  (SliceReindexCompN f g; slice_reindex_comp_iso f g).

End SliceReindex.

Notation "A '[' f ']C'" := (SliceReindexOb f A)
  (at level 8, left associativity, format "A [ f ]C") : cat_scope.
