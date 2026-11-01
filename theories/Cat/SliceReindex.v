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

Notation "A '⟨' f ',' g '⟩C'" := (slice_reindex_comp f g A)
  (at level 8, left associativity, format "A ⟨ f ,  g ⟩C") : cat_scope.

Definition slice_reindex_comp_iso {X Y Z : @Ob C}
    (f : Hom Y Z) (g : Hom X Y) (A : SliceOb C Z)
  : @is_iso (C /C X) _ _ A⟨f, g⟩C :=
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

(** ** Equivalent Base Maps

    Maps into a reindexed slice object already agree on the first
    projection. The second projection therefore determines them uniquely. *)
Theorem slice_reindex_hom_ext {X Y : @Ob C} (f : Hom X Y) (A : SliceOb C Y)
    {B : SliceOb C X} {h k : SliceHom B A[f]C}
  : pb2 f (slice_arrow A) ∘ slice_map h ≈ pb2 f (slice_arrow A) ∘ slice_map k
    → slice_map h ≈ slice_map k.
Proof.
  intros H. apply (pullback_hom_ext (pullback_universal (f := f) (g := slice_arrow A))).
  - transitivity (slice_arrow B); [exact (slice_comm h) | symmetry; exact (slice_comm k)].
  - exact H.
Qed.

Program Definition slice_reindex_equiv {X Y : @Ob C} {f g : Hom X Y}
    (H : f ≈ g) (A : SliceOb C Y) : SliceHom A[f]C A[g]C :=
  slice_reindex_lift g A (B := A[f]C) (pb2 f (slice_arrow A)) _.
Next Obligation. rewrite <- H. apply pullback_comm. Defined.

Notation "A '⟦' H '⟧C'" := (slice_reindex_equiv H A)
  (at level 8, left associativity, format "A ⟦ H ⟧C") : cat_scope.

Theorem slice_reindex_equiv_β2 {X Y : @Ob C} {f g : Hom X Y}
    (H : f ≈ g) (A : SliceOb C Y)
  : pb2 g (slice_arrow A) ∘ slice_map A⟦H⟧C ≈ pb2 f (slice_arrow A).
Proof. apply slice_reindex_lift_β2. Qed.

Definition slice_reindex_equiv_iso {X Y : @Ob C} {f g : Hom X Y}
    (H : f ≈ g) (A : SliceOb C Y) : @is_iso (C /C X) _ _ A⟦H⟧C.
Proof.
  exists A⟦symmetry H⟧C. split; apply slice_reindex_hom_ext; cbn;
    rewrite <- comp_assoc, !pb_β2, comp_id_r; reflexivity.
Defined.

Program Definition SliceReindexEqN {X Y : @Ob C} {f g : Hom X Y} (H : f ≈ g)
  : SliceReindexF f => SliceReindexF g := {| nt := slice_reindex_equiv H |}.
Next Obligation.
  apply (pullback_hom_ext (pullback_universal (f := g) (g := slice_arrow Y0)));
    repeat first [rewrite <- comp_assoc | rewrite pb_β1 | rewrite pb_β2].
  - reflexivity.
  - rewrite comp_assoc, pb_β2. reflexivity.
Defined.

Definition slice_reindex_equiv_nat_iso {X Y : @Ob C} {f g : Hom X Y} (H : f ≈ g)
  : SliceReindexF f ≅N SliceReindexF g :=
  (SliceReindexEqN H; slice_reindex_equiv_iso H).

Global Instance SliceReindexF_proper {X Y : @Ob C}
  : Proper (HomEq ==> NatIso) (@SliceReindexF X Y).
Proof. intros f g H. exact (slice_reindex_equiv_nat_iso H). Defined.

Theorem slice_reindex_equiv_witness_independent {X Y : @Ob C} {f g : Hom X Y}
    (H K : f ≈ g) : SliceReindexEqN H ≈N SliceReindexEqN K.
Proof. intros A. apply slice_reindex_hom_ext. cbn. rewrite !pb_β2. reflexivity. Qed.

Theorem slice_reindex_equiv_id {X Y : @Ob C} {f : Hom X Y} (H : f ≈ f)
  : SliceReindexEqN H ≈N idN.
Proof.
  intros A. apply slice_reindex_hom_ext. cbn. rewrite pb_β2, comp_id_r. reflexivity.
Qed.

Theorem slice_reindex_equiv_comp {X Y : @Ob C} {f g h : Hom X Y}
    (H : f ≈ g) (K : g ≈ h) (L : f ≈ h)
  : SliceReindexEqN L ≈N (SliceReindexEqN K ∘Nv SliceReindexEqN H).
Proof.
  intros A. apply slice_reindex_hom_ext. cbn.
  repeat first [rewrite <- comp_assoc | rewrite pb_β2]. reflexivity.
Qed.

(** ** Unit and Composition Coherence

    All diagrams follow from pullback uniqueness. Base equations are
    equivalences and their witnesses need not be equal. *)
Theorem slice_reindex_comp_equiv {X Y Z : @Ob C}
    {f f' : Hom Y Z} {g g' : Hom X Y}
    (H : f ≈ f') (K : g ≈ g') (L : f ∘ g ≈ f' ∘ g') (A : SliceOb C Z)
  : slice_map (A⟦L⟧C ∘/C A⟨f, g⟩C) ≈
    slice_map (A⟨f', g'⟩C ∘/C A[f']C⟦K⟧C ∘/C
      slice_reindex_map g A⟦H⟧C).
Proof.
  apply slice_reindex_hom_ext. cbn.
  repeat first [rewrite <- comp_assoc | rewrite pb_β2].
  rewrite (comp_assoc (pb2 f' (slice_arrow A))), pb_β2,
    comp_assoc, pb_β2, <- comp_assoc, pb_β2. reflexivity.
Qed.

Theorem slice_reindex_unit_l {X Y : @Ob C} (f : Hom X Y)
    (H : id ∘ f ≈ f) (A : SliceOb C Y)
  : slice_map (A⟦H⟧C ∘/C A⟨id, f⟩C ∘/C
      slice_reindex_map f (slice_reindex_id A)) ≈ slice_map (slice_id A[f]C).
Proof.
  apply slice_reindex_hom_ext. cbn.
  repeat first [rewrite <- comp_assoc | rewrite pb_β2 | rewrite comp_id_l
    | rewrite comp_id_r].
  rewrite comp_assoc, pb_β2, <- comp_assoc, pb_β2, comp_id_l. reflexivity.
Qed.

Theorem slice_reindex_unit_r {X Y : @Ob C} (f : Hom X Y)
    (H : f ∘ id ≈ f) (A : SliceOb C Y)
  : slice_map (A⟦H⟧C ∘/C A⟨f, id⟩C ∘/C
      slice_reindex_id A[f]C) ≈ slice_map (slice_id A[f]C).
Proof.
  apply slice_reindex_hom_ext. cbn.
  repeat first [rewrite <- comp_assoc | rewrite pb_β2 | rewrite comp_id_l
    | rewrite comp_id_r].
  rewrite comp_assoc, pb_β2, comp_id_r. reflexivity.
Qed.

Theorem slice_reindex_assoc {X Y Z W : @Ob C}
    (f : Hom Z W) (g : Hom Y Z) (h : Hom X Y)
    (H : (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)) (A : SliceOb C W)
  : slice_map (A⟦H⟧C ∘/C A⟨f ∘ g, h⟩C ∘/C
      slice_reindex_map h A⟨f, g⟩C) ≈
    slice_map (A⟨f, g ∘ h⟩C ∘/C A[f]C⟨g, h⟩C).
Proof.
  apply slice_reindex_hom_ext. cbn.
  repeat first [rewrite <- comp_assoc | rewrite pb_β2].
  rewrite (comp_assoc (pb2 (f ∘ g) (slice_arrow A))), pb_β2,
    <- comp_assoc, pb_β2, <- comp_assoc, pb_β2,
    !(comp_assoc (pb2 f (slice_arrow A))), pb_β2. reflexivity.
Qed.

End SliceReindex.

Notation "A '[' f ']C'" := (SliceReindexOb f A)
  (at level 8, left associativity, format "A [ f ]C") : cat_scope.

Notation "A '⟦' H '⟧C'" := (slice_reindex_equiv H A)
  (at level 8, left associativity, format "A ⟦ H ⟧C") : cat_scope.

Notation "A '⟨' f ',' g '⟩C'" := (slice_reindex_comp f g A)
  (at level 8, left associativity, format "A ⟨ f ,  g ⟩C") : cat_scope.
