From Cats Require Import Cat.Core.
From Cats Require Import Cat.Functor.



(** * Natural Transformations *)

Class Nat {C D : Cat} (F G : Functor C D) := mkNat
  { nt (X : @Ob C) :> (@Hom D) (F X) (G X)

  ; nt_naturality
    : ∀ X Y : @Ob C, ∀ f : Hom X Y,
      nt Y ∘ fmap F f ≈ fmap G f ∘ nt X
  }.

Arguments mkNat {_ _ _ _} _ _.
Arguments nt {_ _ _ _} _ _.
Arguments nt_naturality {_ _ _ _} _ {_ _} _.

Notation "F => G" := (Nat F G)
  (at level 50, no associativity) : type_scope.

Definition NatEq {C D : Cat} {F G : Functor C D} (α β : F => G)
  := ∀ X, α X ≈ β X.

Infix "≈N" := NatEq
  (at level 50, no associativity).

Program Instance NatEq_Equivalence {C D F G}
  : Equivalence (@NatEq C D F G).
Next Obligation. repeat intro. cato. Qed.
Next Obligation. repeat intro. symmetry. apply X. Qed.
Next Obligation. repeat intro. transitivity (y X1); auto. Qed.

Definition is_NatIso_of {C D : Cat} (F G : Functor C D)
    (α : F => G) : Type
  := ∀ X, is_iso (α X).

Definition NatIso {C D : Cat} (F G : Functor C D)
  := ∃ α : F => G, is_NatIso_of F G α.

Notation "α '⦂' F '≅N' G" := (is_NatIso_of F G α)
  (at level 50, no associativity,
    F at level 49, G at level 49) : cat_scope.

Infix "≅N" := NatIso
  (at level 50, no associativity) : cat_scope.

Program Definition NatIso_inv {C D : Cat} {F G : Functor C D}
    (α : F => G) (Niso : is_NatIso_of F G α) : G => F
  := {| nt := λ X, (Niso X).1 |}.
Next Obligation.
  pose (Hid := λ X, (Niso X).2).
  simpl in Hid.
  rewrite <- comp_id_r. cacr.
  rewrite <- (snd (Hid X)).
  cacl (fmap G f). rewrite <- nt_naturality.
  cacl. cacl. rewrite (fst (Hid Y)). carw.
Qed.

Notation "α '^-1N'" := (NatIso_inv α).

Proposition NatIso_inv_NatIso {C D : Cat} {F G : Functor C D} (α : F => G)
  (Niso : α ⦂ F ≅N G) : (α ^-1N Niso) ⦂ G ≅N F.
Proof. intro X. exists (α X). apply is_inv_of_comm.
  simpl. apply (Niso X).2.
Defined.

Program Instance nt_id {C D : Cat} {F : Functor C D} : F => F
  := { nt _ := id }.
Next Obligation.
  rewrite comp_id_l.
  rewrite comp_id_r.
  reflexivity.
Qed.

Program Instance nt_comp_v {C D : Cat} {F G H : Functor C D}
    (α : G => H) (β : F => G) : F => H
  := { nt X := (α X) ∘ (β X) }.
Next Obligation.
  rewrite comp_assoc.
  rewrite (nt_naturality β f).
  rewrite <- (comp_assoc) at 1.
  rewrite (nt_naturality α f).
  rewrite comp_assoc.
  reflexivity.
Qed.

Notation idN := nt_id.

Infix "∘Nv" := nt_comp_v
  (at level 51, right associativity).



(** ** The Functor Category *)

Program Instance Fct (C D : Cat) : Cat :=
  { Ob := Functor C D
  ; Hom F G := F => G
  ; HomEq _ _ := NatEq
  ; id _ := idN
  ; comp _ _ _ := nt_comp_v
  }.
Next Obligation.
  intros a a' Ha b b' Hb O.
  simpl. rewrite (Ha O), (Hb O). cato.
Qed.
Next Obligation. intros O. simpl. cato. Qed.
Next Obligation. intros O. simpl. cato. Qed.
Next Obligation. intros O; simpl.
  rewrite comp_assoc. cato.
Qed.

Section Fct.
Context {C D : Cat} {F G : Functor C D}.

Theorem iso_NatIso : F ≅[Fct C D] G ↔ F ≅N G.
Proof. split.
  - intros (a & b & H1 & H2); simpl in *.
    exists a. intros X. exists (b X). simpl. split; cato.
  - intros [a H]. exists a. exists (a ^-1N H).
    split; simpl; intro X; apply (H X).2.
Qed.

End Fct.

Definition NatIso_is_iso {C D : Cat} {F G : Functor C D}
    (α : F => G) (Hα : α ⦂ F ≅N G) : @is_iso (Fct C D) F G α.
Proof.
  exists (α ^-1N Hα). split; intros X.
  - exact (fst (Hα X).2).
  - exact (snd (Hα X).2).
Defined.

(** An inverse in the functor category gives component inverses directly. *)
Definition is_iso_NatIso {C D : Cat} {F G : Functor C D}
    (α : F => G) (Hα : @is_iso (Fct C D) F G α) : α ⦂ F ≅N G.
Proof.
  intros X. exists (Hα.1 X). split.
  - exact ((fst Hα.2) X).
  - exact ((snd Hα.2) X).
Defined.

(** ** Functors Compared by Natural Isomorphism

    The comparison retains its natural transformation and component inverses.
    It imposes no Rocq equality on objects or on functor-law proofs. *)

Definition nt_id_NatIso {C D : Cat} (F : Functor C D)
  : idN ⦂ F ≅N F.
Proof. intros X. exists id. split; cbn; apply comp_id_l. Defined.

Definition nt_comp_v_NatIso {C D : Cat} {F G H : Functor C D}
    (β : G => H) (α : F => G) (Hβ : β ⦂ G ≅N H) (Hα : α ⦂ F ≅N G)
  : (β ∘Nv α) ⦂ F ≅N H.
Proof.
  intros X. exists ((Hα X).1 ∘ (Hβ X).1). split; cbn.
  - rewrite comp_assoc, <- (comp_assoc (Hβ X).1), (fst (Hβ X).2), comp_id_l.
    exact (fst (Hα X).2).
  - rewrite comp_assoc, <- (comp_assoc (α X)), (snd (Hα X).2), comp_id_l.
    exact (snd (Hβ X).2).
Defined.

Global Instance NatIso_Equivalence {C D : Cat} : Equivalence (@NatIso C D).
Proof.
  split.
  - intros F. exists idN. apply nt_id_NatIso.
  - intros F G [α Hα]. exists (α ^-1N Hα). apply NatIso_inv_NatIso.
  - intros F G H [α Hα] [β Hβ]. exists (β ∘Nv α).
    exact (nt_comp_v_NatIso β α Hβ Hα).
Defined.

(** Whiskering applies a functor to a natural transformation, or evaluates
    that transformation after another functor. *)
Program Definition nt_whisker_l {C D E : Cat} (G : Functor D E)
    {F F' : Functor C D} (α : F => F') : (G ∘F F) => (G ∘F F') :=
  {| nt X := fmap G (α X) |}.
Next Obligation.
  rewrite <- (@functor_comp D E G _ _ _ (α Y) (fmap F f)),
    <- (@functor_comp D E G _ _ _ (fmap F' f) (α X)).
  apply functor_fmap_proper. apply nt_naturality.
Qed.

Program Definition nt_whisker_r {C D E : Cat} {G G' : Functor D E}
    (β : G => G') (F : Functor C D) : (G ∘F F) => (G' ∘F F) :=
  {| nt X := β (F X) |}.
Next Obligation. apply nt_naturality. Qed.

Infix "∘Nl" := nt_whisker_l (at level 51, right associativity) : cat_scope.
Infix "∘Nr" := nt_whisker_r (at level 51, right associativity) : cat_scope.

Global Instance nt_whisker_l_proper {C D E : Cat} (G : Functor D E)
    {F F' : Functor C D}
  : Proper (NatEq ==> NatEq) (@nt_whisker_l C D E G F F').
Proof.
  intros α β H X. change (fmap G (α X) ≈ fmap G (β X)).
  apply functor_fmap_proper. exact (H X).
Qed.

Global Instance nt_whisker_r_proper {C D E : Cat} {G G' : Functor D E}
    (F : Functor C D)
  : Proper (NatEq ==> NatEq) (λ β : G => G', β ∘Nr F).
Proof. intros α β H X. exact (H (F X)). Qed.

Definition nt_whisker_l_NatIso {C D E : Cat} (G : Functor D E)
    {F F' : Functor C D} (α : F => F') (Hα : α ⦂ F ≅N F')
  : (G ∘Nl α) ⦂ (G ∘F F) ≅N (G ∘F F').
Proof. intros X. exact (functor_is_iso G (α X) (Hα X)). Defined.

Definition nt_whisker_r_NatIso {C D E : Cat} {G G' : Functor D E}
    (β : G => G') (F : Functor C D) (Hβ : β ⦂ G ≅N G')
  : (β ∘Nr F) ⦂ (G ∘F F) ≅N (G' ∘F F).
Proof. intros X. exact (Hβ (F X)). Defined.

(** ** Horizontal Composition *)

Definition nt_comp_h {C D E : Cat} {G G' : Functor D E} {F F' : Functor C D}
    (β : G => G') (α : F => F') : (G ∘F F) => (G' ∘F F') :=
  (β ∘Nr F') ∘Nv (G ∘Nl α).

Infix "∘Nh" := nt_comp_h (at level 50, left associativity) : cat_scope.

Theorem nt_comp_h_alt {C D E : Cat} {G G' : Functor D E} {F F' : Functor C D}
    (β : G => G') (α : F => F')
  : (β ∘Nh α) ≈N ((G' ∘Nl α) ∘Nv (β ∘Nr F)).
Proof. intros X. exact (nt_naturality β (α X)). Qed.

Global Instance nt_comp_h_proper {C D E : Cat}
    {G G' : Functor D E} {F F' : Functor C D}
  : Proper (NatEq ==> NatEq ==> NatEq) (@nt_comp_h C D E G G' F F').
Proof.
  intros β β' Hβ α α' Hα X.
  change (β (F' X) ∘ fmap G (α X) ≈ β' (F' X) ∘ fmap G (α' X)).
  apply comp_proper; [apply Hβ | apply functor_fmap_proper; apply Hα].
Qed.

Theorem nt_comp_h_id {C D E : Cat} (G : Functor D E) (F : Functor C D)
  : (idN (F := G) ∘Nh idN (F := F)) ≈N idN.
Proof.
  intros X. change (id ∘ fmap G (@id (F X)) ≈ @id (G (F X))).
  rewrite functor_id. apply comp_id_l.
Qed.

Theorem nt_comp_h_interchange {C D E : Cat}
    {G0 G1 G2 : Functor D E} {F0 F1 F2 : Functor C D}
    (β2 : G1 => G2) (β1 : G0 => G1) (α2 : F1 => F2) (α1 : F0 => F1)
  : ((β2 ∘Nv β1) ∘Nh (α2 ∘Nv α1)) ≈N
      ((β2 ∘Nh α2) ∘Nv (β1 ∘Nh α1)).
Proof.
  intros X.
  change ((β2 (F2 X) ∘ β1 (F2 X)) ∘ fmap G0 (α2 X ∘ α1 X) ≈
    (β2 (F2 X) ∘ fmap G1 (α2 X)) ∘ (β1 (F1 X) ∘ fmap G0 (α1 X))).
  rewrite functor_comp, !comp_assoc.
  rewrite <- (comp_assoc (β1 (F2 X))), (nt_naturality β1 (α2 X)).
  rewrite comp_assoc. reflexivity.
Qed.

(** Horizontal composition is a functor on the two hom-categories. *)
Program Definition CompNF (C D E : Cat)
  : Functor (Fct D E ×C Fct C D) (Fct C E) :=
  {| F0 p := fst p ∘F snd p
   ; F1 p q α := fst α ∘Nh snd α
   |}.
Next Obligation.
  intros [β α] [β' α'] [Hβ Hα].
  exact (nt_comp_h_proper β β' Hβ α α' Hα).
Defined.
Next Obligation. apply nt_comp_h_id. Defined.
Next Obligation. apply nt_comp_h_interchange. Defined.

Definition nt_comp_h_NatIso {C D E : Cat}
    {G G' : Functor D E} {F F' : Functor C D}
    (β : G => G') (α : F => F') (Hβ : β ⦂ G ≅N G') (Hα : α ⦂ F ≅N F')
  : (β ∘Nh α) ⦂ (G ∘F F) ≅N (G' ∘F F').
Proof.
  apply nt_comp_v_NatIso.
  - exact (nt_whisker_r_NatIso β F' Hβ).
  - exact (nt_whisker_l_NatIso G α Hα).
Defined.

Global Instance CompF_proper {C D E : Cat}
  : Proper (NatIso ==> NatIso ==> NatIso) (@CompF C D E).
Proof.
  intros G G' [β Hβ] F F' [α Hα].
  exists (β ∘Nh α). exact (nt_comp_h_NatIso β α Hβ Hα).
Defined.

Global Instance π1F_proper {C D E : Cat} (d : @Ob D)
  : Proper (NatIso ==> NatIso) (λ F : Functor (C ×C D) E, π1F F d).
Proof.
  intros F G [α Hα].
  unshelve notypeclasses refine (({| nt := _ |}); _).
  - exact (λ c, α (c, d)).
  - intros X Y f. exact (nt_naturality α (X := (X, d)) (Y := (Y, d)) (f, id)).
  - intros X. exact (Hα (X, d)).
Defined.

Global Instance π2F_proper {C D E : Cat} (c : @Ob C)
  : Proper (NatIso ==> NatIso) (λ F : Functor (C ×C D) E, π2F F c).
Proof.
  intros F G [α Hα].
  unshelve notypeclasses refine (({| nt := _ |}); _).
  - exact (λ d, α (c, d)).
  - intros X Y f. exact (nt_naturality α (X := (c, X)) (Y := (c, Y)) (id, f)).
  - intros X. exact (Hα (c, X)).
Defined.

(** The comparison components for the functor laws are identities, even
    when the functor records have different proof fields. *)
Program Definition CompF_id_l {C D : Cat} (F : Functor C D) : IdF ∘F F ≅N F :=
  ({| nt X := id |}; _).
Next Obligation. simpl. carw. Defined.
Next Obligation. intros X. exists id. split; cbn; apply comp_id_l. Defined.

Program Definition CompF_id_r {C D : Cat} (F : Functor C D) : F ∘F IdF ≅N F :=
  ({| nt X := id |}; _).
Next Obligation. simpl. carw. Defined.
Next Obligation. intros X. exists id. split; cbn; apply comp_id_l. Defined.

Program Definition CompF_assoc {B C D E : Cat}
    (H : Functor D E) (G : Functor C D) (F : Functor B C)
  : (H ∘F G) ∘F F ≅N H ∘F (G ∘F F) := ({| nt X := id |}; _).
Next Obligation. simpl. carw. Defined.
Next Obligation. intros X. exists id. split; cbn; apply comp_id_l. Defined.

(** ** Opposite Natural Transformations

    Components keep their underlying morphisms. Their direction, and the
    order of vertical composition, are reversed in the opposite category. *)

Program Definition nt_op {C D : Cat} {F G : Functor C D} (α : F => G)
  : OpF G => OpF F :=
  {| nt X := α X |}.
Next Obligation. symmetry. apply nt_naturality. Qed.

Notation "α '^opN'" := (nt_op α) (at level 35) : cat_scope.

Global Instance nt_op_proper {C D : Cat} {F G : Functor C D}
  : Proper (NatEq ==> NatEq) (@nt_op C D F G).
Proof. intros α β Hαβ X. exact (Hαβ X). Qed.

Theorem nt_op_id {C D : Cat} {F : Functor C D}
  : nt_op (idN (F := F)) ≈N idN.
Proof. intros X. reflexivity. Qed.

Theorem nt_op_comp_v {C D : Cat} {F G H : Functor C D}
    (β : G => H) (α : F => G)
  : (β ∘Nv α) ^opN ≈N (α ^opN ∘Nv β ^opN).
Proof. intros X. reflexivity. Qed.

Program Definition OpFctF {C D : Cat}
  : Functor ((Fct C D) ^op) (Fct (C ^op) (D ^op)) :=
  {| F0 := OpF; F1 F G α := nt_op α |}.
Next Obligation. apply nt_op_id. Qed.
Next Obligation. apply nt_op_comp_v. Qed.

Definition nt_op_NatIso {C D : Cat} {F G : Functor C D}
    (α : F => G) (Hα : α ⦂ F ≅N G) : α ^opN ⦂ OpF G ≅N OpF F.
Proof.
  intros X. exists (Hα X).1. split.
  - exact (snd (Hα X).2).
  - exact (fst (Hα X).2).
Defined.

Global Instance OpF_proper {C D : Cat} : Proper (NatIso ==> NatIso) (@OpF C D).
Proof.
  intros F G [α Hα]. symmetry. exists (α ^opN). exact (nt_op_NatIso α Hα).
Defined.

Program Definition OpF_id {C : Cat} : OpF (@IdF C) ≅N (@IdF (C ^op)) :=
  ({| nt X := id |}; _).
Next Obligation. simpl. carw. Defined.
Next Obligation. intros X. exists id. split; cbn; apply comp_id_l. Defined.

Program Definition OpF_comp {C D E : Cat} (G : Functor D E) (F : Functor C D)
  : OpF (G ∘F F) ≅N (OpF G ∘F OpF F) := ({| nt X := id |}; _).
Next Obligation. simpl. carw. Defined.
Next Obligation. intros X. exists id. split; cbn; apply comp_id_l. Defined.

Program Definition OpF_involution {C D : Cat} (F : Functor C D)
  : FromDoubleOpF ∘F (OpF (OpF F) ∘F ToDoubleOpF) ≅N F :=
  ({| nt X := id |}; _).
Next Obligation. simpl. carw. Defined.
Next Obligation. intros X. exists id. split; cbn; apply comp_id_l. Defined.
