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
Qed.

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

(** The double-opposite comparison is natural in the category. *)
Program Definition OpInvolutionN : (OpCatF ∘F OpCatF) => (@IdF CatCat) :=
  {| nt C := FromDoubleOpF (C := C) |}.
Next Obligation.
  exists (λ A, eq_refl). intros A B u. simpl. carw.
Qed.

Definition op_involution_nat_iso : (OpCatF ∘F OpCatF) ≅N (@IdF CatCat).
Proof.
  exists OpInvolutionN. intros C. exact (op_involution C).2.
Defined.
