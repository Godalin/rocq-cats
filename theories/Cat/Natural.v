From Cats Require Import Cat.Core.
From Cats Require Import Cat.Functor.

(** * Natural Transformations *)

Class Nat {C D : Cat} (F G : Functor C D) := mkNat
  { nt (X : @Ob C) :> (@Hom D) (F X) (G X)

  ; axiom_naturality
    : ∀ X Y : @Ob C, ∀ f : Hom X Y,
      nt Y ∘ fmap f ≈ fmap f ∘ nt X
  }.

Arguments mkNat {_ _ _ _} _ _.
Arguments nt {_ _ _ _} _ _.
Arguments axiom_naturality {_ _ _ _} _ {_ _} _.

Notation "F => G" := (Nat F G)
  (at level 50, no associativity) : type_scope.

Definition NatEq {C D : Cat} {F G : Functor C D}
    (α β : F => G) : Prop
  := ∀ X, α X ≈ β X.

Infix "≈N" := NatEq
  (at level 50, no associativity).

Program Instance NatEq_Equivalence {C D F G} : Equivalence (@NatEq C D F G).
Next Obligation. repeat intro. cato. Qed.
Next Obligation. repeat intro. symmetry. apply H. Qed.
Next Obligation. repeat intro. transitivity (y X); auto. Qed.



Program Instance id_nt {C D : Cat} {F : Functor C D} : F => F
  := { nt _ := id }.
Next Obligation.
  rewrite axiom_id_l.
  rewrite axiom_id_r.
  reflexivity.
Qed.

Program Instance comp_nt_v {C D : Cat} {F G H : Functor C D}
    (α : G => H) (β : F => G) : F => H
  := { nt X := (nt α X) ∘ (nt β X) }.
Next Obligation.
  rewrite axiom_comp_assoc.
  rewrite (axiom_naturality β f).
  rewrite <- (axiom_comp_assoc) at 1.
  rewrite (axiom_naturality α f).
  rewrite axiom_comp_assoc.
  reflexivity.
Qed.

Notation idN := id_nt.

Infix "∘Nv" := comp_nt_v
  (at level 51, right associativity).



(** Functor Category *)

Program Instance Fct (C D : Cat) : Cat :=
  { Ob := Functor C D
  ; Hom F G := F => G
  ; HomEq _ _ := NatEq
  ; id _ := id_nt
  ; comp _ _ _ := comp_nt_v
  }.
Next Obligation. split. apply NatEq_Equivalence. Qed.
Next Obligation.
  intros a a' Ha b b' Hb O.
  simpl. rewrite (Ha O), (Hb O). cato.
Qed.
Next Obligation. intros O. simpl. cato. Qed.
Next Obligation. intros O. simpl. cato. Qed.
Next Obligation. intros O; simpl.
  rewrite axiom_comp_assoc. cato.
Qed.
