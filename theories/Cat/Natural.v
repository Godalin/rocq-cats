From Cats Require Import Cat.Core.
From Cats Require Import Cat.Functor.
From Cats Require Import Cat.Set.



(** * Natural Transformations *)

Class Nat {C D : Cat} (F G : Functor C D) := mkNat
  { nt (X : @Ob C) :> (@Hom D) (F X) (G X)

  ; axiom_naturality
    : ∀ X Y : @Ob C, ∀ f : Hom X Y,
      nt Y ∘ fmap F f ≈ fmap G f ∘ nt X
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

Program Instance NatEq_Equivalence {C D F G}
  : Equivalence (@NatEq C D F G).
Next Obligation. repeat intro. cato. Qed.
Next Obligation. repeat intro. symmetry. apply H. Qed.
Next Obligation. repeat intro. transitivity (y X); auto. Qed.

Definition is_NatIso_of {C D : Cat} (F G : Functor C D)
    (α : F => G) : Prop
  := ∀ X, is_iso (α X).

Definition NatIso {C D : Cat} (F G : Functor C D)
  := ∃ α : F => G, is_NatIso_of F G α.

Infix "≅N" := NatIso
  (at level 50, no associativity).



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

Definition yo {C : Cat} (X : Ob) := λ Y, Hom Y X.
Notation "'Hom(-,'  X ')'" := (yo X).

Definition xo {C : Cat} (X : Ob) := λ Y, Hom X Y.
Notation "'Hom(' X  ',-)'" := (xo X).

Program Canonical Structure Hom_SetC
    {C : Cat} {X Y : Ob} : SetC :=
  {|carrier := Hom X Y |}.

Program Canonical Structure comp_l_resp {C : Cat}
    {X Y Z : Ob} {f : Hom Y Z} : FunS_resp (Hom X Y) (Hom X Z) :=
  {|func := f _* |}.

Program Canonical Structure comp_r_resp {C : Cat}
    {X Y Z : Ob} {f : Hom X Y} : FunS_resp (Hom Y Z) (Hom X Z) :=
  {|func := f ^* |}.
Next Obligation.
  intros g1 g2 Hg. unfold comp_pre. rewrite Hg. reflexivity.
Qed.

Program Canonical Structure xo_Functor {C : Cat} (X : Ob)
  : Functor C SetCat :=
  {|F0 := xo X
  ; F1 Y Y' (f : Hom Y Y') := f _*
  |}.
Next Obligation. intros f f' Hf g. simpl. rewrite Hf. cato. Qed.
Next Obligation. intros f. simpl. cato. Qed.
Next Obligation. intros x. simpl. apply axiom_comp_assoc. Qed.



(** Yoneda Lemma *)

Program Canonical Structure Nat_SetS {C D : Cat}
  (F G : Functor C D) :=
  {|carrier := F => G
  ; carrier_equiv := NatEq
  |} .

Section Yoneda.
Context `{C : Cat}.
Context {F : Functor C SetCat}.

Program Canonical Structure yoneda_func {X}
    : Nat (xo_Functor X) F →r F X
  := {| func α := α X id |}.
Next Obligation. intros a a' Ha.
  pose (HaX := Ha X id). cato.
Qed.

Program Canonical Structure yoneda_func_inv {X}
    : F X →r Nat (xo_Functor X) F
  := {| func (x : F X) := {| nt Y := {| func f :=
        (fmap F f) x |} |} |}.
Next Obligation.
  intros f f' Hf.
  assert (H : fmap F f ≈ fmap F f').
  { rewrite Hf. cato. }
  specialize (H x). cato.
Qed.
Next Obligation. intros g.
  assert (H : fmap F (f ∘ g) ≈ fmap F f ∘ fmap F g).
  { rewrite axiom_functor_comp. cato. }
  specialize (H x). cato.
Qed.
Next Obligation.
  intros a a' Ha Y. simpl.
  intros f. rewrite Ha. cato.
Qed.

Theorem yoneda_lemma_iso {X : @Ob C}
  : Nat (xo_Functor X) F ≅[SetCat] F X.
Proof. exists yoneda_func, yoneda_func_inv.
  split; simpl.
  - intros a Y. simpl. intros f.
    assert (fmap F f ∘ a X ≈ a Y ∘ fmap (xo_Functor X) f).
    { symmetry. apply axiom_naturality. }
    specialize (H id). rewrite H.
    simpl. rewrite axiom_id_r. cato.
  - intros x.
    assert (fmap F (@id X) ≈ id_resp).
    { rewrite axiom_functor_id. cato. }
    specialize (H x). cato.
Qed.

End Yoneda.
