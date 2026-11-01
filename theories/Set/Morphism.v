From Cats.Set Require Export Core.

(** * Respectful Maps

    Function equality is pointwise equality in the codomain. It compares
    values, without comparing functions or respectfulness proofs by [eq]. *)

Definition FunEq {X Y : SetC} (f g : X → Y) := ∀ x : X, f x ≈S g x.

Infix "≈f" := FunEq (at level 50).

Program Instance FunEq_Equivalence {X Y} : Equivalence (@FunEq X Y).
Next Obligation. intros f x. reflexivity. Defined.
Next Obligation. intros f g H x. symmetry. apply H. Defined.
Next Obligation. intros f g h H1 H2 x. transitivity (g x); auto. Defined.

Record FunS_resp (X Y : SetC) :=
  { func :> carrier X → carrier Y
  ; func_proper :: Proper (carrier_equiv X ==> carrier_equiv Y) func
  }.

Infix "→r" := FunS_resp (at level 99).

Program Definition lift_resp@{v q +} {X Y : SetC} (f : X →r Y)
  : LiftS@{_ _ v q} X →r LiftS@{_ _ v q} Y :=
  {| func x := {| lower := f (lower x) |} |}.
Next Obligation.
  intros [x] [y] [H]. exact {| lower := @func_proper _ _ f x y H |}.
Defined.

Notation "f '^↑S'" := (lift_resp f) (at level 35) : set_scope.

Program Canonical FunS (X Y : SetC) : SetC :=
  {| carrier := X →r Y
   ; carrier_equiv := FunEq |}.
Next Obligation. split.
  - intros f x. reflexivity.
  - intros f g H x. symmetry. apply H.
  - intros f g h H1 H2 x. transitivity (g x); auto.
Defined.

Infix "→S" := FunS (at level 99).

Global Instance lift_resp_proper@{v q +} {X Y : SetC}
  : Proper (carrier_equiv (X →S Y) ==>
      carrier_equiv (LiftS@{_ _ v q} X →S LiftS@{_ _ v q} Y))
      (λ f, (f^↑S : LiftS@{_ _ v q} X →r LiftS@{_ _ v q} Y)).
Proof. intros f g H [x]. exact {| lower := H x |}. Defined.

Program Definition id_resp {X} : X →r X :=
  {| func (x : X) := x |}.
Next Obligation. intros x x' Hx. exact Hx. Defined.

Program Definition comp_resp {X Y Z} (f : Y →r Z) (g : X →r Y) : X →r Z :=
  {| func (x : X) := f (g x) |}.
Next Obligation. intros x x' Hx. rewrite Hx. reflexivity. Defined.

Infix "∘r" := comp_resp (at level 50).

Global Instance comp_resp_proper {X Y Z}
  : Proper (carrier_equiv (Y →S Z) ==> carrier_equiv (X →S Y)
      ==> carrier_equiv (X →S Z)) (@comp_resp X Y Z).
Proof.
  intros f f' Hf g g' Hg x. cbn.
  rewrite (Hg x), (Hf (g' x)). reflexivity.
Qed.

Theorem comp_resp_id_r {X Y} (f : X →r Y) : f ∘r id_resp ≈f f.
Proof. intros x. reflexivity. Qed.

Theorem comp_resp_id_l {X Y} (f : X →r Y) : id_resp ∘r f ≈f f.
Proof. intros x. reflexivity. Qed.

Theorem comp_resp_assoc {W X Y Z} (f : Y →r Z) (g : X →r Y) (h : W →r X)
  : ((f ∘r g) ∘r h) ≈f (f ∘r (g ∘r h)).
Proof. intros x. reflexivity. Qed.
