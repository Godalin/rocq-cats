From Stdlib Require Import SetoidClass.
From Cats Require Import Cat.Core.

Record SetC :=
  { carrier :> Type
  ; carrier_equiv : carrier → carrier → Prop
  ; carrier_setoid :: Equivalence carrier_equiv
  }.

Infix "≈S" := (carrier_equiv _)
  (at level 50) : cat_scope.

Definition  FunEq {X Y : SetC} (f g : X → Y) : Prop
  := ∀ x : X, f x ≈S g x.

Infix "≈f" := FunEq (at level 50).

Record FunS_resp (X Y : SetC) :=
  { func :> carrier X → carrier Y
  ; func_proper
    :: Proper (carrier_equiv X ==> carrier_equiv Y) func
  }.

Infix "→r" := FunS_resp (at level 99).

Program Canonical Structure FunS (X Y : SetC) : SetC :=
  {|carrier := carrier X → carrier Y
  ; carrier_equiv := FunEq
  |}.
Next Obligation. split.
  - intros f x. reflexivity.
  - intros f g H x. symmetry. cato.
  - intros f g h H1 H2 x. transitivity (g x); cato.
Qed.

Infix "→S" := FunS (at level 99).



Program Definition id_resp {X} : X →r X :=
  {|func (x : X) := x |}.
Next Obligation. intros x x' Hx. auto. Qed.

Program Definition comp_resp {X Y Z}
    (f : Y →r Z) (g : X →r Y) : X →r Z :=
  {|func (x : X) := f (g x) |}.
Next Obligation. intros x x' Hx'.
  rewrite Hx'. reflexivity.
Qed.

Infix "∘r" := comp_resp (at level 50).

Program Instance SetCat : Cat :=
  {|Ob := SetC
  ; Hom X Y := X →r Y
  ; HomEq X Y f g := FunEq f g
  ; id _ := id_resp
  ; comp _ _ _ := comp_resp
  |}.
Next Obligation. split. split.
  - intros f x. cato.
  - intros f g H x. symmetry. cato.
  - intros f g h H1 H2 x. transitivity (g x); auto.
Qed.
Next Obligation.
  intros f f' Hf g g' Hg x. simpl.
  rewrite (Hg x), (Hf (g' x)). reflexivity.
Qed.
Next Obligation. intros x. cato. Qed.
Next Obligation. intros x. cato. Qed.
Next Obligation. intros x. cato. Qed.
