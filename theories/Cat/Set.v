From Stdlib Require Import SetoidClass.
From Cats Require Import Cat.Core.



(** * Category of all Sets (Setoids in Rocq) *)

(** ** Sets in category: [SetC], as setoids *)

Record SetC :=
  { carrier :> Type
  ; carrier_equiv : carrier → carrier → Prop
  ; carrier_setoid :: Equivalence carrier_equiv
  }.

Infix "≈S" := (carrier_equiv _)
  (at level 50) : cat_scope.



(** Hom- [Sets] *)

Program Canonical Structure Hom_SetC
    {C : Cat} {X Y : Ob} : SetC :=
  {|carrier := Hom X Y
  ; carrier_equiv := HomEq
  |}.



(** The equivalence relation of function types
    between [SetC] are defined as point-wise equivalent.
    With this definition instead of [eq], the axiom of
    _functional extensionality_ is not required. *)

Definition  FunEq {X Y : SetC} (f g : X → Y) : Prop
  := ∀ x : X, f x ≈S g x.

Infix "≈f" := FunEq (at level 50).



(** ** Functions between [SetC]

    Functions between [SetC] are those respecting
    setoid equivalence relations of its domain and codomain. *)

Record FunS_resp (X Y : SetC) :=
  { func :> carrier X → carrier Y
  ; func_proper
    :: Proper (carrier_equiv X ==> carrier_equiv Y) func
  }.

Infix "→r" := FunS_resp (at level 99).



(** *** Set of Functions

    Set of respective functions can be equipped with
    a canonical [SetC] structure. *)

Program Canonical Structure FunS (X Y : SetC) : SetC :=
  {|carrier := X →r Y
  ; carrier_equiv := FunEq
  |}.
Next Obligation. split.
  - intros f x. reflexivity.
  - intros f g H x. symmetry. cato.
  - intros f g h H1 H2 x. transitivity (g x); cato.
Qed.

Infix "→S" := FunS (at level 99).



(** *** Identity & Composite Functions *)

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


(** Hom-Set Functions *)

Program Canonical Structure comp_l_resp {C : Cat}
    {X Y Z : Ob} {f : Hom Y Z} : FunS_resp (Hom X Y) (Hom X Z) :=
  {|func := f _* |}.

Program Canonical Structure comp_r_resp {C : Cat}
    {X Y Z : Ob} {f : Hom X Y} : FunS_resp (Hom Y Z) (Hom X Z) :=
  {|func := f ^* |}.
Next Obligation.
  intros g1 g2 Hg. unfold comp_pre. rewrite Hg. reflexivity.
Qed.



(** ** Category of [SetC]: [SetCat]

    [SetCat] can be used as a suitable category with similar
    role as _Set_ in ordinary mathematics. In the proof of
    _Yoneda lemma,_ [SetC] plays an important role. *)

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
