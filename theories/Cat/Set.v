From Cats Require Import Cat.Core.

(** * Category of all Sets (Setoids in Rocq) *)

(** ** Sets in category: [SetC], as setoids *)

Record SetC :=
  { carrier :> Type
  ; carrier_equiv : crelation carrier
  ; carrier_setoid :: Equivalence carrier_equiv
  }.

Notation "[≈S]" := (carrier_equiv _).

Infix "≈S" := (carrier_equiv _)
  (at level 50) : cat_scope.

(** [Hom]-Sets are [SecC] *)

Program Canonical Hom_SetC {C : Cat} {X Y : Ob} : SetC :=
  {|carrier := Hom X Y
  ; carrier_equiv := HomEq
  |}.

(** *** [HomEq] for [SetC]

    The equivalence relation of function types
    between [SetC] are defined as point-wise equivalent.
    With this definition instead of [eq], the axiom of
    _functional extensionality_ is not required. *)

Definition  FunEq {X Y : SetC} (f g : X → Y)
  := ∀ x : X, f x ≈S g x.

Infix "≈f" := FunEq (at level 50).

Program Instance FunEq_Equivalence {X Y} : Equivalence (@FunEq X Y).
Next Obligation. intros f x. reflexivity. Qed.
Next Obligation. intros f g H x. symmetry. cato. Qed.
Next Obligation. intros f g h H1 H2 x. transitivity (g x); cato. Qed.

(** ** Functions between [SetC]

    Functions between [SetC] are those respecting
    setoid equivalence relations of its domain and codomain. *)

Record FunS_resp (X Y : SetC) :=
  { func :> carrier X → carrier Y
  ; func_proper
    :: Proper (carrier_equiv X ==> carrier_equiv Y) func
  }.

Infix "→r" := FunS_resp (at level 99).

(** ** [Hom]-Set of For [SetCat]

    Set of respective functions can be equipped with
    a canonical [SetC] structure. *)

Program Canonical FunS (X Y : SetC) : SetC :=
  {|carrier := X →r Y
  ; carrier_equiv := FunEq
  |}.
Next Obligation. split.
  - intros f x. reflexivity.
  - intros f g H x. symmetry. cato.
  - intros f g h H1 H2 x. transitivity (g x); cato.
Qed.

Infix "→S" := FunS (at level 99).

(** Identity & Composite Functions *)

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

(** [Hom]-Set Functions *)

Program Canonical comp_l_resp {C : Cat} {X Y Z : Ob}
    {f : Hom Y Z} : FunS_resp (Hom X Y) (Hom X Z) :=
  {|func := f _* |}.

Program Canonical comp_r_resp {C : Cat} {X Y Z : Ob}
    {f : Hom X Y} : FunS_resp (Hom Y Z) (Hom X Z) :=
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
  ; HomEq X Y := FunEq
  ; id _ := id_resp
  ; comp _ _ _ := comp_resp
  |}.
Next Obligation.
  intros f f' Hf g g' Hg x. simpl.
  rewrite (Hg x), (Hf (g' x)). reflexivity.
Qed.
Next Obligation. intros x. cato. Qed.
Next Obligation. intros x. cato. Qed.
Next Obligation. intros x. cato. Qed.



(** ** Other [SetC] constructions *)

(** *** Non-dependent products *)

Program Canonical ProdS (X Y : SetC) :=
  {|carrier := X * Y
  ; carrier_equiv := ProdEq [≈S] [≈S]
  |}.

Infix "×S" := ProdS (at level 40).

(** *** Dependent Functions (Indexed Set Families) *)

Definition PiEq {X : SetC} {Y : X → SetC} : crelation (∀ x : X, Y x)
  := λ f g, ∀ x : X, f x ≈S g x.

Infix "≈ΠS" := PiEq (at level 50).

Program Instance PiEq_Equivalence {X Y} : Equivalence (@PiEq X Y).
Next Obligation. intros f x. reflexivity. Qed.
Next Obligation. intros f g H x. symmetry. auto. Qed.
Next Obligation. intros f g h H1 H2 x. transitivity (g x); auto. Qed.

Program Canonical PiS (X : SetC) (Y : X → SetC) :=
  {|carrier := ∀ x : X, Y x
  ; carrier_equiv := PiEq
  |}.

(** *** Dependent Product/Sums *)

Inductive SigEq' {X : SetC} {Y : X → SetC} (x : X) (y : Y x)
    : ∀ (y : X), (Y y) → Type
  := SigEq_intro : ∀ {y'}, y ≈S y' → SigEq' x y x y'.

Definition SigEq {X : SetC} {Y : X → SetC} (a b : ∃ x : X, Y x)
  := SigEq' a.1 a.2 b.1 b.2.

Infix "≈ΣS" := SigEq (at level 50).

Program Instance SigEq_Symmetric {X Y} : Symmetric (@SigEq X Y).
Next Obligation. inversion X0; subst; simpl in *.
  constructor. simpl. rewrite <- X3. simpl. reflexivity.
Qed.

From Stdlib Require Import Equality.

Program Instance SigEq_Equivalence {X Y} : Equivalence (@SigEq X Y).
Next Obligation. intros x. constructor. reflexivity. Qed.
Next Obligation. intros [x Yx] [y Yy] [z Yz] H1 H2.
  inversion H1; simpl in *; subst.
  inversion H2; simpl in *; subst.
  dependent destruction H4; simpl in *; subst.
  dependent destruction H6; simpl in *; subst.
  constructor; simpl. transitivity Yy; cato.
Qed.

Program Canonical SigS (X : SetC) (Y : X → SetC) :=
  {|carrier := ∃ x : X, Y x
  ; carrier_equiv := SigEq
  |}.
