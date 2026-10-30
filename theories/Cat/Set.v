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

(** *** Raw Dependent Functions

    This pointwise setoid does not require sections to respect equivalent
    indices. Coherent families and their dependent sums are defined below. *)

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

(** *** Coherent Families over Setoids

    Transport is a respectful map. The laws compare its action on elements,
    never equality witnesses themselves. Quantifying over any witnesses of
    the same base equivalences expresses coherence over a setoid: the composite
    law accepts any witness r, and witness independence follows from it. *)

Record FamS (X : SetC) :=
  { fam :> X → SetC
  ; transpS {x y : X} : x ≈S y → fam x →r fam y
  ; axiom_transp_id {x} (p : x ≈S x) (v : fam x)
    : transpS p v ≈S v
  ; axiom_transp_comp {x y z} (p : x ≈S y) (q : y ≈S z) (r : x ≈S z)
      (v : fam x)
    : transpS r v ≈S transpS q (transpS p v)
  }.

Arguments transpS {_} _ {_ _} _.
Arguments axiom_transp_id {_} _ {_} _ _.
Arguments axiom_transp_comp {_} _ {_ _ _} _ _ _ _.

Theorem reflS {X : SetC} {x : X} : x ≈S x.
Proof. reflexivity. Qed.

(** Different witnesses induce equivalent maps; no proof irrelevance is used. *)
Theorem transpS_witness_independent {X} (Y : FamS X) {x y} (p q : x ≈S y)
  : transpS Y p ≈f transpS Y q.
Proof.
  intros v. assert (e : x ≈S x) by reflexivity.
  transitivity (transpS Y q (transpS Y e v)).
  - exact (axiom_transp_comp Y e q p v).
  - apply func_proper. apply axiom_transp_id.
Qed.

Theorem transpS_inverse {X} (Y : FamS X) {x y}
    (p : x ≈S y) (q : y ≈S x) (v : Y x)
  : transpS Y q (transpS Y p v) ≈S v.
Proof.
  assert (e : x ≈S x) by reflexivity.
  transitivity (transpS Y e v).
  - symmetry. exact (axiom_transp_comp Y p q e v).
  - apply axiom_transp_id.
Qed.

(** Fiber isomorphisms are consequences of coherent transport. *)
Definition fam_EqToIso {X} (Y : FamS X) {x y} (p : x ≈S y)
  : Y x ≅[SetCat] Y y.
Proof.
  assert (q : y ≈S x) by (symmetry; exact p).
  exists (transpS Y p), (transpS Y q); split; intros v;
    apply transpS_inverse.
Defined.

Definition ConstFamS (X A : SetC) : FamS X.
Proof.
  refine {| fam := fun _ => A; transpS := fun _ _ _ => id_resp (X := A) |};
    intros; reflexivity.
Defined.



(** *** Dependent Sums

    Both coordinates are compared by setoid equivalence. The first witness
    supplies the transport needed to compare the second coordinates. *)

Definition SigEq {X : SetC} {Y : FamS X} (a b : ∃ x : X, Y x)
  := ∃ p : a.1 ≈S b.1, transpS Y p a.2 ≈S b.2.

Infix "≈ΣS" := SigEq (at level 50).

Global Instance SigEq_Equivalence {X Y} : Equivalence (@SigEq X Y).
Proof.
  split.
  - intros [x v]. assert (p : x ≈S x) by reflexivity.
    exists p. apply axiom_transp_id.
  - intros [x v] [y w] [p Hp].
    assert (q : y ≈S x) by (symmetry; exact p).
    exists q. transitivity (transpS Y q (transpS Y p v)).
    + apply func_proper. symmetry. exact Hp.
    + apply transpS_inverse.
  - intros [x v] [y w] [z u] [p Hp] [q Hq].
    assert (r : x ≈S z) by (transitivity y; assumption).
    exists r. transitivity (transpS Y q (transpS Y p v)).
    + exact (axiom_transp_comp Y p q r v).
    + transitivity (transpS Y q w).
      * apply func_proper. exact Hp.
      * exact Hq.
Qed.

Program Canonical SigS (X : SetC) (Y : FamS X) :=
  {|carrier := ∃ x : X, Y x
  ; carrier_equiv := SigEq
  |}.

Definition sig_baseS {X} (Y : FamS X) : SigS X Y →r X.
Proof.
  unshelve refine (@Build_FunS_resp (SigS X Y) X (fun a => a.1) _).
  intros a b [p Hp]. exact p.
Defined.
