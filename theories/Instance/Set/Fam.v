From Cats Require Import Cat.Core Instance.Set.Core.

(** * Dependent Sets and Coherent Families *)

(** ** Raw Dependent Functions

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

(** ** Coherent Families over Setoids

    Transport is a respectful map. The laws compare its action on elements,
    never equality witnesses themselves. Quantifying over any witnesses of
    the same base equivalences expresses coherence over a setoid: the composite
    law accepts any witness r, and witness independence follows from it. *)

Record FamS (X : SetC) :=
  { fam :> X → SetC
  ; transpS {x y : X} : x ≈S y → fam x →r fam y
  ; transpS_id {x} (p : x ≈S x) (v : fam x)
    : transpS p v ≈S v
  ; transpS_comp {x y z} (p : x ≈S y) (q : y ≈S z) (r : x ≈S z)
      (v : fam x)
    : transpS r v ≈S transpS q (transpS p v)
  }.

Arguments transpS {_} _ {_ _} _.
Arguments transpS_id {_} _ {_} _ _.
Arguments transpS_comp {_} _ {_ _ _} _ _ _ _.

Theorem reflS {X : SetC} {x : X} : x ≈S x.
Proof. reflexivity. Qed.

(** Different witnesses induce equivalent maps; no proof irrelevance is used. *)
Theorem transpS_witness_independent {X} (Y : FamS X) {x y} (p q : x ≈S y)
  : transpS Y p ≈f transpS Y q.
Proof.
  intros v. assert (e : x ≈S x) by reflexivity.
  transitivity (transpS Y q (transpS Y e v)).
  - exact (transpS_comp Y e q p v).
  - apply func_proper. apply transpS_id.
Qed.

Theorem transpS_inv {X} (Y : FamS X) {x y}
    (p : x ≈S y) (q : y ≈S x) (v : Y x)
  : transpS Y q (transpS Y p v) ≈S v.
Proof.
  assert (e : x ≈S x) by reflexivity.
  transitivity (transpS Y e v).
  - symmetry. exact (transpS_comp Y p q e v).
  - apply transpS_id.
Qed.

(** Fiber isomorphisms are consequences of coherent transport. *)
Definition transpS_iso {X} (Y : FamS X) {x y} (p : x ≈S y)
  : Y x ≅[SetCat] Y y.
Proof.
  assert (q : y ≈S x) by (symmetry; exact p).
  exists (transpS Y p), (transpS Y q); split; intros v;
    apply transpS_inv.
Defined.

Definition ConstFamS (X A : SetC) : FamS X.
Proof.
  refine {| fam := λ _, A; transpS := λ _ _ _, id_resp (X := A) |};
    intros; reflexivity.
Defined.

(** Reindexing keeps the fiber over the image and transports along the
    image of the base equivalence. Coherence follows from the original family. *)
Definition ReindexFamS {X Y : SetC} (A : FamS Y) (f : X →r Y) : FamS X.
Proof.
  refine {| fam := λ x, A (f x)
          ; transpS := λ x y p, transpS A (@func_proper _ _ f x y p) |}.
  - intros x p a. apply transpS_id.
  - intros x y z p q r a. apply transpS_comp.
Defined.

Notation "A '[' f ']S'" := (ReindexFamS A f)
  (at level 8, left associativity, format "A [ f ]S") : cat_scope.



(** ** Dependent Sums

    Both coordinates are compared by setoid equivalence. The first witness
    supplies the transport needed to compare the second coordinates. *)

Definition SigEq {X : SetC} {Y : FamS X} (a b : ∃ x : X, Y x)
  := ∃ p : a.1 ≈S b.1, transpS Y p a.2 ≈S b.2.

Infix "≈ΣS" := SigEq (at level 50).

Global Instance SigEq_Equivalence {X Y} : Equivalence (@SigEq X Y).
Proof.
  split.
  - intros [x v]. assert (p : x ≈S x) by reflexivity.
    exists p. apply transpS_id.
  - intros [x v] [y w] [p Hp].
    assert (q : y ≈S x) by (symmetry; exact p).
    exists q. transitivity (transpS Y q (transpS Y p v)).
    + apply func_proper. symmetry. exact Hp.
    + apply transpS_inv.
  - intros [x v] [y w] [z u] [p Hp] [q Hq].
    assert (r : x ≈S z) by (transitivity y; assumption).
    exists r. transitivity (transpS Y q (transpS Y p v)).
    + exact (transpS_comp Y p q r v).
    + transitivity (transpS Y q w).
      * apply func_proper. exact Hp.
      * exact Hq.
Qed.

Program Canonical SigS (X : SetC) (Y : FamS X) :=
  {|carrier := ∃ x : X, Y x
  ; carrier_equiv := SigEq
  |}.

Definition sig_base_resp {X} (Y : FamS X) : SigS X Y →r X.
Proof.
  unshelve refine (@Build_FunS_resp (SigS X Y) X (λ a, a.1) _).
  intros a b [p Hp]. exact p.
Defined.

(** ** Fibers of Setoid Maps

    Every respectful map of setoids gives a coherent family of fibers.
    Membership witnesses are retained as data; fiber equality compares only
    their underlying elements. *)

Definition FiberS {E X : SetC} (f : E →r X) (x : X) : SetC.
Proof.
  refine {| carrier := ∃ u : E, f u ≈S x
          ; carrier_equiv a b := a.1 ≈S b.1 |}.
  split.
  - intros a. reflexivity.
  - intros a b H. symmetry. exact H.
  - intros a b c H1 H2. transitivity b.1; assumption.
Defined.

Definition fiber_transp_resp {E X : SetC} (f : E →r X)
    {x y : X} (p : x ≈S y) : FiberS f x →r FiberS f y.
Proof.
  assert (step : ∀ u : E, f u ≈S x → f u ≈S y).
  { intros u q. transitivity x; assumption. }
  unshelve refine (@Build_FunS_resp (FiberS f x) (FiberS f y)
    (λ a, (a.1; step a.1 a.2)) _).
  intros a b H. exact H.
Defined.

Definition FiberFamS {E X : SetC} (f : E →r X) : FamS X.
Proof.
  refine {| fam := FiberS f
          ; transpS := λ x y p, fiber_transp_resp f p |}.
  - intros x p v. change (v.1 ≈S v.1). reflexivity.
  - intros x y z p q r v. change (v.1 ≈S v.1). reflexivity.
Defined.

(** The total space recovers the domain of the original map, up to setoid
    isomorphism. This also shows that transport-based sum equality identifies
    equivalent representatives without identifying their witness data. *)

Definition fiber_total_proj_resp {E X : SetC} (f : E →r X)
    : SigS X (FiberFamS f) →r E.
Proof.
  unshelve refine (@Build_FunS_resp (SigS X (FiberFamS f)) E
    (λ a, a.2.1) _).
  intros a b [p Hp]. exact Hp.
Defined.

Definition fiber_total_intro_resp {E X : SetC} (f : E →r X)
    : E →r SigS X (FiberFamS f).
Proof.
  unshelve refine (@Build_FunS_resp E (SigS X (FiberFamS f))
    (λ e, (f e; (e; reflS (x := f e)))) _).
  intros e e' H.
  assert (p : f e ≈S f e') by (apply func_proper; exact H).
  exists p. exact H.
Defined.

Theorem fiber_total_iso {E X : SetC} (f : E →r X)
  : SigS X (FiberFamS f) ≅[SetCat] E.
Proof.
  exists (fiber_total_proj_resp f), (fiber_total_intro_resp f); split.
  - intros [x [e q]]. exists q. change (e ≈S e). reflexivity.
  - intros e. change (e ≈S e). reflexivity.
Qed.
