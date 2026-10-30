From Cats Require Import Cat.Core Cat.Set.

(** * Families of Setoids

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

Definition fiber_transpS {E X : SetC} (f : E →r X)
    {x y : X} (p : x ≈S y) : FiberS f x →r FiberS f y.
Proof.
  assert (step : ∀ u : E, f u ≈S x → f u ≈S y).
  { intros u q. transitivity x; assumption. }
  unshelve refine (@Build_FunS_resp (FiberS f x) (FiberS f y)
    (fun a => existT _ a.1 (step a.1 a.2)) _).
  intros a b H. exact H.
Defined.

Definition FiberFamS {E X : SetC} (f : E →r X) : FamS X.
Proof.
  refine {| fam := FiberS f
          ; transpS := fun x y p => fiber_transpS f p |}.
  - intros x p v. change (v.1 ≈S v.1). reflexivity.
  - intros x y z p q r v. change (v.1 ≈S v.1). reflexivity.
Defined.

(** The total space recovers the domain of the original map, up to setoid
    isomorphism. This also shows that transport-based sum equality identifies
    equivalent representatives without identifying their witness data. *)

Definition fiber_total_projS {E X : SetC} (f : E →r X)
    : SigS X (FiberFamS f) →r E.
Proof.
  unshelve refine (@Build_FunS_resp (SigS X (FiberFamS f)) E
    (fun a => a.2.1) _).
  intros a b [p Hp]. exact Hp.
Defined.

Definition fiber_total_introS {E X : SetC} (f : E →r X)
    : E →r SigS X (FiberFamS f).
Proof.
  unshelve refine (@Build_FunS_resp E (SigS X (FiberFamS f))
    (fun e => existT _ (f e) (existT _ e (reflS (x := f e)))) _).
  intros e e' H.
  assert (p : f e ≈S f e') by (apply func_proper; exact H).
  exists p. exact H.
Defined.

Theorem fiber_total_iso {E X : SetC} (f : E →r X)
  : SigS X (FiberFamS f) ≅[SetCat] E.
Proof.
  exists (fiber_total_projS f), (fiber_total_introS f); split.
  - intros [x [e q]]. exists q. change (e ≈S e). reflexivity.
  - intros e. change (e ≈S e). reflexivity.
Qed.
