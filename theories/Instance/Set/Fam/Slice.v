From Cats Require Import Cat.Core Cat.Slice Cat.Functor Cat.Natural Cat.CatCat.
From Cats Require Import Instance.Set.Core Instance.Set.Fam.Core Instance.Set.Fam.Fixed.

(** * Coherent Families and Slices

    A family gives its total-space projection; a map gives its family of
    fibers. Both constructions act on morphisms and preserve their equality. *)

Definition FamSumOb {X : SetC} (A : FamS X) : SliceOb SetCat X :=
  {| slice_dom := SigS X A; slice_arrow := sig_base_resp A |}.

Program Definition fam_sum_map {X : SetC} {A B : FamS X} (f : A →Fam B)
  : SliceHom (FamSumOb A) (FamSumOb B) :=
  {| slice_map := fam_map_total_resp f |}.
Next Obligation. intros [x a]. reflexivity. Defined.

Program Definition FamSumF (X : SetC) : Functor (FamSCat X) (SetCat /C X) :=
  {| F0 := FamSumOb
   ; F1 A B := fam_sum_map |}.
Next Obligation.
  intros f g H [x a]. exists (reflS (x := x)).
  transitivity (fam_map f x a); [apply transpS_id | exact (H x a)].
Defined.
Next Obligation. intros [x a]. reflexivity. Defined.
Next Obligation. intros [x a]. reflexivity. Defined.

(** The triangle witness determines fiber membership, not fiber equality. *)
Program Definition slice_fiber_map_resp {X : SetC} {A B : SliceOb SetCat X}
    (f : SliceHom A B) (x : X)
  : FiberS (slice_arrow A) x →r FiberS (slice_arrow B) x :=
  {| func a := (slice_map f a.1; _) |}.
Next Obligation.
  transitivity (slice_arrow A a.1); [exact (slice_comm f a.1) | exact a.2].
Defined.
Next Obligation. intros a b H. apply func_proper. exact H. Defined.

Program Definition slice_fiber_map {X : SetC} {A B : SliceOb SetCat X}
    (f : SliceHom A B) : FiberFamS (slice_arrow A) →Fam FiberFamS (slice_arrow B) :=
  {| fam_map := slice_fiber_map_resp f |}.
Next Obligation. reflexivity. Defined.

Program Definition SliceFamF (X : SetC) : Functor (SetCat /C X) (FamSCat X) :=
  {| F0 A := FiberFamS (slice_arrow A)
   ; F1 A B := slice_fiber_map |}.
Next Obligation. intros f g H x a. exact (H a.1). Defined.
Next Obligation. intros x a. cbn. reflexivity. Defined.
Next Obligation. intros x a. cbn. reflexivity. Defined.

(** ** Total Space of a Fiber Family *)

Program Definition fiber_total_slice@{u p +} {X : SetC@{u p}} (A : SliceOb SetCat X)
  : SliceHom (FamSumOb (FiberFamS (slice_arrow A))) A :=
  {| slice_map := fiber_total_proj_resp (slice_arrow A) |}.
Next Obligation. intros [x [a p]]. exact p. Defined.

Program Definition fiber_total_slice_inv@{u p +} {X : SetC@{u p}} (A : SliceOb SetCat X)
  : SliceHom A (FamSumOb (FiberFamS (slice_arrow A))) :=
  {| slice_map := fiber_total_intro_resp (slice_arrow A) |}.
Next Obligation. intros a. reflexivity. Defined.

Definition fiber_total_slice_iso@{u p +} {X : SetC@{u p}} (A : SliceOb SetCat X)
  : @is_iso (SetCat /C X) _ _ (fiber_total_slice A).
Proof.
  exists (fiber_total_slice_inv A). split.
  - exact (fst (fiber_total_iso (slice_arrow A)).2.2).
  - exact (snd (fiber_total_iso (slice_arrow A)).2.2).
Defined.

Program Definition FamFiberTotalN@{u p +} (X : SetC@{u p})
  : (FamSumF X ∘F SliceFamF X) => (@IdF (SetCat /C X)) :=
  {| nt := fiber_total_slice |}.
Next Obligation. intros a. reflexivity. Defined.

Definition fam_fiber_total_nat_iso@{u p +} (X : SetC@{u p})
  : (FamSumF X ∘F SliceFamF X) ≅N (@IdF (SetCat /C X)) :=
  (FamFiberTotalN X; fiber_total_slice_iso).

(** ** Fibers of a Total-space Projection

    A point over x may be represented by (y,a) together with y ≈ x.
    Recover its value in A x by the family's coherent transport. *)

Program Definition total_fiber_elim_resp {X : SetC} (A : FamS X) (x : X)
  : FiberS (sig_base_resp A) x →r A x :=
  {| func a := transpS A a.2 a.1.2 |}.
Next Obligation.
  intros [[y a] p] [[z b] q] [r H]. cbn in *.
  transitivity (transpS A q (transpS A r a)).
  - apply transpS_comp.
  - apply func_proper. exact H.
Defined.

Program Definition total_fiber_elim {X : SetC} (A : FamS X)
  : FiberFamS (sig_base_resp A) →Fam A :=
  {| fam_map := total_fiber_elim_resp A |}.
Next Obligation. apply transpS_comp. Defined.

Program Definition total_fiber_intro_resp {X : SetC} (A : FamS X) (x : X)
  : A x →r FiberS (sig_base_resp A) x :=
  {| func a := ((x; a); reflS (x := x)) |}.
Next Obligation.
  intros a b H. exists (reflS (x := x)).
  transitivity a; [apply transpS_id | exact H].
Defined.

Program Definition total_fiber_intro {X : SetC} (A : FamS X)
  : A →Fam FiberFamS (sig_base_resp A) :=
  {| fam_map := total_fiber_intro_resp A |}.
Next Obligation. exists (symmetry p). apply transpS_inv. Defined.

Definition total_fiber_iso {X : SetC} (A : FamS X)
  : @is_iso (FamSCat X) _ _ (total_fiber_elim A).
Proof.
  exists (total_fiber_intro A). split.
  - intros x [[y a] p]. exists (symmetry p). apply transpS_inv.
  - intros x a. apply transpS_id.
Defined.

Program Definition FamTotalFiberN@{u p +} (X : SetC@{u p})
  : (SliceFamF X ∘F FamSumF X) => (@IdF (FamSCat X)) :=
  {| nt := total_fiber_elim |}.
Next Obligation.
  intros x [[y a] p]. cbn.
  transitivity (transpS Y p (fam_map f y a)).
  - apply transpS_witness_independent.
  - symmetry. apply fam_map_naturality.
Defined.

Definition fam_total_fiber_nat_iso@{u p +} (X : SetC@{u p})
  : (SliceFamF X ∘F FamSumF X) ≅N (@IdF (FamSCat X)) :=
  (FamTotalFiberN X; total_fiber_iso).

Definition fam_slice_equiv@{u p +} (X : SetC@{u p}) : FamSCat X ≃C (SetCat /C X) :=
  (FamSumF X; (SliceFamF X;
    (fam_total_fiber_nat_iso X, fam_fiber_total_nat_iso X))).
