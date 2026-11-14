From Cats Require Import
  Cat.Core
  Cat.Slice.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.CatCat.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Fam.Core
  Instance.Set.Fam.Fixed.

(** * Coherent Families and Slices

    A family gives its total-space projection; a map gives its family of
    fibers. Both constructions act on morphisms and preserve their equality. *)

(** * 相干族与切片

    族给出全空间投影，映射给出纤维族；两种构造都作用于态射并保持指定相等。 *)

Definition FamSumOb {X : SetC} (A : FamS X)
  : SliceOb SetCat X
  :=
  {|slice_dom := SigS X A
  ; slice_arrow := sig_base_resp A
  |}.

(** A fixed-base family map induces a slice map of total projections. *)

(** 固定基底族映射诱导全空间投影之间的切片映射。 *)

Program Definition fam_sum_map {X : SetC} {A B : FamS X} (f : A →Fam B)
  : SliceHom (FamSumOb A) (FamSumOb B)
  :=
  {|slice_map := fam_map_total_resp f
  |}.
Next Obligation. intros [x a]. reflexivity. Defined.

(** Send a fixed-base family to its total projection in the slice category. *)

(** 将固定基底族送到切片范畴中的全空间投影。 *)

Program Definition FamSumF (X : SetC)
  : Fct (FamSCat X) (SetCat /C X)
  :=
  {|F0 := FamSumOb
  ; F1 A B := fam_sum_map
  |}.
Next Obligation.
  intros f g H [x a]. exists (reflS (x := x)).
  transitivity (fam_map f x a); [apply transpS_id | exact (H x a)].
Defined.
Next Obligation. intros [x a]. reflexivity. Defined.
Next Obligation. intros [x a]. reflexivity. Defined.

(** The triangle witness determines fiber membership, not fiber equality. *)

(** 三角形见证决定纤维成员资格，不决定纤维相等。 *)

Program Definition slice_fiber_map_resp {X : SetC} {A B : SliceOb SetCat X}
    (f : SliceHom A B) (x : X)
  : FiberS (slice_arrow A) x →r FiberS (slice_arrow B) x
  :=
  {|func a := (slice_map f a.1; _)
  |}.
Next Obligation.
  transitivity (slice_arrow A a.1); [exact (slice_comm f a.1) | exact a.2].
Defined.
Next Obligation. intros a b H. apply func_proper. exact H. Defined.

(** A slice morphism gives a transport-compatible map between fiber families. *)

(** 切片态射给出纤维族之间与运输相容的映射。 *)

Program Definition slice_fiber_map {X : SetC} {A B : SliceOb SetCat X}
    (f : SliceHom A B)
  : FiberFamS (slice_arrow A) →Fam FiberFamS (slice_arrow B)
  :=
  {|fam_map := slice_fiber_map_resp f
  |}.
Next Obligation. reflexivity. Defined.

(** Send a slice object to its coherent family of fibers. *)

(** 将切片对象送到其相干纤维族。 *)

Program Definition SliceFamF (X : SetC)
  : Fct (SetCat /C X) (FamSCat X)
  :=
  {|F0 A := FiberFamS (slice_arrow A)
  ; F1 A B := slice_fiber_map
  |}.
Next Obligation. intros f g H x a. exact (H a.1). Defined.
Next Obligation. intros x a. cbn. reflexivity. Defined.
Next Obligation. intros x a. cbn. reflexivity. Defined.

(** ** Total Space of a Fiber Family *)

(** ** 纤维族的全空间 *)

(** Forget the fiber presentation of a total-space point to recover the
    original slice point. *)

(** 忘却全空间点的纤维表示，恢复原切片点。 *)

Program Definition fiber_total_slice@{u p +} {X : SetC@{u p}}
    (A : SliceOb SetCat X)
  : SliceHom (FamSumOb (FiberFamS (slice_arrow A))) A
  :=
  {|slice_map := fiber_total_proj_resp (slice_arrow A)
  |}.
Next Obligation. intros [x [a p]]. exact p. Defined.

(** Present a slice point in the fiber over its own image. *)

(** 在切片点自身像处的纤维中表示该点。 *)

Program Definition fiber_total_slice_inv@{u p +} {X : SetC@{u p}}
    (A : SliceOb SetCat X)
  : SliceHom A (FamSumOb (FiberFamS (slice_arrow A)))
  :=
  {|slice_map := fiber_total_intro_resp (slice_arrow A)
  |}.
Next Obligation. intros a. reflexivity. Defined.

(** The total-space fiber comparison is an isomorphism in the slice. *)

(** 全空间纤维比较是切片中的同构。 *)

Definition fiber_total_slice_iso@{u p +} {X : SetC@{u p}} (A : SliceOb SetCat X)
  : @is_iso (SetCat /C X) _ _ (fiber_total_slice A).
Proof.
  exists (fiber_total_slice_inv A). split.
  - exact (fst (fiber_total_iso (slice_arrow A)).2.2).
  - exact (snd (fiber_total_iso (slice_arrow A)).2.2).
Defined.

(** The fiber-then-total comparison is natural in slice morphisms. *)

(** 先取纤维再取全空间的比较在切片态射上自然。 *)

Program Definition FamFiberTotalN@{u p +} (X : SetC@{u p})
  : (FamSumF X ∘F SliceFamF X) ⇒ (@IdF (SetCat /C X))
  :=
  {|nt := fiber_total_slice
  |}.
Next Obligation. intros a. reflexivity. Defined.

(** Taking fibers and then total spaces is naturally isomorphic to the slice
    identity. *)

(** 先取纤维再取全空间自然同构于切片恒等函子。 *)

Definition fam_fiber_total_nat_iso@{u p +} (X : SetC@{u p})
  : (FamSumF X ∘F SliceFamF X) ≅N (@IdF (SetCat /C X))
  := (FamFiberTotalN X; fiber_total_slice_iso).

(** ** Fibers of a Total-space Projection

    A point over x may be represented by (y,a) together with y ≈ x. Recover
    its value in A x by the family's coherent transport. *)

(** ** 全空间投影的纤维

    位于 x 上的点可以由 (y,a) 及 y ≈ x 表示；通过族的相干运输恢复 A x 中的值。 *)

Program Definition total_fiber_elim_resp {X : SetC} (A : FamS X) (x : X)
  : FiberS (sig_base_resp A) x →r A x
  :=
  {|func a := transpS A a.2 a.1.2
  |}.
Next Obligation.
  intros [[y a] p] [[z b] q] [r H]. cbn in *.
  transitivity (transpS A q (transpS A r a)).
  - apply transpS_comp.
  - apply func_proper. exact H.
Defined.

(** Transport a fiber point of a total projection into its designated family
    fiber. *)

(** 将全空间投影的纤维点运输到指定的族纤维。 *)

Program Definition total_fiber_elim {X : SetC} (A : FamS X)
  : FiberFamS (sig_base_resp A) →Fam A
  :=
  {|fam_map := total_fiber_elim_resp A
  |}.
Next Obligation. apply transpS_comp. Defined.

(** Present a family element in the corresponding fiber of its total
    projection. *)

(** 将族元素表示为全空间投影中对应的纤维元素。 *)

Program Definition total_fiber_intro_resp {X : SetC} (A : FamS X) (x : X)
  : A x →r FiberS (sig_base_resp A) x
  :=
  {|func a := ((x; a); reflS (x := x))
  |}.
Next Obligation.
  intros a b H. exists (reflS (x := x)).
  transitivity a; [apply transpS_id | exact H].
Defined.

(** The fiberwise map into the fiber family of the total projection. *)

(** 指向全空间投影的纤维族的逐纤维映射。 *)

Program Definition total_fiber_intro {X : SetC} (A : FamS X)
  : A →Fam FiberFamS (sig_base_resp A)
  :=
  {|fam_map := total_fiber_intro_resp A
  |}.
Next Obligation. exists (symmetry p). apply transpS_inv. Defined.

(** A family is isomorphic to the fibers of its total projection. *)

(** 族同构于其全空间投影的纤维族。 *)

Definition total_fiber_iso {X : SetC} (A : FamS X)
  : @is_iso (FamSCat X) _ _ (total_fiber_elim A).
Proof.
  exists (total_fiber_intro A). split.
  - intros x [[y a] p]. exists (symmetry p). apply transpS_inv.
  - intros x a. apply transpS_id.
Defined.

(** The total-then-fiber comparison is natural in fixed-base families. *)

(** 先取全空间再取纤维的比较在固定基底族上自然。 *)

Program Definition FamTotalFiberN@{u p +} (X : SetC@{u p})
  : (SliceFamF X ∘F FamSumF X) ⇒ (@IdF (FamSCat X))
  :=
  {|nt := total_fiber_elim
  |}.
Next Obligation.
  intros x [[y a] p]. cbn.
  transitivity (transpS Y p (fam_map f y a)).
  - apply transpS_witness_independent.
  - symmetry. apply fam_map_naturality.
Defined.

(** Taking total spaces and then fibers is naturally isomorphic to the family
    identity. *)

(** 先取全空间再取纤维自然同构于族恒等函子。 *)

Definition fam_total_fiber_nat_iso@{u p +} (X : SetC@{u p})
  : (SliceFamF X ∘F FamSumF X) ≅N (@IdF (FamSCat X))
  := (FamTotalFiberN X; total_fiber_iso).

(** Coherent families over a setoid and the slice over that setoid are
    equivalent categories. *)

(** 广集上的相干族范畴等价于该广集上的切片范畴。 *)

Definition fam_slice_equiv@{u p +} (X : SetC@{u p})
  : FamSCat X ≃C (SetCat /C X)
  := (FamSumF X; (SliceFamF X;
    (fam_total_fiber_nat_iso X, fam_fiber_total_nat_iso X))).
