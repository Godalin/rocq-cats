From Cats Require Import
  Cat.Core
  Cat.Slice
  Cat.Slice.Reindex
  Cat.Pullback.
From Cats Require Import
  Cat.Functor
  Cat.Natural.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Pullback.
From Cats Require Import
  Instance.Set.Fam.Core
  Instance.Set.Fam.Cat
  Instance.Set.Fam.Reindex.
From Cats Require Import
  Instance.Set.Fam.Fixed
  Instance.Set.Fam.Slice.

(** * Total Spaces Commute with Substitution

    Compare the existing family-reindexing pullback with the chosen setoid
    pullback, using the general slice construction. *)

(** * 全空间与替换相容

    使用一般切片构造，将已有族重索引拉回与选定广集拉回比较。 *)

Local Existing Instance SetCat_HasPullback.

(** Naming the carrier universe prevents minimization from identifying it with
    the inferred equivalence-witness universe. *)

(** 命名载体宇宙可防止最小化将其与推断出的相等见证宇宙等同。 *)

Definition fam_sum_reindex@{u +} {X Y : SetC@{u _}} (f : X →r Y) (A : FamS Y)
  : SliceHom (FamSumOb A[f]S) (FamSumOb A)[f]C
  := slice_reindex_lift f (FamSumOb A) (B := FamSumOb A[f]S)
    (fam_total_resp (fam_reindex (FixedFamC A) f))
    (fst (fam_reindex_pullback (FixedFamC A) f)).

(** The comparison between reindexed totals and pulled-back totals is
    invertible. *)

(** 重索引全空间与拉回全空间之间的比较可逆。 *)

Definition fam_sum_reindex_iso@{u +} {X Y : SetC@{u _}} (f : X →r Y)
    (A : FamS Y)
  : @is_iso (SetCat /C X) _ _ (fam_sum_reindex f A)
  := slice_reindex_lift_iso f (FamSumOb A) (B := FamSumOb A[f]S)
    (fam_total_resp (fam_reindex (FixedFamC A) f))
    (fst (fam_reindex_pullback (FixedFamC A) f))
    (fam_reindex_pullback (FixedFamC A) f).

(** Total-space base-change comparisons are natural in the family. *)

(** 全空间基变换比较在族变量上自然。 *)

Program Definition FamSumReindexN@{u +} {X Y : SetC@{u _}} (f : X →r Y)
  : (FamSumF X ∘F FamReindexF f)
      ⇒ (SliceReindexF (C := SetCat) f ∘F FamSumF Y)
  :=
  {|nt := fam_sum_reindex f
  |}.
Next Obligation. intros [x a]. split; reflexivity. Defined.

(** Taking total spaces commutes with reindexing up to natural isomorphism. *)

(** 取全空间与重索引在自然同构意义下交换。 *)

Definition fam_sum_reindex_nat_iso@{u +} {X Y : SetC@{u _}} (f : X →r Y)
  : (FamSumF X ∘F FamReindexF f)
      ≅N (SliceReindexF (C := SetCat) f ∘F FamSumF Y)
  := (FamSumReindexN f; fam_sum_reindex_iso f).

(** The natural comparison commutes with the chosen identity and composite
    substitution comparisons. These are equations of maps in the slice. *)

(** 自然比较与选定恒等、复合替换比较交换；这些是切片中映射的方程。 *)

Theorem fam_sum_reindex_id@{u +} {X : SetC@{u _}} (A : FamS X)
  : slice_map
      (fam_sum_reindex id_resp A ∘/C fam_sum_map (fam_map_reindex_id A)) ≈f
      slice_map (slice_reindex_id (C := SetCat) (FamSumOb A)).
Proof. intros [x a]. split; reflexivity. Qed.

(** Compatibility with composition for [fam_sum_reindex]. *)

(** [fam_sum_reindex] 与复合的相容性。 *)

Theorem fam_sum_reindex_comp@{u +} {X Y Z : SetC@{u _}}
    (f : Y →r Z) (g : X →r Y) (A : FamS Z)
  : slice_map (fam_sum_reindex (f ∘r g) A ∘/C
      fam_sum_map A⟨f, g⟩Fam) ≈f
    slice_map (slice_reindex_comp (C := SetCat) f g (FamSumOb A) ∘/C
      slice_reindex_map (C := SetCat) g (fam_sum_reindex f A) ∘/C
      fam_sum_reindex g A[f]S).
Proof. intros [x a]. split; reflexivity. Qed.

(** * Fibers Commute with Substitution

    Over x, an element (a,p : q a ≈ f x) becomes the pullback point
    (x,a,p⁻¹), together with its reflexive membership over x. *)

(** * 纤维与替换相容

    在 x 上，元素 (a,p : q a ≈ f x) 变为拉回点 (x,a,p⁻¹)，再附带其在 x 处的
    自反成员见证。 *)

Program Definition slice_fiber_reindex_resp@{u +} {X Y : SetC@{u _}}
    (f : X →r Y) (A : SliceOb SetCat Y) (x : X)
  : (FiberFamS (slice_arrow A))[f]S x →r
      FiberS (slice_arrow (C := SetCat) A[f]C) x
  :=
  {|func a := ((x; (a.1; symmetry a.2)); reflS (x := x))
  |}.
Next Obligation. intros a b H. split; [reflexivity | exact H]. Defined.

(** Map a reindexed fiber family to the fibers of the pulled-back slice
    object. *)

(** 将重索引纤维族映射到拉回切片对象的纤维族。 *)

Program Definition slice_fiber_reindex@{u +} {X Y : SetC@{u _}}
    (f : X →r Y) (A : SliceOb SetCat Y)
  : (FiberFamS (slice_arrow A))[f]S →Fam
      FiberFamS (slice_arrow (C := SetCat) A[f]C)
  :=
  {|fam_map := slice_fiber_reindex_resp f A
  |}.
Next Obligation. split; [symmetry; exact p | reflexivity]. Defined.

(** A pullback point need only have an equivalent first coordinate. Its
    fiber-membership witness transports that coordinate along f. *)

(** 拉回点的第一坐标仅需等价于索引，其纤维成员见证通过 f 运输该坐标。 *)

Program Definition slice_fiber_reindex_inv_resp@{u +} {X Y : SetC@{u _}}
    (f : X →r Y) (A : SliceOb SetCat Y) (x : X)
  : FiberS (slice_arrow (C := SetCat) A[f]C) x →r
      (FiberFamS (slice_arrow A))[f]S x
  :=
  {|func a := (a.1.2.1; _)
  |}.
Next Obligation.
  transitivity (f a.1.1).
  - symmetry. exact a.1.2.2.
  - apply func_proper. exact a.2.
Defined.
Next Obligation. intros a b H. exact (snd H). Defined.

(** Recover a reindexed fiber point from a fiber of the slice pullback. *)

(** 从切片拉回的纤维中恢复重索引纤维点。 *)

Program Definition slice_fiber_reindex_inv@{u +} {X Y : SetC@{u _}}
    (f : X →r Y) (A : SliceOb SetCat Y)
  : FiberFamS (slice_arrow (C := SetCat) A[f]C) →Fam
      (FiberFamS (slice_arrow A))[f]S
  :=
  {|fam_map := slice_fiber_reindex_inv_resp f A
  |}.
Next Obligation. reflexivity. Defined.

(** The comparison between fiber formation and slice reindexing is invertible. *)

(** 取纤维与切片重索引之间的比较可逆。 *)

Definition slice_fiber_reindex_iso@{u +} {X Y : SetC@{u _}}
    (f : X →r Y) (A : SliceOb SetCat Y)
  : @is_iso (FamSCat X) _ _ (slice_fiber_reindex f A).
Proof.
  exists (slice_fiber_reindex_inv f A). split.
  - intros x a. cbn. reflexivity.
  - intros x [[y [a q]] r]. split; [symmetry; exact r | reflexivity].
Defined.

(** Fiber base-change comparisons are natural in the slice object. *)

(** 纤维基变换比较在切片对象上自然。 *)

Program Definition SliceFamReindexN@{u +} {X Y : SetC@{u _}} (f : X →r Y)
  : (FamReindexF f ∘F SliceFamF Y)
      ⇒ (SliceFamF X ∘F SliceReindexF (C := SetCat) f)
  :=
  {|nt := slice_fiber_reindex f
  |}.
Next Obligation. intros x a. split; reflexivity. Defined.

(** Taking fibers commutes with base change up to natural isomorphism. *)

(** 取纤维与基变换在自然同构意义下交换。 *)

Definition slice_fam_reindex_nat_iso@{u +} {X Y : SetC@{u _}} (f : X →r Y)
  : (FamReindexF f ∘F SliceFamF Y)
      ≅N (SliceFamF X ∘F SliceReindexF (C := SetCat) f)
  := (SliceFamReindexN f; slice_fiber_reindex_iso f).

(** ** Compatibility with the Two Round-trip Comparisons

    The sum and fiber base-change comparisons give the same map after the
    slice round trip. The family round trip is likewise preserved, using the
    specified inverse fiber comparison to match its endpoints. *)

(** ** 与两个往返比较的相容性

    和与纤维的基变换比较在切片往返后给出同一映射。族的往返也被保持，并通过指定
    的逆纤维比较对齐端点。 *)

Theorem slice_fam_reindex_fiber_total@{u +} {X Y : SetC@{u _}}
    (f : X →r Y) (A : SliceOb SetCat Y)
  : slice_map (slice_reindex_map (C := SetCat) f (fiber_total_slice A) ∘/C
      fam_sum_reindex f (FiberFamS (slice_arrow A))) ≈f
    slice_map (fiber_total_slice (SliceReindexOb (C := SetCat) f A) ∘/C
      fam_sum_map (slice_fiber_reindex f A)).
Proof. intros [x [a q]]. split; reflexivity. Qed.

(** The fiber base-change comparison respects the family total-fiber round
    trip. *)

(** 纤维基变换比较保持族的全空间与纤维往返比较。 *)

Theorem slice_fam_reindex_total_fiber@{u +} {X Y : SetC@{u _}}
    (f : X →r Y) (A : FamS Y)
  : fam_map_reindex f (total_fiber_elim A) ∘Fam
      (slice_fiber_reindex_inv f (FamSumOb A) ∘Fam
        slice_fiber_map (fam_sum_reindex f A)) ≈Fam total_fiber_elim A[f]S.
Proof.
  intros x [[y a] q]. cbn. apply transpS_witness_independent.
Qed.

(** ** Coherent Indexed Equivalence

    Both directions respect equivalent base maps. Together with the unit and
    composition equations, the round-trip equations above give the comparison
    data and coherence componentwise. *)

(** ** 相干索引等价

    两个方向均保持等价基底映射；连同单位、复合和上述往返方程，逐分量给出比较数
    据及其相干性。 *)

Theorem fam_sum_reindex_equiv@{u +} {X Y : SetC@{u _}} {f g : X →r Y}
    (H : f ≈f g) (A : FamS Y)
  : slice_map (slice_reindex_equiv (C := SetCat) H (FamSumOb A) ∘/C
      fam_sum_reindex f A) ≈f
    slice_map (fam_sum_reindex g A ∘/C fam_sum_map A⟦H⟧Fam).
Proof.
  intros [x a]. split; [reflexivity | exists (H x); reflexivity].
Qed.

(** Fiber base-change comparison is compatible with equality of base maps. *)

(** 纤维基变换比较与基底映射相等相容。 *)

Theorem slice_fam_reindex_equiv@{u +} {X Y : SetC@{u _}} {f g : X →r Y}
    (H : f ≈f g) (A : SliceOb SetCat Y)
  : slice_fiber_reindex g A ∘Fam (FiberFamS (slice_arrow A))⟦H⟧Fam ≈Fam
    slice_fiber_map A⟦H⟧C ∘Fam slice_fiber_reindex f A.
Proof. intros x [a p]. split; reflexivity. Qed.

(** The fiber base-change comparison is compatible with identity substitution. *)

(** 纤维基变换比较与恒等替换相容。 *)

Theorem slice_fam_reindex_id@{u +} {X : SetC@{u _}} (A : SliceOb SetCat X)
  : slice_fiber_reindex id_resp A ∘Fam
      fam_map_reindex_id (FiberFamS (slice_arrow A)) ≈Fam
    slice_fiber_map (slice_reindex_id (C := SetCat) A).
Proof. intros x [a p]. split; [symmetry; exact p | reflexivity]. Qed.

(** The fiber base-change comparison is compatible with composite
    substitution. *)

(** 纤维基变换比较与复合替换相容。 *)

Theorem slice_fam_reindex_comp@{u +} {X Y Z : SetC@{u _}}
    (f : Y →r Z) (g : X →r Y) (A : SliceOb SetCat Z)
  : slice_fiber_reindex (f ∘r g) A ∘Fam
      (FiberFamS (slice_arrow A))⟨f, g⟩Fam ≈Fam
    slice_fiber_map A⟨f, g⟩C ∘Fam
      slice_fiber_reindex g (SliceReindexOb (C := SetCat) f A) ∘Fam
      fam_map_reindex g (slice_fiber_reindex f A).
Proof. intros x [a p]. split; reflexivity. Qed.
