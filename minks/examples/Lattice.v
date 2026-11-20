From Stdlib Require Import Utf8.
From Minks Require Import all.
From MinksExamples Require Import Algebra.

Set Universe Polymorphism.

(** * The lattice hierarchy

    Choose a partial order on a setoid. Add meets and joins independently,
    then choose bounds and the joins and meets of arbitrary families. *)

(** * 格的层级

    在广集上选取偏序，分别加入交与并，再选取上下界以及任意族的交与并。 *)

(** Choose a relation on the carrier. *)

(** 在载体上选取一个关系。 *)

Minks.Mixin HasOrder (A : Type)
  :=
  { leq : A → A → Type
  }.
Arguments leq {_ _} _ _.

(** Relate the chosen order to the setoid equality. *)

(** 将选取的偏序与广集相等联系起来。 *)

Minks.Mixin IsPoset
  extends HasEquiv, HasOrder
  :=
  { leq_of_equiv : ∀ x y, equiv x y → leq x y
  ; leq_trans : ∀ x y z, leq x y → leq y z → leq x z
  ; leq_antisym : ∀ x y, leq x y → leq y x → equiv x y
  }.

(** Choose greatest lower bounds for the selected order. *)

(** 为选定的序选取最大下界。 *)

Minks.Mixin HasMeet
  extends HasOrder
  :=
  { meet : A → A → A
  ; meet_leq_l : ∀ x y, leq (meet x y) x
  ; meet_leq_r : ∀ x y, leq (meet x y) y
  ; leq_meet : ∀ x y z, leq z x → leq z y → leq z (meet x y)
  }.
Arguments meet {_ _ _} _ _.

(** Choose least upper bounds for the same order. *)

(** 为同一选定的序选取最小上界。 *)

Minks.Mixin HasJoin
  extends HasOrder
  :=
  { join : A → A → A
  ; leq_join_l
    : ∀ x y, leq x (join x y)
  ; leq_join_r
    : ∀ x y, leq y (join x y)
  ; join_leq
    : ∀ x y z, leq x z → leq y z → leq (join x y) z
  }.
Arguments join {_ _ _} _ _.

(** Choose least upper bounds at an index universe that contains the carrier. *)

(** 在可容纳载体的索引宇宙上选取最小上界。 *)

Minks.Mixin HasAJoin@{u o i | u <= i}
  extends HasOrder@{u o}
  :=
  { ajoin {I : Type@{i}} (f : I → A) : A
  ; leq_ajoin {I : Type@{i}} (f : I → A) (k : I)
    : leq (f k) (ajoin f)
  ; ajoin_leq {I : Type@{i}} (f : I → A) (b : A)
    : (∀ k, leq (f k) b) → leq (ajoin f) b
  }.

(** Choose greatest lower bounds at an index universe that contains the carrier. *)

(** 在可容纳载体的索引宇宙上选取最大下界。 *)

Minks.Mixin HasAMeet@{u o i | u <= i}
  extends HasOrder@{u o}
  :=
  { ameet {I : Type@{i}} (f : I → A) : A
  ; ameet_leq {I : Type@{i}} (f : I → A) (k : I)
    : leq (ameet f) (f k)
  ; leq_ameet {I : Type@{i}} (f : I → A) (b : A)
    : (∀ k, leq b (f k)) → leq b (ameet f)
  }.

(** Restrict the family join to two elements on the same order. *)

(** 在同一份序上将族的并限制为两个元素。 *)

Definition HasJoinOfHasAJoin {A : Type} {O : HasOrder A}
    `(J : !@HasAJoin A O)
  : @HasJoin A O.
Proof.
  refine {| join := fun x y => ajoin (fun b : bool => if b then x else y) |}.
  - intros x y. exact (leq_ajoin _ true).
  - intros x y. exact (leq_ajoin _ false).
  - intros x y z Hx Hy. apply ajoin_leq. intros []; assumption.
Defined.

(** Restrict the family meet to two elements on the same order. *)

(** 在同一份序上将族的交限制为两个元素。 *)

Definition HasMeetOfHasAMeet {A : Type} {O : HasOrder A}
    `(M : !@HasAMeet A O)
  : @HasMeet A O.
Proof.
  refine {| meet := fun x y => ameet (fun b : bool => if b then x else y) |}.
  - intros x y. exact (ameet_leq _ true).
  - intros x y. exact (ameet_leq _ false).
  - intros x y z Hx Hy. apply leq_ameet. intros []; assumption.
Defined.

(** Choose a bottom for the selected order and witness its lower bound law. *)

(** 在选定的序上选取底元，并提供它小于等于每个元素的见证。 *)

Minks.Mixin HasBottom
  extends HasOrder
  :=
  { bottom : A
  ; bottom_leq : ∀ x : A, leq bottom x
  }.

(** Choose a top for the selected order and witness its upper bound law. *)

(** 在选定的序上选取顶元，并提供每个元素小于等于它的见证。 *)

Minks.Mixin HasTop@{u o}
  extends HasOrder@{u o}
  :=
  { top : A
  ; leq_top : ∀ x : A, leq x top
  }.

(** ** Finite and complete lattices

    Both bounds extend the lattice on its already selected order. *)

(** ** 有限运算与完备格

    两个界都在格已选定的序上扩展。 *)

Minks.Struct Poset extends SetC
  with  hasOrder : HasOrder,
        isPoset : IsPoset.

Minks.Struct MeetSemilattice extends Poset
  with  hasMeet : HasMeet.

Minks.Struct JoinSemilattice extends Poset
  with  hasJoin : HasJoin.

Minks.Struct Lattice
  extends MeetSemilattice, JoinSemilattice.

Minks.Struct LatticeWithBottom extends Lattice
  with  hasBottom : HasBottom.

Minks.Struct LatticeWithTop extends Lattice
  with  hasTop : HasTop.

Minks.Struct BoundedLattice
  extends LatticeWithBottom, LatticeWithTop.

(** The complete branches add family bounds to the same chosen poset. *)

(** 两条完备分支在同一个选定偏序上加入族的界。 *)

Minks.Struct CompleteJoinSemilattice
  extends Poset
  with  hasAJoin : HasAJoin.

Minks.Struct CompleteMeetSemilattice
  extends Poset
  with  hasAMeet : HasAMeet.

Minks.Struct CompleteLattice
  extends CompleteJoinSemilattice, CompleteMeetSemilattice
  with  hasBottom : HasBottom,
        hasTop : HasTop.

(** ** Deriving binary operations

    Read the binary join from the chosen family join. *)

(** ** 导出二元运算

    从选定的族并读出二元并。 *)

Definition CompleteJoinSemilatticeToJoinSemilattice
    (L : CompleteJoinSemilattice)
  : JoinSemilattice
  := MakeJoinSemilattice L (CompleteJoinSemilattice_hasEquiv L)
       (CompleteJoinSemilattice_hasOrder L) (CompleteJoinSemilattice_isPoset L)
       (HasJoinOfHasAJoin (CompleteJoinSemilattice_hasAJoin L)).

(** Read the binary meet from the chosen family meet. *)

(** 从选定的族交读出二元交。 *)

Definition CompleteMeetSemilatticeToMeetSemilattice
    (L : CompleteMeetSemilattice)
  : MeetSemilattice
  := MakeMeetSemilattice L (CompleteMeetSemilattice_hasEquiv L)
       (CompleteMeetSemilattice_hasOrder L) (CompleteMeetSemilattice_isPoset L)
       (HasMeetOfHasAMeet (CompleteMeetSemilattice_hasAMeet L)).

(** Combine the two derived binary operations on the shared poset. *)

(** 在共享偏序上组合两份导出的二元运算。 *)

Definition CompleteLatticeToLattice (L : CompleteLattice)
  : Lattice
  := MakeLattice L (CompleteLattice_hasEquiv L) (CompleteLattice_hasOrder L)
       (CompleteLattice_isPoset L)
       (HasMeetOfHasAMeet (CompleteLattice_hasAMeet L))
       (HasJoinOfHasAJoin (CompleteLattice_hasAJoin L)).

(** Use the derived operations and the same selected bottom and top. *)

(** 使用导出的运算以及同一份选定的底元和顶元。 *)

Definition CompleteLatticeToBoundedLattice (L : CompleteLattice)
  : BoundedLattice
  := let F := CompleteLatticeToLattice L in
     MakeBoundedLattice F (Lattice_hasEquiv F) (Lattice_hasOrder F)
       (Lattice_isPoset F) (Lattice_hasMeet F) (Lattice_hasJoin F)
       (CompleteLattice_hasBottom L) (CompleteLattice_hasTop L).

Minks.Inspect BoundedLattice.

(** ** Checking the selected components

    The two inheritance paths reconstruct the same lattice. *)

(** ** 检查选定的组件

    两条继承路径重建同一个格。 *)

Definition bounded_lattice_coherence (L : BoundedLattice)
  : LatticeWithBottomToLattice (BoundedLatticeToLatticeWithBottom L) =
      LatticeWithTopToLattice (BoundedLatticeToLatticeWithTop L)
  := eq_refl.

(** The order and meet methods use the unique instances directly. *)

(** 序和交的字段可以直接使用唯一的实例。 *)

Definition meet_below_join (L : BoundedLattice) (x y : L)
  : leq (meet x y) (join x y)
  := leq_trans _ _ _ (meet_leq_l x y) (leq_join_l x y).

(** The expected carrier selects each bound and its law. *)

(** 从预期的载体推断对应的界和定律。 *)

Definition selected_bottom_law (L : BoundedLattice) (x : L)
  : leq bottom x
  := bottom_leq x.

Definition selected_top_law (L : BoundedLattice) (x : L)
  : leq x top
  := leq_top x.

(** Inference uses exactly the choices stored in the record. *)

(** 推断使用记录中保存的两份选定值。 *)

Definition bound_laws_use_fields (L : BoundedLattice) (x : L)
  : selected_bottom_law L x =
      @bottom_leq L (BoundedLattice_hasOrder L) (BoundedLattice_hasBottom L) x
    ∧ selected_top_law L x =
      @leq_top L (BoundedLattice_hasOrder L) (BoundedLattice_hasTop L) x
  := conj eq_refl eq_refl.

(** ** Subsets of a complete lattice

    Index a subset by the dependent pair of an element and its membership
    witness. The family bounds give the subset bounds directly. *)

(** ** 完备格的子集

    用元素及其成员见证组成的依赖对作为索引。族的上界和下界直接给出子集的界。 *)

Section CompleteLatticeSubsets.
Context (L : CompleteLattice).

(** Select the least upper bound of a Type-valued subset. *)

(** 选取 Type 值子集的最小上界。 *)

Definition subset_ajoin (P : L → Type)
  : L
  := ajoin (I := sigT P) (@projT1 L P).

(** Every member lies below the selected join. *)

(** 每个成员都小于等于选定的并。 *)

Definition leq_subset_ajoin (P : L → Type) (x : L) (p : P x)
  : leq x (subset_ajoin P)
  := leq_ajoin (@projT1 L P) (@existT L P x p).

(** Every upper bound lies above the selected join. *)

(** 每个上界都大于等于选定的并。 *)

Definition subset_ajoin_leq (P : L → Type) (b : L)
    (upper : ∀ x, P x → leq x b)
  : leq (subset_ajoin P) b
  := ajoin_leq (@projT1 L P) b
       (fun t : sigT P => upper (@projT1 L P t) (@projT2 L P t)).

(** Select the greatest lower bound of the same kind of subset. *)

(** 选取同一类子集的最大下界。 *)

Definition subset_ameet (P : L → Type)
  : L
  := ameet (I := sigT P) (@projT1 L P).

(** The selected meet lies below every member. *)

(** 选定的交小于等于每个成员。 *)

Definition subset_ameet_leq (P : L → Type) (x : L) (p : P x)
  : leq (subset_ameet P) x
  := ameet_leq (@projT1 L P) (@existT L P x p).

(** Every lower bound lies below the selected meet. *)

(** 每个下界都小于等于选定的交。 *)

Definition leq_subset_ameet (P : L → Type) (b : L)
    (lower : ∀ x, P x → leq b x)
  : leq b (subset_ameet P)
  := leq_ameet (@projT1 L P) b
       (fun t : sigT P => lower (@projT1 L P t) (@projT2 L P t)).

End CompleteLatticeSubsets.

(** Both complete branches read the same chosen order. *)

(** 完备格的两条分支读取同一份选定偏序。 *)

Example complete_lattice_order_coherence (L : CompleteLattice)
  : CompleteJoinSemilattice_hasOrder (CompleteLatticeToCompleteJoinSemilattice L)
    = CompleteMeetSemilattice_hasOrder (CompleteLatticeToCompleteMeetSemilattice L)
  := eq_refl.

(** Empty families recover the selected bounds in the setoid equality. *)

(** 空族的并和交分别与选定的底元和顶元广集相等。 *)

Definition ajoin_empty (L : CompleteLattice)
  : equiv (ajoin (fun t : Empty_set => match t return L with end)) (bottom : L).
Proof.
  apply leq_antisym.
  - apply ajoin_leq. intros k. destruct k.
  - apply bottom_leq.
Defined.

Definition ameet_empty (L : CompleteLattice)
  : equiv (ameet (fun t : Empty_set => match t return L with end)) (top : L).
Proof.
  apply leq_antisym.
  - apply leq_top.
  - apply leq_ameet. intros k. destruct k.
Defined.

(** The binary operations of the finite view compute by the chosen family
    operations. *)

(** 有限格视图中的二元运算通过选定的族运算计算。 *)

Example complete_lattice_meet_computes (L : CompleteLattice) (x y : L)
  : @meet L (CompleteLattice_hasOrder L)
      (Lattice_hasMeet (CompleteLatticeToLattice L)) x y
    = ameet (fun b : bool => if b then x else y)
  := eq_refl.

Example complete_lattice_join_computes (L : CompleteLattice) (x y : L)
  : @join L (CompleteLattice_hasOrder L)
      (Lattice_hasJoin (CompleteLatticeToLattice L)) x y
    = ajoin (fun b : bool => if b then x else y)
  := eq_refl.
