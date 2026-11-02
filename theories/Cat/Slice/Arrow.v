From Cats Require Import
  Cat.Core
  Cat.Functor
  Cat.Natural
  Cat.Slice
  Cat.Slice.Reindex.
From Cats Require Import
  Cat.Arrow
  Cat.Arrow.Fibration
  Cat.Pullback
  Cat.Fibration.

(** * Slices and Codomain Lifts

    A slice map is a square over the identity. The same chosen pullback
    supplies slice reindexing and the corresponding codomain lift. *)

(** * 切片与余域提升

    切片映射是底边为恒等的方形；同一个选定拉回同时给出切片重索引和对应的余域提
    升。 *)

Program Definition SliceArrowOb {C : Cat} {X : @Ob C} (A : SliceOb C X)
  : ArrowOb C
  :=
  {|arrow_dom := slice_dom A
  ; arrow_cod := X
  ; arrow_map := slice_arrow A
  |}.

Notation "A '^Arr'" := (SliceArrowOb A) (at level 8, left associativity) : cat_scope.

(** Regard a commuting slice triangle as a square over the identity. *)

(** 将切片交换三角形视为恒等基底上的方形。 *)

Program Definition slice_to_square {C : Cat} {X : @Ob C} {A B : SliceOb C X}
    (h : SliceHom A B)
  : ArrowHom A^Arr B^Arr
  :=
  {|arrow_top := slice_map h
  ; arrow_bottom := id
  |}.
Next Obligation. rewrite comp_id_l. apply slice_comm. Defined.

(** Embed a slice category into the arrow category. *)

(** 将切片范畴嵌入箭头范畴。 *)

Program Definition SliceArrowF (C : Cat) (X : @Ob C)
  : Functor (C /C X) (Arr C)
  :=
  {|F0 := SliceArrowOb
  ; F1 A B := slice_to_square
  |}.
Next Obligation. intros h k H. split; [exact H | reflexivity]. Defined.
Next Obligation. split; reflexivity. Defined.
Next Obligation. split; [reflexivity | symmetry; apply comp_id_l]. Defined.

(** The embedding of a slice into the arrow category reflects equality. *)

(** 切片到箭头范畴的嵌入反映相等。 *)

Theorem slice_arrow_faithful {C : Cat} (X : @Ob C)
  : is_faithful (SliceArrowF C X).
Proof. intros A B h k H. exact (fst H). Defined.

(** Recover a slice arrow from a square whose base map is equivalent to
    identity. *)

(** 由基底映射等价于恒等的方形恢复切片箭头。 *)

Program Definition square_to_slice {C : Cat} {X : @Ob C} {A B : SliceOb C X}
    (f : ArrowHom A^Arr B^Arr) (H : arrow_bottom f ≈ id)
  : SliceHom A B
  :=
  {|slice_map := arrow_top f
  |}.
Next Obligation. rewrite (arrow_comm f), H, comp_id_l. reflexivity. Defined.

(** Turning a slice arrow into a square and back preserves its underlying
    arrow. *)

(** 将切片箭头转为方形再返回，保持底层箭头。 *)

Theorem slice_square_round_trip {C : Cat} {X : @Ob C} {A B : SliceOb C X}
    (f : ArrowHom A^Arr B^Arr) (H : arrow_bottom f ≈ id)
  : slice_to_square (square_to_slice f H) ≈Arr f.
Proof. split; [reflexivity | symmetry; exact H]. Defined.

(** Turning an identity-base square into a slice map and back preserves its
    sides. *)

(** 将恒等基底方形转为切片映射再返回，保持其侧边。 *)

Theorem square_slice_round_trip {C : Cat} {X : @Ob C} {A B : SliceOb C X}
    (h : SliceHom A B) (H : arrow_bottom (slice_to_square h) ≈ id)
  : slice_map (square_to_slice (slice_to_square h) H) ≈ slice_map h.
Proof. reflexivity. Defined.

Section SliceCodomainLifts.
Context {C : Cat} `{HP : !HasPullback C}.

(** The source type checks by computation: (A[f]C)^Arr is A^Arr[f]Arr. *)

(** 源类型通过计算对齐：[(A[f]C)^Arr] 就是 [A^Arr[f]Arr]。 *)

Definition slice_reindex_square {X Y : @Ob C} (f : Hom X Y) (A : SliceOb C Y)
  : ArrowHom (A[f]C)^Arr A^Arr
  := arrow_reindex A^Arr f.

(** The square underlying slice base change is codomain-cartesian. *)

(** 切片基变换的底层方形对余域函子是笛卡尔的。 *)

Definition slice_reindex_square_cartesian {X Y : @Ob C} (f : Hom X Y)
    (A : SliceOb C Y)
  : slice_reindex_square f A ⦂ Cart(ArrowCodF C)
  := arrow_reindex_cartesian A^Arr f.

(** The chosen base-change squares assemble naturally over slice morphisms. *)

(** 选定基变换方形在切片态射上组成自然变换。 *)

Program Definition SliceReindexSquareN {X Y : @Ob C} (f : Hom X Y)
  : (SliceArrowF C X ∘F SliceReindexF f) ⇒ SliceArrowF C Y
  :=
  {|nt := slice_reindex_square f
  |}.
Next Obligation.
  split.
  - apply slice_reindex_map_β2.
  - change (f ∘ id ≈ id ∘ f). rewrite comp_id_r, comp_id_l. reflexivity.
Defined.

(** Reindexing a slice map is the cartesian factor of the corresponding
    square. *)

(** 切片映射的重索引是对应方形的笛卡尔分解中介。 *)

Theorem slice_reindex_map_cartesian_factor {X Y : @Ob C} (f : Hom X Y)
    {A B : SliceOb C Y} (h : SliceHom A B)
  : slice_to_square (slice_reindex_map f h) ≈Arr
    cartesian_factor (slice_reindex_square_cartesian f B)
      (slice_to_square h ∘Arr slice_reindex_square f A) id
      (transitivity (comp_id_r f) (symmetry (comp_id_l f))).
Proof.
  apply (that _ _ (cartesian_factor_unique (slice_reindex_square_cartesian f B)
    (slice_to_square h ∘Arr slice_reindex_square f A) id
    (transitivity (comp_id_r f) (symmetry (comp_id_l f))))).
  split; [reflexivity | exact (nt_naturality (SliceReindexSquareN f) h)].
Qed.

(** The existing unit and composition comparisons are the cartesian
    comparisons. *)

(** 已有单位与复合比较正是笛卡尔比较。 *)

Theorem slice_reindex_square_id {X : @Ob C} (A : SliceOb C X)
  : slice_reindex_square id A ∘Arr slice_to_square (slice_reindex_id A)
      ≈Arr arrow_id A^Arr.
Proof.
  split.
  - apply slice_reindex_lift_β2.
  - apply comp_id_l.
Qed.

(** Compatibility with composition for [slice_reindex_square]. *)

(** [slice_reindex_square] 与复合的相容性。 *)

Theorem slice_reindex_square_comp {X Y Z : @Ob C} (f : Hom Y Z) (g : Hom X Y)
    (A : SliceOb C Z)
  : slice_reindex_square (f ∘ g) A ∘Arr slice_to_square A⟨f, g⟩C ≈Arr
    slice_reindex_square f A ∘Arr slice_reindex_square g A[f]C.
Proof.
  split.
  - apply slice_reindex_lift_β2.
  - apply comp_id_r.
Qed.

(** The slice identity comparison is the corresponding cartesian factor. *)

(** 切片恒等比较就是对应的笛卡尔分解。 *)

Theorem slice_reindex_id_cartesian_factor {X : @Ob C} (A : SliceOb C X)
  : slice_to_square (slice_reindex_id A) ≈Arr
    cartesian_factor (slice_reindex_square_cartesian id A) (arrow_id A^Arr) id
      (comp_id_l id).
Proof.
  apply (that _ _ (cartesian_factor_unique (slice_reindex_square_cartesian id A)
    (arrow_id A^Arr) id (comp_id_l id))).
  split; [reflexivity | apply slice_reindex_square_id].
Qed.

(** The slice composition comparison is the corresponding cartesian factor. *)

(** 切片复合比较就是对应的笛卡尔分解。 *)

Theorem slice_reindex_comp_cartesian_factor {X Y Z : @Ob C}
    (f : Hom Y Z) (g : Hom X Y) (A : SliceOb C Z)
  : slice_to_square A⟨f, g⟩C ≈Arr
    cartesian_factor (slice_reindex_square_cartesian (f ∘ g) A)
      (slice_reindex_square f A ∘Arr slice_reindex_square g A[f]C) id
      (comp_id_r (f ∘ g)).
Proof.
  apply (that _ _ (cartesian_factor_unique (slice_reindex_square_cartesian (f ∘ g) A)
    (slice_reindex_square f A ∘Arr slice_reindex_square g A[f]C) id
    (comp_id_r (f ∘ g)))).
  split; [reflexivity | apply slice_reindex_square_comp].
Qed.

End SliceCodomainLifts.
