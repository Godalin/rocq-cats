From Cats Require Import
  Cat.Core
  Cat.Functor.

(** * Slice Categories

    Commuting triangles use [HomEq]. Their witnesses are retained as data,
    while morphism equivalence compares only the underlying arrows. *)

(** * 切片范畴

    交换三角形使用 [HomEq] 并保留见证；态射相等只比较底层箭头。 *)

Record SliceOb (C : Cat) (X : @Ob C)
  :=
  { slice_dom : @Ob C
  ; slice_arrow : Hom slice_dom X
  }.

Arguments slice_dom {_ _} _.
Arguments slice_arrow {_ _} _.

(** An arrow commuting with the two maps into the fixed base. *)

(** 与两个指向固定基底的映射交换的箭头。 *)

Record SliceHom {C : Cat} {X : @Ob C} (A B : SliceOb C X)
  :=
  { slice_map : Hom (slice_dom A) (slice_dom B)
  ; slice_comm : slice_arrow B ∘ slice_map ≈ slice_arrow A
  }.

Arguments slice_map {_ _ _ _} _.
Arguments slice_comm {_ _ _ _} _.

(** The identity slice arrow, retaining its triangle witness. *)

(** 保留三角形见证的恒等切片箭头。 *)

Program Definition slice_id {C : Cat} {X : @Ob C} (A : SliceOb C X)
  : SliceHom A A
  :=
  {|slice_map := id
  |}.
Next Obligation. apply comp_id_r. Defined.

(** Compose slice arrows and their commuting triangles. *)

(** 复合切片箭头及其交换三角形。 *)

Program Definition slice_comp {C : Cat} {X : @Ob C} {A B D : SliceOb C X}
    (g : SliceHom B D) (f : SliceHom A B)
  : SliceHom A D
  :=
  {|slice_map := slice_map g ∘ slice_map f
  |}.
Next Obligation.
  rewrite <- comp_assoc, (slice_comm g). apply slice_comm.
Defined.

Infix "∘/C" := slice_comp
  (at level 40, left associativity) : cat_scope.

(** The category of arrows into a fixed object, with commuting triangles. *)

(** 指向固定对象的箭头及其交换三角形组成的范畴。 *)

Program Definition Slice (C : Cat) (X : @Ob C)
  : Cat
  :=
  {|Ob := SliceOb C X
  ; HomSet A B :=
      {|carrier := SliceHom A B
      ; carrier_equiv f g := slice_map f ≈ slice_map g
      |}
  ; id := slice_id
  ; comp A B D := slice_comp
  |}.
Next Obligation.
  split.
  - intros f. reflexivity.
  - intros f g H. symmetry. exact H.
  - intros f g h Hfg Hgh. transitivity (slice_map g); assumption.
Defined.
Next Obligation. intros g g' Hg f f' Hf. now apply comp_proper. Defined.
Next Obligation. apply comp_id_r. Defined.
Next Obligation. apply comp_id_l. Defined.
Next Obligation. apply comp_assoc. Defined.

Notation "C '/C' X" := (Slice C X)
  (at level 40, no associativity) : cat_scope.

(** Forget a slice object to its domain and a slice map to its underlying
    arrow. *)

(** 将切片对象忘却为定义域，将切片映射忘却为底层箭头。 *)

Program Definition SliceDomF (C : Cat) (X : @Ob C)
  : Functor (C /C X) C
  :=
  {|F0 := slice_dom
  ; F1 A B := slice_map
  |}.
Next Obligation. intros f g H. exact H. Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.
