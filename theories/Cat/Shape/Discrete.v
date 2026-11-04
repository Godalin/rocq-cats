From Cats Require Export Cat.Free.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core.

(** * Discrete Index Categories *)

(** * 离散索引范畴 *)

(** The free category on a graph without edges. *)

(** 无边图上的自由范畴。 *)

Definition DiscreteCat (V : Type)
  := FreeCat (DiscreteGraph V).

(** The discrete shape with no objects. *)

(** 没有对象的离散形状。 *)

Definition EmptyShape
  := DiscreteCat Empty_set.
(** The discrete shape with one object. *)

(** 仅有一个对象的离散形状。 *)

Definition PointShape
  := DiscreteCat unit.
(** The discrete shape with two objects. *)

(** 具有两个对象的离散形状。 *)

Definition PairShape
  := DiscreteCat bool.

(** Discrete shapes are self-dual by path reversal, without identifying
    their category records. *)

(** 离散形状通过路径反转自对偶，无需认同范畴记录。 *)

Definition OpDiscreteF (I : Type)
  : Functor (DiscreteCat I) ((DiscreteCat I)^op)
  := OpFreeF (DiscreteGraph I).

(** The inverse self-duality reads reversed discrete paths back. *)

(** 自对偶的逆向映射将反离散路径读回。 *)

Definition UnopDiscreteF (I : Type)
  : Functor ((DiscreteCat I)^op) (DiscreteCat I)
  := UnopFreeF (DiscreteGraph I).

(** Self-duality retains chosen arrow preimages in both directions. *)

(** 自对偶双向保留选定箭头原像。 *)

Definition op_discrete_full (I : Type)
  : is_full (OpDiscreteF I)
  := op_free_full (DiscreteGraph I).

(** The inverse discrete comparison is full. *)

(** 逆离散比较为满。 *)

Definition unop_discrete_full (I : Type)
  : is_full (UnopDiscreteF I)
  := unop_free_full (DiscreteGraph I).

(** The comparison retains all discrete objects. *)

(** 比较保留全部离散对象。 *)

Definition op_discrete_essentially_surjective (I : Type)
  : is_essentially_surjective (OpDiscreteF I)
  := op_free_essentially_surjective (DiscreteGraph I).

(** The inverse comparison retains all discrete objects. *)

(** 逆向比较保留全部离散对象。 *)

Definition unop_discrete_essentially_surjective (I : Type)
  : is_essentially_surjective (UnopDiscreteF I)
  := unop_free_essentially_surjective (DiscreteGraph I).
