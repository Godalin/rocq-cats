From Cats Require Import
  Cat.Diagram.PrismReconstruction
  Cat.Diagram.Core
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * A Directed Time Edge Survives Reconstruction

    Use the generating arrow of the walking arrow as a transformation
    between constant functors. Its component is not invertible. Both
    boundaries and the recovered time arrow must compute transparently. *)

(** * 重建保留有向时间边

    用步行箭头的生成箭头作为常值函子之间的自然变换，其分量不可逆。
    两个边界及恢复出的时间箭头都须透明计算。 *)

Definition InitialF
  : Functor ArrowShape ArrowShape
  := ConstF ArrowShape (C := ArrowShape) false.

Definition FinalF
  : Functor ArrowShape ArrowShape
  := ConstF ArrowShape (C := ArrowShape) true.

Program Definition DirectedN
  : InitialF ⇒ FinalF
  :=
  {|nt x := tt
  |}.
Next Obligation. exact tt. Defined.

(** The reverse component would be an inhabitant of the empty hom. *)

(** 反向分量将成为空 Hom 的元素。 *)

Example directed_not_invertible
  : (DirectedN ⦂ InitialF ≅N FinalF) → Empty_set.
Proof. intros H. exact (H false).1. Defined.

(** The extracted boundaries retain their distinct concrete objects. *)

(** 提取的边界保留两个不同的具体对象。 *)

Example initial_boundary_computes
  : π1F (NaturalPrismF DirectedN) fin_first true = false.
Proof. reflexivity. Qed.

Example final_boundary_computes
  : π1F (NaturalPrismF DirectedN) (fin_next fin_first) false = true.
Proof. reflexivity. Qed.

(** Extraction returns the actual noninvertible witness. Native equality
    here only compares the concrete unit-valued hom of the walking arrow. *)

(** 提取返回实际的不可逆见证；此处原生相等仅比较步行箭头中取值为 unit
    的具体 Hom。 *)

Example directed_time_edge_computes
  : PrismTransformationN (NaturalPrismF DirectedN) false = tt.
Proof. reflexivity. Qed.

(** The inverse of reconstruction remains an explicitly stored identity. *)

(** 重建的逆仍为显式存储的恒等。 *)

Example reconstruction_inverse_computes
  : ((prism_reconstruction_iso (NaturalPrismF DirectedN)).2
      (false, fin_first)).1 = tt.
Proof. reflexivity. Qed.
