From Cats Require Import
  Instance.Set.Simplicial.Homotopy.Core
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Independent Carrier and Equality Sizes for Homotopies *)

(** * 同伦的独立载体及相等大小 *)

Section LowNativeEquality.
Universes e h o l.
Constraint e < h.
Constraint h < o.
Constraint o < l.
Context (C : Cat@{o h e l l}) (TC : HasTerminal C) (PC : HasProduct C).
Local Existing Instance TC.
Local Existing Instance PC.
Context (I : Interval C) (X Y Z : @Ob C)
    (f : Hom X Y) (g : Hom Y Z).

(** The equality of witnesses stays below the native map carrier. *)

(** 见证相等保持低于原生映射载体。 *)

Definition low_native_constant
  : f ∼[I] f
  := ConstantHomotopy I f.

Definition low_native_witness_equality
  : Type@{e}
  := HomotopyEq low_native_constant low_native_constant.

Definition low_native_composition
  : (g ∘ f) ∼[I] (g ∘ f)
  := CompHomotopy (ConstantHomotopy I g) low_native_constant.

End LowNativeEquality.

Section HighNativeEquality.
Universes h e o l.
Constraint h < e.
Constraint e < o.
Constraint o < l.
Context (C : Cat@{o h e l l}) (TC : HasTerminal C) (PC : HasProduct C).
Local Existing Instance TC.
Local Existing Instance PC.
Context (I : Interval C) (X Y : @Ob C) (f : Hom X Y).

(** Reversing the native order does not change the interface. *)

(** 反转原生大小次序不改变接口。 *)

Definition high_native_constant
  : f ∼[I] f
  := ConstantHomotopy I f.

Definition high_native_witness_equality
  : Type@{e}
  := HomotopyEq high_native_constant high_native_constant.

End HighNativeEquality.

Section LowValueEquality.
Universes r u.
Constraint r < u.
Context (X Y Z : Fct (Δ^op) SetCat@{u r _ _ _ _ _})
    (f g : X ⇒ Y) (a b : Y ⇒ Z) (H : f ∼Δ g) (K : a ∼Δ b).

(** Value equality need not contain the value carrier. *)

(** 值相等无需包含值载体。 *)

Definition low_value_constant
  : f ∼Δ f
  := SimplicialConstantHomotopy f.

Definition low_value_precomposition
  : (f ∘Nv idN) ∼Δ (g ∘Nv idN)
  := SimplicialPreHomotopy H idN.

Definition low_value_postcomposition
  : (a ∘Nv f) ∼Δ (a ∘Nv g)
  := SimplicialPostHomotopy a H.

Definition low_value_composition
  : (a ∘Nv f) ∼Δ (b ∘Nv g)
  := SimplicialCompHomotopy K H.

Definition low_value_endpoint
  : (homotopy_map H ∘Nv SimplicialEndpointN X false) ≈N f
  := simplicial_homotopy_0 H.

End LowValueEquality.

Section HighValueEquality.
Universes u r.
Constraint u < r.
Context (X Y : Fct (Δ^op) SetCat@{u r _ _ _ _ _}) (f : X ⇒ Y).

(** The opposite strict value-size order supports the same constructions. *)

(** 相反的严格值大小次序支持相同构造。 *)

Definition high_value_constant
  : f ∼Δ f
  := SimplicialConstantHomotopy f.

Definition high_value_interval
  : (SimplicialConstantPointN X false) ∼Δ (SimplicialConstantPointN X true)
  := SimplicialIntervalHomotopy X.

End HighValueEquality.
