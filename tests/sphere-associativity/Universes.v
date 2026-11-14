From Cats Require Import
  Instance.Set.Simplicial.Homotopy.SphereAssociativity.

Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Independent Sizes and Minimal Associativity Choices

    A supplied actual filler needs no choice. Rebracketing selects only
    dimension-four missing face three; class comparison adds only missing
    face two. Multiplication choices remain independent explicit data. *)

(** * 独立大小与结合律的最小选择

    给定实际填充无需选择；重括号仅选择四维缺第三面，类比较只另加缺第二面。
    乘法选择保持为独立显式数据。 *)

(** ** Strict Levels

    Fix strictly increasing levels, probing simplex equality both below
    and above the carrier. The laws must retain those independent sizes. *)

(** ** 严格层级

    固定严格递增层级，分别检查低于及高于载体的单形相等；定律须保留独立大小。 *)

Section StrictSizes.
Universes l u p.
Constraint l < u, u < p.

(** Read a supplied filler without any chosen structure. *)

(** 无需选定结构即可读取给定填充。 *)

Definition lower_given
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    (x y z s t l : TwoSphereS X b)
    (A : TwoSphereComposite X b x y s)
    (B : TwoSphereComposite X b y z t)
    (C : TwoSphereComposite X b s z l)
    (V : X 4) (HV : is_horn_filler (SphereAssociativityHornN X b A B C) V)
  : TwoSphereComposite X b x t l
  := SphereCompositeReassociateOfFiller X b A B C V HV.

(** Rebracketing needs only missing-face-three four-horns. *)

(** 重括号仅需四维缺第三面的 horn。 *)

Definition lower_rebracket
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (x y z s t l : TwoSphereS X b)
    (A : TwoSphereComposite X b x y s)
    (B : TwoSphereComposite X b y z t)
    (C : TwoSphereComposite X b s z l)
  : TwoSphereComposite X b x t l
  := SphereCompositeReassociate X b A B C.

(** Compare arbitrary supplied composites without a three-horn selection. *)

(** 比较任意给定合成，不需三维 horn 选择。 *)

Definition lower_comparison
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (x y z s t l : TwoSphereS X b)
    (A : TwoSphereComposite X b x y s)
    (B : TwoSphereComposite X b y z t)
    (C : TwoSphereComposite X b s z l)
    (r : TwoSphereS X b) (D : TwoSphereComposite X b x t r)
  : (l : TwoSphereClassS X b) ≈S r
  := two_sphere_composite_assoc X b A B C D.

(** The selected associativity law uses no missing-face-four selection. *)

(** 选定结合律不需缺第四面的选择。 *)

Definition lower_selected
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺) (x y z : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H (two_sphere_kan_mul X b H x y) z ≈S
      two_sphere_kan_mul X b H x (two_sphere_kan_mul X b H y z)
  := two_sphere_kan_mul_assoc X b H x y z.

(** Four independent multiplication choices are covered by the supplied
    composite theorem, without identifying their choices or witnesses. *)

(** 给定合成定理涵盖四个独立乘法选择，不等同选择或见证。 *)

Definition lower_independent
    (X : Fct (Δ^op) SetCat@{u l _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (H1 H2 H3 H4 : HasHornFillers X 3 fin_first⁺⁺)
    (x y z : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H3 (two_sphere_kan_mul X b H1 x y) z ≈S
      two_sphere_kan_mul X b H4 x (two_sphere_kan_mul X b H2 y z).
Proof.
  exact (two_sphere_composite_assoc X b
    (TwoSphereKanMulComposite X b H1 x y)
    (TwoSphereKanMulComposite X b H2 y z)
    (TwoSphereKanMulComposite X b H3 (two_sphere_kan_mul X b H1 x y) z)
    (TwoSphereKanMulComposite X b H4 x (two_sphere_kan_mul X b H2 y z))).
Defined.

(** Read a supplied filler without any chosen structure. *)

(** 无需选定结构即可读取给定填充。 *)

Definition higher_given
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    (x y z s t l : TwoSphereS X b)
    (A : TwoSphereComposite X b x y s)
    (B : TwoSphereComposite X b y z t)
    (C : TwoSphereComposite X b s z l)
    (V : X 4) (HV : is_horn_filler (SphereAssociativityHornN X b A B C) V)
  : TwoSphereComposite X b x t l
  := SphereCompositeReassociateOfFiller X b A B C V HV.

(** Rebracketing needs only missing-face-three four-horns. *)

(** 重括号仅需四维缺第三面的 horn。 *)

Definition higher_rebracket
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (x y z s t l : TwoSphereS X b)
    (A : TwoSphereComposite X b x y s)
    (B : TwoSphereComposite X b y z t)
    (C : TwoSphereComposite X b s z l)
  : TwoSphereComposite X b x t l
  := SphereCompositeReassociate X b A B C.

(** Compare arbitrary supplied composites without a three-horn selection. *)

(** 比较任意给定合成，不需三维 horn 选择。 *)

Definition higher_comparison
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (x y z s t l : TwoSphereS X b)
    (A : TwoSphereComposite X b x y s)
    (B : TwoSphereComposite X b y z t)
    (C : TwoSphereComposite X b s z l)
    (r : TwoSphereS X b) (D : TwoSphereComposite X b x t r)
  : (l : TwoSphereClassS X b) ≈S r
  := two_sphere_composite_assoc X b A B C D.

(** The selected associativity law uses no missing-face-four selection. *)

(** 选定结合律不需缺第四面的选择。 *)

Definition higher_selected
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (H : HasHornFillers X 3 fin_first⁺⁺) (x y z : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H (two_sphere_kan_mul X b H x y) z ≈S
      two_sphere_kan_mul X b H x (two_sphere_kan_mul X b H y z)
  := two_sphere_kan_mul_assoc X b H x y z.

(** Four independent multiplication choices are covered by the supplied
    composite theorem, without identifying their choices or witnesses. *)

(** 给定合成定理涵盖四个独立乘法选择，不等同选择或见证。 *)

Definition higher_independent
    (X : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) (b : X 0)
    `{HX2 : !HasHornFillers X 4 fin_first⁺⁺}
    `{HX3 : !HasHornFillers X 4 fin_first⁺⁺⁺}
    (H1 H2 H3 H4 : HasHornFillers X 3 fin_first⁺⁺)
    (x y z : TwoSphereClassS X b)
  : two_sphere_kan_mul X b H3 (two_sphere_kan_mul X b H1 x y) z ≈S
      two_sphere_kan_mul X b H4 x (two_sphere_kan_mul X b H2 y z).
Proof.
  exact (two_sphere_composite_assoc X b
    (TwoSphereKanMulComposite X b H1 x y)
    (TwoSphereKanMulComposite X b H2 y z)
    (TwoSphereKanMulComposite X b H3 (two_sphere_kan_mul X b H1 x y) z)
    (TwoSphereKanMulComposite X b H4 x (two_sphere_kan_mul X b H2 y z))).
Defined.

End StrictSizes.
