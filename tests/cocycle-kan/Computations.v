From Cats Require Import
  Algebra.Group.Cocycle
  Instance.Bool.CocycleKan.

Local Open Scope ordinal_scope.

(** * Computing Chosen Horn Fillers

    Imports retain explicit selection of coefficient and Kan structures.
    After enabling them locally, inspect actual selected simplices in all
    five branches of the construction. *)

(** * 计算选定 Horn 填充

    导入后仍须显式选定系数及 Kan 结构。局部启用之后，读取构造全部五种分支
    中实际选定的单形。 *)

Fail Definition unchosen_boolean_group
  : Group BoolS
  := _.

Fail Definition unchosen_boolean_commutativity
  : @IsCommutativeMonoid BoolS BoolS_Monoid
  := _.

Fail Definition unchosen_boolean_Kan
  : HasKanFillers BoolCocycleModel
  := _.

Local Existing Instance BoolS_Group.
Local Existing Instance BoolCocycleModel_HasKanFillers.

(** Fill the actual restriction of a supplied simplex. The theorem does
    not promise to recover that simplex in the nonunique second dimension. *)

(** 填充给定单形的实际限制；定理不承诺在非唯一的二维恢复原单形。 *)

Definition bool_chosen_filler {n : nat} (i : Ordinal (S n))
    (x : BoolCocycleModel (S n))
  : BoolCocycleModel (S n)
  := (horn_fill (x↾Λ[BoolCocycleModel; S n; i])).1.

(** The one-dimensional branch selects the unit edge. *)

(** 一维分支选取单位边。 *)

Example one_horn_computes (i : Ordinal 1)
  : (lower (bool_chosen_filler i (two_cocycle_simplex_unit 1)))⟦
      ordinal_step fin_first,
      (@Cat.Core.id [Ord 1] (fin_next fin_first))⟧₂ = false.
Proof. reflexivity. Defined.

(** A two-horn sees only edges, so its selected triangle can have a
    different label from the original triangle. *)

(** 二维 horn 只看到边，因此选定三角形的标签可以与原三角形不同。 *)

Example two_horn_computes (i : Ordinal 2)
  : two_cocycle_triangle_value_resp
      (bool_chosen_filler i bool_cocycle_triangle) = false.
Proof. reflexivity. Defined.

(** A nonconstant coefficient table exercises all four missing faces. *)

(** 非常值系数表检验四种缺失面。 *)

Definition bool_tetrahedron
  : BoolCocycleModel 3
  :=
  {|lower := TetrahedronTwoCocycle false true true false eq_refl
  |}.

(** Every three-horn completion computes all four original coefficients,
    including the missing face rather than only retained faces. *)

(** 每个三维 horn 补全均计算出原来的四个系数，也包括缺失面而不只是保留面。 *)

Example three_horns_compute (i : Ordinal 3)
  : (two_cocycle_triangle_value_resp
        (d[BoolCocycleModel; 2; fin_first]
          (bool_chosen_filler i bool_tetrahedron)),
      two_cocycle_triangle_value_resp
        (d[BoolCocycleModel; 2; fin_first⁺]
          (bool_chosen_filler i bool_tetrahedron)),
      two_cocycle_triangle_value_resp
        (d[BoolCocycleModel; 2; fin_first⁺⁺]
          (bool_chosen_filler i bool_tetrahedron)),
      two_cocycle_triangle_value_resp
        (d[BoolCocycleModel; 2; fin_first⁺⁺⁺]
          (bool_chosen_filler i bool_tetrahedron))) =
      (true, true, false, false).
Proof. destruct i as [[] | [[] | [[] | [[] | []]]]]; reflexivity. Defined.

(** A normalized table with three nonunit triangles exercises the critical
    fourth-dimensional branch. All five equations compute by xor. *)

(** 含三个非单位三角形的归一化表检验关键四维分支，五条方程均由异或计算。 *)

Definition bool_four_simplex
  : BoolCocycleModel 4
  :=
  {|lower := PentachoronTwoCocycle true false false true true
      false false false false false
      eq_refl eq_refl eq_refl eq_refl eq_refl
  |}.

(** Even when its containing tetrahedron is omitted, triangle 012 is
    retained and its coefficient computes to the original value. *)

(** 即使省去包含它的某个四面体，三角形 012 仍被保留，其系数计算为原值。 *)

Example four_horns_compute (i : Ordinal 4)
  : two_cocycle_triangle_value_resp
      (BoolCocycleModel[δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺⁺]]Δ
        (bool_chosen_filler i bool_four_simplex)) = true.
Proof.
  destruct i as [[] | [[] | [[] | [[] | [[] | []]]]]]; reflexivity.
Defined.

(** Every five-horn branch reconstructs the unit table from its actual
    restrictions. Both outer indices and every inner index are checked. *)

(** 每个五维 horn 分支均从实际限制重构单位表，检查两个外索引及全部内索引。 *)

Example five_horns_compute (i : Ordinal 5)
  : two_cocycle_triangle_value_resp
      (BoolCocycleModel[δ[4; fin_first⁺⁺⁺⁺⁺] ∘F
        δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺⁺]]Δ
        (bool_chosen_filler i (two_cocycle_simplex_unit 5))) = false.
Proof.
  destruct i as [[] | [[] | [[] | [[] | [[] | [[] | []]]]]]]; reflexivity.
Defined.

(** A larger stable dimension follows the recursive family rather than a
    finite list of hard-coded dimensions. *)

(** 更大的稳定维度沿递归族计算，而非沿有限个写死的维度列表计算。 *)

Example six_horn_computes
  : two_cocycle_triangle_value_resp
      (BoolCocycleModel[δ[5; fin_first⁺⁺⁺⁺⁺⁺] ∘F δ[4; fin_first⁺⁺⁺⁺⁺] ∘F
        δ[3; fin_first⁺⁺⁺⁺] ∘F δ[2; fin_first⁺⁺⁺]]Δ
        (bool_chosen_filler fin_first⁺⁺⁺
          (two_cocycle_simplex_unit 6))) = false.
Proof. reflexivity. Defined.
