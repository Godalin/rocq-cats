From Cats Require Import
  Instance.Bool.CocycleModel
  Instance.Set.Simplicial.Horn.

(** * Computing with the Boolean Model

    Inspect the retained triangle label, face restrictions and repeated
    positions. These checks exercise the actual simplicial functor rather
    than only the earlier standalone cocycle. *)

(** * 计算布尔模型

    检查保存的三角形标签、面限制及重复位置。这些检查使用实际的单纯函子，
    不仅是先前独立的 cocycle。 *)

Fail Definition unchosen_boolean_monoid
  : Monoid BoolS
  := ltac:(typeclasses eauto).

(** A simplicial model alone does not implicitly select Kan fillers. *)

(** 仅有单纯模型并不会隐式选定 Kan 填充。 *)

Fail Definition unchosen_boolean_cocycle_fillers
  : HasKanFillers BoolCocycleModel
  := ltac:(typeclasses eauto).

(** The increasing triangle retains its actual Boolean coefficient. *)

(** 严格递增三角形保留实际的布尔系数。 *)

Example triangle_label_computes
  : two_cocycle_triangle_value_resp bool_cocycle_triangle = true.
Proof. reflexivity. Qed.

Example unit_label_computes
  : two_cocycle_triangle_value_resp bool_cocycle_unit_triangle = false.
Proof. reflexivity. Qed.

Example identity_restriction_computes
  : two_cocycle_triangle_value_resp
      (BoolCocycleModel[(id : (@Hom Δ) 2 2)]Δ bool_cocycle_triangle) = true.
Proof. reflexivity. Qed.

(** Each of the three actual faces has the unit triangle label on its
    repeated-position test triangle in degree one. *)

(** 三个实际的面在一维的重复位置测试三角形上均具有单位标签。 *)

Example face_labels_compute (i : Fin@{Set} 3)
  : (lower (d[BoolCocycleModel; 1; i] bool_cocycle_triangle))⟦
      @Cat.Core.id [Ord 1] fin_first, ordinal_step fin_first⟧₂ = false.
Proof. destruct i as [[] | [[] | [[] | []]]]; reflexivity. Qed.

Example degenerate_triangle_labels_compute (i : Fin@{Set} 2)
  : two_cocycle_triangle_value_resp
      (s[BoolCocycleModel; 1; i] (two_cocycle_simplex_unit 1)) = false.
Proof. destruct i as [[] | [[] | []]]; reflexivity. Qed.

(** Selection after repetition reads positions 0,0,2, so it is normalized. *)

(** 重复之后再选择，读取位置 0、0、2，因此由归一化得到单位。 *)

Example collapsed_operator_computes
  : two_cocycle_triangle_value_resp
      (BoolCocycleModel[δ[1; fin_next fin_first] ∘ σ[1; fin_first]]Δ
        bool_cocycle_triangle) = false.
Proof. reflexivity. Qed.
