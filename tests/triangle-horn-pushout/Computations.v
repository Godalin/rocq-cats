From Cats Require Import
  Instance.Set.Simplicial.TriangleAttachment
  Instance.Bool.CocycleKan
  Cat.Diagram.Core
  Cat.Core.
From Stdlib Require Import
  Lists.List.

Import Cats.Cat.Core ListNotations.
Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Every Concrete Step Retains Its New Cell

    Boolean equality witnesses expose native-distinct filler choices.
    The extension uses the actual geometric square, not an identity
    attachment, and reads both new-cell and old-region values. *)

(** * 每个具体步骤保留其新增单形

    布尔相等见证使原生不同的填充选择可见。延拓使用实际几何方形而非恒等附着，
    同时读取新增单形与旧区域取值。 *)

Program Definition WitnessS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv x y := bool
  |}.
Next Obligation.
  split; red; intros; exact true.
Defined.

Definition W
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) WitnessS.

Program Definition old_map (r : Ordinal 2) (s : Ordinal 8)
  : TriangleHornStage r (fin_rank s) ⇒ W
  :=
  {|nt n := {|func x := true|}
  |}.
Next Obligation. intros x y E. exact false. Defined.
Next Obligation. intros x. exact true. Defined.

Program Definition one_choice (n : nat) (i : Ordinal n) (v : bool)
  : HasHornFillers W n i
  :=
  {|horn_fill h := (v; _)
  |}.
Next Obligation. intros m h'. exact true. Defined.

Definition extension (r : Ordinal 2) (s : Ordinal 8) (v : bool)
  := TriangleHornStepExtension r s
      (one_choice (S (simplex_triangle_horn_face_dim s))
        (simplex_triangle_horn_missing r s) v) (old_map r s).

Definition new_value (r : Ordinal 2) (s : Ordinal 8) (v : bool)
  : bool
  := (extension r s v).1 (S (simplex_triangle_horn_face_dim s))
      (TriangleHornStageCellN r s _ (simplex_generic _)).

Definition steps
  : list (Ordinal 8)
  := [(fin_first : Ordinal 8); (fin_first⁺ : Ordinal 8);
      (fin_first⁺⁺ : Ordinal 8); (fin_first⁺⁺⁺ : Ordinal 8);
      (fin_first⁺⁺⁺⁺ : Ordinal 8); (fin_first⁺⁺⁺⁺⁺ : Ordinal 8);
      (fin_first⁺⁺⁺⁺⁺⁺ : Ordinal 8); (fin_first⁺⁺⁺⁺⁺⁺⁺ : Ordinal 8);
      (fin_first⁺⁺⁺⁺⁺⁺⁺⁺ : Ordinal 8)].

Definition parameters
  : list (Ordinal 2)
  := [(fin_first : Ordinal 2); (fin_first⁺ : Ordinal 2);
      (fin_first⁺⁺ : Ordinal 2)].

(** All twenty-seven actual attachment squares compute both independent
    selected new-cell values. *)

(** 全部二十七个实际附着方形计算两份独立的选定新增单形值。 *)

Example all_new_choices_compute
  : map (λ r, map (λ s, (new_value r s false, new_value r s true)) steps)
      parameters = repeat (repeat (false, true) 9) 3.
Proof. vm_compute. reflexivity. Defined.

Definition boundary_factor
  : (@Hom Δ) 2 1%nat
  := σ[1; fin_first].

Definition boundary_space
  : (@Hom Δ) 2 2
  := δ[1; fin_first⁺⁺] ∘ boundary_factor.

Definition old_point (r : Ordinal 2) (s : Ordinal 8)
  : TriangleHornStage r (fin_rank s) 2.
Proof.
  refine (({|lower := boundary_space|},
           {|lower := (id : (@Hom Δ) 2 2)|}); _).
  left. left. exists (fin_first⁺⁺). exists boundary_factor. reflexivity.
Defined.

(** The chosen new cell does not replace the actual old-domain value. *)

(** 所选新增单形不替换实际旧域取值。 *)

Example all_old_values_compute
  : map (λ r, map (λ s, (extension r s false).1 2
      (TriangleHornStageInclusionN r s 2 (old_point r s))) steps) parameters
      = repeat (repeat true 9) 3.
Proof. vm_compute. reflexivity. Defined.

(** Recovery of an actual degree-five factor traverses the new cell image. *)

(** 实际五维因子的恢复经过新增单形像。 *)

Definition repeated_factor (s : Ordinal 8)
  : (@Hom Δ) 5 (S (simplex_triangle_horn_face_dim s))
  := match Nat.ltb (fin_rank s) 3 as b
      return (@Hom Δ) 5 (S (if b then 2 else 3)) with
    | true => σ[3; fin_first] ∘ σ[4; fin_first]
    | false => σ[4; fin_first]
    end.

Example all_cell_factors_compute
  : map (λ r, map (λ s, fin_rank
      (lower (TriangleHornCellInverseN r s 5
        (TriangleHornCellImageN r s 5 {|lower := repeated_factor s|})) fin_first))
      steps) parameters = repeat (repeat 0 9) 3.
Proof. vm_compute. reflexivity. Defined.

Definition old_recovery (r : Ordinal 2) (s : Ordinal 8)
  := fst (extension r s false).2.

Definition new_recovery (r : Ordinal 2) (s : Ordinal 8)
  := snd (extension r s true).2.

Fail Definition choices_are_native_equal
  : new_value fin_first fin_first false = new_value fin_first fin_first true
  := eq_refl.

Fail Definition geometry_selects_kan
  : HasKanFillers (TriangleHornStage fin_first 0)
  := ltac:(typeclasses eauto).

Fail Definition geometry_selects_all_pushouts
  : HasPushout (FctCat (Δ^op) SetCat)
  := ltac:(typeclasses eauto).

(** ** A Genuine Boolean Cocycle Kan Client

    Restrict the nonzero triangle along the spatial projection to get
    an actual old-stage map. The integrated all-dimensional cocycle Kan
    choice supplies exactly the horn requested by each concrete step.
    Old recovery holds on the full stage, not only on vertices. *)

(** ** 真正的布尔 cocycle Kan 客户端

    沿空间投影限制非零三角形，得到实际旧阶段映射。已集成的全维 cocycle Kan
    选择只提供每个具体步骤请求的 horn；旧域恢复在整个阶段成立，而非仅在顶点。 *)

Program Definition spatial_projection
  : TriangleHornAmbient ⇒ (Δ[2] : Fct (Δ^op) SetCat)
  :=
  {|nt n := {|func x := fst x|}
  |}.
Next Obligation. intros [a b] [a' b'] [E F]. exact E. Defined.
Next Obligation. intros [a b]. reflexivity. Defined.

Definition nonzero_total
  : TriangleHornAmbient ⇒ BoolCocycleModel
  := (simplex_map_resp bool_cocycle_triangle) ∘Nv spatial_projection.

Definition actual_kan_extension (r : Ordinal 2) (s : Ordinal 8)
  := TriangleHornStepExtension r s
      (@hasHornFillers BoolCocycleModel BoolCocycleModel_HasKanFillers
        (simplex_triangle_horn_face_dim s) (simplex_triangle_horn_missing r s))
      (nonzero_total ∘Nv RegionInclusionN (TriangleHornRegion r (fin_rank s))).

Definition actual_kan_old_recovery (r : Ordinal 2) (s : Ordinal 8)
  := fst (actual_kan_extension r s).2.

Definition actual_kan_new_recovery (r : Ordinal 2) (s : Ordinal 8)
  := snd (actual_kan_extension r s).2.

Definition cocycle_old_point (s : Ordinal 8)
  : TriangleHornStage fin_first (fin_rank s) 2.
Proof.
  refine (({|lower := (id : (@Hom Δ) 2 2)|},
           {|lower := δ[1; fin_first⁺] ∘ boundary_factor|}); _).
  left. right.
  assert (J : ¬ (fin_first⁺ : Ordinal 2) = fin_first).
  { intros E. discriminate E. }
  exists (fin_first⁺; J), boundary_factor. reflexivity.
Defined.

(** The actual Kan extension preserves the true coefficient on an old
    two-simplex, using the full prescribed map rather than a unit value. *)

(** 实际 Kan 延拓保持旧二维单形上的真系数，使用完整给定映射而非单位值。 *)

Example actual_nonzero_old_value_computes
  : two_cocycle_triangle_value_resp
      ((actual_kan_extension fin_first fin_first).1 2
        (TriangleHornStageInclusionN fin_first fin_first 2
          (cocycle_old_point fin_first))) = true.
Proof. vm_compute. reflexivity. Defined.
