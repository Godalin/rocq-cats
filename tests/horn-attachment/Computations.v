From Cats Require Import
  Instance.Set.Simplicial.HornAttachment
  Instance.Set.Simplicial.Homotopy.Sphere
  Instance.Bool.CocycleSphere
  Instance.Set.Pushout
  Instance.Set.Product
  Cat.Diagram.Core
  Cat.Core.

Import Cats.Cat.Core.
Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Actual Pushouts and Independent New-Piece Choices

    Attach the Boolean square along its diagonal, with the other span
    map negating the Boolean. The two coordinate projections give
    distinct total maps that agree on the entire old region. *)

(** * 实际推出与独立新块选择

    沿对角附着布尔方块，跨度另一条映射为布尔否定。两个坐标投影给出不同的
    总映射，却在整个旧区域相等。 *)

Program Definition flip
  : BoolS →r BoolS
  :=
  {|func := negb
  |}.

Program Definition diagonal
  : BoolS →r ProdS BoolS BoolS
  :=
  {|func x := (x, x)
  |}.

Program Definition first
  : ProdS BoolS BoolS →r BoolS
  :=
  {|func := fst
  |}.
Next Obligation. intros [x y] [x' y'] [E F]. exact E. Defined.

Program Definition second
  : ProdS BoolS BoolS →r BoolS
  :=
  {|func := snd
  |}.
Next Obligation. intros [x y] [x' y'] [E F]. exact F. Defined.

Definition diagonal_target (p : ProdS BoolS BoolS →r BoolS)
    (E : (p ∘r diagonal) ≈f id_resp)
  : is_extension_target (C := SetCat) diagonal BoolS.
Proof.
  intros a. exists (a ∘r p). intros x.
  exact (@func_proper _ _ a _ _ (E x)).
Defined.

Definition first_target
  := diagonal_target first (λ x, eq_refl).

Definition second_target
  := diagonal_target second (λ x, eq_refl).

(** ** Using the Existing Chosen Pushout Locally

    The generated setoid pushout is selected only in this section. Its
    actual disjoint-sum representatives remain computational. *)

(** ** 局部使用既有选定推出

    只在本节选取生成广集推出，实际不交和代表仍保持可计算。 *)

Section ConcretePushout.
Local Existing Instance SetCat_HasPushout.

Definition total_first
  := PushoutMapExtension (pushout_universal (f := flip) (g := diagonal))
      (id_resp : BoolS →r BoolS) (first_target (id_resp ∘r flip)).

Definition total_second
  := PushoutMapExtension (pushout_universal (f := flip) (g := diagonal))
      (id_resp : BoolS →r BoolS) (second_target (id_resp ∘r flip)).

Example old_and_new_values_compute
  : (total_first.1 (ιpo1[flip,diagonal] true),
     total_first.1 (ιpo2[flip,diagonal] (false, true)),
     total_second.1 (ιpo2[flip,diagonal] (false, true))) = (true, true, false).
Proof. vm_compute. reflexivity. Defined.

Definition old_region_agrees
  : (total_first.1 ∘r ιpo1[flip,diagonal]) ≈f
      (total_second.1 ∘r ιpo1[flip,diagonal]).
Proof.
  transitivity (id_resp : BoolS →r BoolS);
    [exact (fst total_first.2) | symmetry; exact (fst total_second.2)].
Defined.

Example old_region_does_not_determine_total_map
  : ¬ (total_first.1 ≈f total_second.1).
Proof.
  intros E. specialize (E (ιpo2[flip,diagonal] (false, true))).
  vm_compute in E. discriminate E.
Defined.

Definition composite_extension_operation
  := map_extension_target_comp (C := SetCat)
      (id_resp : BoolS →r BoolS) ιpo1[flip,diagonal]
      (map_extension_target_id (C := SetCat) BoolS BoolS) (pushout_extension_target
        (pushout_universal (f := flip) (g := diagonal)) first_target).

End ConcretePushout.

(** ** Actual Horn Attachment with Native-Distinct Choices

    The identity pushout is a genuine attachment square. A constant
    simplicial setoid with Boolean equality witnesses exposes that
    filling choices and old-region values need not be natively equal. *)

(** ** 带原生不同选择的实际 horn 附着

    恒等推出是实际附着方形。相等见证为布尔值的常单纯广集使填充选择与旧区域值
    不必原生相等这一点可见。 *)

Program Definition WitnessS
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv x y := bool
  |}.
Next Obligation.
  split.
  - intros x. exact true.
  - intros x y E. exact E.
  - intros x y z E F. exact E.
Defined.

Definition W
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) WitnessS.

Program Definition old_horn
  : HornS W 3 fin_first⁺⁺
  :=
  {|nt n := {|func z := true|}
  |}.
Next Obligation. intros x y E. exact true. Defined.
Next Obligation. intros z. exact false. Defined.

Program Definition one_horn_choice (v : bool)
  : HasHornFillers W 3 fin_first⁺⁺
  :=
  {|horn_fill h := (v; _)
  |}.
Next Obligation. intros m z. exact true. Defined.

Definition witness_attachment (v : bool)
  := HornAttachmentExtension (IdN : Λ[3; fin_first⁺⁺] ⇒ _)
      ιΛ[3; fin_first⁺⁺] IdN
      (pushout_id (C := FctCat (Δ^op) SetCat) ιΛ[3; fin_first⁺⁺])
      (one_horn_choice v) old_horn.

Example selected_cells_compute_without_equating_witnesses
  : ((witness_attachment false).1 3 (simplex_generic 3),
     (witness_attachment true).1 3 (simplex_generic 3)) = (false, true).
Proof. vm_compute. reflexivity. Defined.

Definition specified_old_region_equation
  := fst (witness_attachment false).2.

Definition specified_new_cell_equation
  := snd (witness_attachment true).2.

Definition old_relative_values_preserved
  := horn_attachment_extension_relative
      (IdN : Λ[3; fin_first⁺⁺] ⇒ _) ιΛ[3; fin_first⁺⁺] IdN
      (pushout_id (C := FctCat (Δ^op) SetCat) ιΛ[3; fin_first⁺⁺])
      (one_horn_choice false) old_horn
      IdN old_horn (λ m z, true).

Definition chosen_cell_equality (m : nat) (z : (Δ[3]) m)
  : (horn_extension_target W 3 fin_first⁺⁺ (one_horn_choice false) old_horn).1 m z
      ≈S (horn_extension_target W 3 fin_first⁺⁺ (one_horn_choice true) old_horn).1 m z
  := false.

Definition comparison_requires_chosen_cell_equation
  := horn_attachment_extension_proper
      (IdN : Λ[3; fin_first⁺⁺] ⇒ _) ιΛ[3; fin_first⁺⁺] IdN
      (pushout_id (C := FctCat (Δ^op) SetCat) ιΛ[3; fin_first⁺⁺])
      (one_horn_choice false) (one_horn_choice true) old_horn old_horn
      (λ m z, false) chosen_cell_equality.

Fail Definition no_global_set_pushout
  : HasPushout SetCat
  := _.

Fail Definition no_automatic_Kan
  : HasKanFillers W
  := _.

Fail Definition no_other_horn_selected
  : HasHornFillers W 4 fin_first
  := _.

(** ** Consume One Choice from the Actual Cocycle Kan Model

    Only dimension three, missing face two is used. The chosen model is
    passed explicitly and does not become an instance by import. *)

(** ** 消费实际 Cocycle Kan 模型中的一份选择

    只使用三维缺第二面的填充；显式传入选定模型，不通过导入成为实例。 *)


Definition coefficient_tetrahedron
  := (CocycleTwoSphereHomotopy bool_cocycle_sphere bool_cocycle_sphere eq_refl).1.

Definition coefficient_horn
  : HornS BoolCocycleModel 3 fin_first⁺⁺
  := coefficient_tetrahedron↾Λ[BoolCocycleModel; 3; fin_first⁺⁺].

Definition coefficient_choice
  : HasHornFillers BoolCocycleModel 3 fin_first⁺⁺
  := @hasHornFillers BoolCocycleModel BoolCocycleModel_HasKanFillers 2 fin_first⁺⁺.

Definition coefficient_attachment
  := HornAttachmentExtension (IdN : Λ[3; fin_first⁺⁺] ⇒ _)
      ιΛ[3; fin_first⁺⁺] IdN
      (pushout_id (C := FctCat (Δ^op) SetCat) ιΛ[3; fin_first⁺⁺])
      coefficient_choice coefficient_horn.

Definition coefficient_cell
  := coefficient_attachment.1 3 (simplex_generic 3).

Example actual_cocycle_filler_faces_compute
  : (two_cocycle_triangle_value_resp (M := BoolS_Monoid)
       (d[BoolCocycleModel; 2; fin_first] coefficient_cell),
     (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
       (d[BoolCocycleModel; 2; fin_first⁺] coefficient_cell),
     (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
       (d[BoolCocycleModel; 2; fin_first⁺⁺] coefficient_cell),
     (two_cocycle_triangle_value_resp (M := BoolS_Monoid))
       (d[BoolCocycleModel; 2; fin_first⁺⁺⁺] coefficient_cell)) =
      (false, false, true, true).
Proof. vm_compute. reflexivity. Defined.

Definition all_degree_horn_preserved
  := fst coefficient_attachment.2.

Definition chosen_cell_determines_attachment
  := horn_attachment_extension_unique
      (IdN : Λ[3; fin_first⁺⁺] ⇒ _) ιΛ[3; fin_first⁺⁺] IdN
      (pushout_id (C := FctCat (Δ^op) SetCat) ιΛ[3; fin_first⁺⁺])
      coefficient_choice coefficient_horn
      coefficient_attachment.1 (fst coefficient_attachment.2)
      (snd coefficient_attachment.2).

Fail Definition no_global_cocycle_Kan
  : HasKanFillers BoolCocycleModel
  := _.
