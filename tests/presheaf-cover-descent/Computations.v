From Cats Require Import
  Instance.Set.PresheafDescent
  Instance.Set.Sieve.Matching
  Instance.Set.Simplicial.Horn
  Instance.Bool.Group
  Cat.Diagram.Core
  Cat.Core.
From Cats.Set Require Import
  Pi
  Subset.

Import Cats.Cat.Core.
Local Open Scope nat_scope.
Local Open Scope ordinal_scope.

(** * Cover Selections Need Not Be Natural

    The constant presheaf below has two native-distinct representatives
    and Boolean equality witnesses. Every degree has the same two
    generators. Covers can change generator when the degree changes. *)

(** * 覆盖选择无需自然

    下方常预层有两个原生不同的代表和布尔相等见证。每维共用两个生成元，
    覆盖可随维数改变生成元。 *)

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

Definition generator (i : bool)
  : W 0
  := i.

Definition degree_cover
  : is_presheaf_cover generator.
Proof.
  intros n x. exists (Nat.even n), (ConstF [Ord n] (C := [Ord 0]) fin_first).
  exact false.
Defined.

Definition opposite_cover
  : is_presheaf_cover generator.
Proof.
  intros n x. exists (negb (Nat.even n)), (ConstF [Ord n] (C := [Ord 0]) fin_first).
  exact true.
Defined.

Definition values (i : bool)
  : W 0
  := i.

Definition compatibility
  : presheaf_values_compatible generator values.
Proof. intros n i j f h E. exact false. Defined.

Definition other_compatibility
  : presheaf_values_compatible generator values.
Proof. intros n i j f h E. exact true. Defined.

Definition descended
  : W ⇒ W
  := PresheafDescendN generator degree_cover values compatibility.

Definition other_descended
  : W ⇒ W
  := PresheafDescendN generator opposite_cover values other_compatibility.

(** The selected index changes after restriction, with unequal native data. *)

(** 限制后所选索引改变，且数据原生不同。 *)

Example different_choices_compute
  : ((degree_cover 0 true).1, (degree_cover 1 true).1,
     (opposite_cover 0 true).1) = (true, false, false).
Proof. vm_compute. reflexivity. Defined.

(** Descent does not force the selected raw values to be native equal. *)

(** 下降不强制所选原始值原生相等。 *)

Example different_outputs_compute
  : (descended 0 false, descended 1 true,
     other_descended 0 false) = (true, false, false).
Proof. vm_compute. reflexivity. Defined.

(** The two actual maps are nevertheless equal in the specified setoid. *)

(** 两个实际映射仍按指定广集相等。 *)

Definition independent_maps
  : descended ≈N other_descended
  := presheaf_descend_proper generator degree_cover opposite_cover
      values values compatibility other_compatibility (λ i, true).

(** This consumes actual naturality at a restriction changing the choice. *)

(** 此处实际消费改变选择的限制处的自然性。 *)

Definition changing_restriction_natural
  : descended 1 (fmap W (ConstF [Ord 1] (C := [Ord 0]) fin_first) true) ≈S
      fmap W (ConstF [Ord 1] (C := [Ord 0]) fin_first) (descended 0 true)
  := nat_naturality descended (ConstF [Ord 1] (C := [Ord 0]) fin_first) true.

(** A cover may also choose native-distinct indices for source elements
    which are equal only in their specified relation. *)

(** 覆盖也可为仅按指定关系相等的来源元素选择原生不同的索引。 *)

Definition input_cover
  : is_presheaf_cover generator.
Proof.
  intros n x. exists x, (ConstF [Ord n] (C := [Ord 0]) fin_first).
  exact false.
Defined.

Definition input_descended
  : W ⇒ W
  := PresheafDescendN generator input_cover values compatibility.

Example input_choices_compute
  : ((input_cover 0 false).1, (input_cover 0 true).1,
     input_descended 0 false, input_descended 0 true) =
      (false, true, false, true).
Proof. vm_compute. reflexivity. Defined.

(** The actual component is respectful despite native-distinct selections. *)

(** 即使选择原生不同，实际分量仍保指定相等。 *)

Definition input_component_proper
  : input_descended 0 false ≈S input_descended 0 true
  := @func_proper _ _ (input_descended 0) false true false.

(** The bundled respectful map ignores compatibility proof differences. *)

(** 打包的保相等映射忽略相容证明的差别。 *)

Definition bundled_descend_proper
  : presheaf_descend_resp generator degree_cover (values; compatibility)
      ≈N presheaf_descend_resp generator degree_cover
        (values; other_compatibility).
Proof.
  apply (@func_proper _ _ (presheaf_descend_resp generator degree_cover)).
  intros i. exact true.
Defined.

(** Equality and compatibility proof fields are excluded from raw equality. *)

(** 原始相等不包含相等与相容证明字段。 *)

Fail Definition choices_are_native_equal
  : descended 0 false = other_descended 0 false
  := eq_refl.

Fail Definition selected_values_are_natural_by_conversion
  : descended 1 true = descended 0 true
  := eq_refl.

(** ** A Strict Boolean Value Client

    Here equality is native equality and coverage must retain the correct
    generator. Descent computes a genuine nonconstant map, negation. *)

(** ** 严格布尔值客户端

    此处指定相等是原生相等，覆盖必须保留正确生成元；下降计算真正的非常值
    映射，即布尔否定。 *)

Definition B
  : Fct (Δ^op) SetCat
  := ConstF (Δ^op) BoolS.

Definition strict_generator (i : bool)
  : B 0
  := i.

Definition strict_cover
  : is_presheaf_cover strict_generator.
Proof.
  intros n x. exists x, (ConstF [Ord n] (C := [Ord 0]) fin_first). reflexivity.
Defined.

Definition negated (i : bool)
  : B 0
  := negb i.

Definition negation_compatible
  : presheaf_values_compatible strict_generator negated.
Proof. intros n i j f h E. exact (f_equal negb E). Defined.

Definition negation_descended
  : B ⇒ B
  := PresheafDescendN strict_generator strict_cover negated
      negation_compatible.

Example negation_computes
  : (negation_descended 0 true, negation_descended 5 false) = (false, true).
Proof. vm_compute. reflexivity. Defined.

(** Incompatible values cannot be made compatible by simply supplying
    reflexivity; all equal source images must be compared. *)

(** 不能仅填入自反见证使不相容的值相容；必须比较全部相等来源像。 *)

Fail Definition compatibility_is_automatic
  : presheaf_values_compatible generator negated
  := λ n i j f h E, eq_refl.

(** ** Existing Sieve Computation and Universal Property

    A generated sieve retains two representations of the same generator.
    Reusing general descent preserves the old evaluation and inverse laws. *)

(** ** 既有筛计算与泛性质

    生成筛保留同一生成元的两个表示；复用一般下降保持旧求值及互逆律。 *)

Definition sieve_generator (i : bool)
  : (@Hom Δ) 0%nat 0%nat
  := id.

Program Definition sieve_value
  : SieveMatching sieve_generator B
  :=
  {|matching_value (i : bool) := (true : B 0)
  |}.
Next Obligation. reflexivity. Defined.

Definition sieve_descended
  : SievePsh (@GeneratedSieve Δ 0%nat bool (λ _ : bool, 0%nat) sieve_generator) ⇒ B
  := SieveMatchingN sieve_generator B sieve_value.

Example sieve_values_compute
  : (sieve_descended 0 {|lower :=
      (sieve_generator false; generated_sieve_member sieve_generator false)|},
     sieve_descended 0 {|lower :=
      (sieve_generator true; generated_sieve_member sieve_generator true)|})
      = (true, true).
Proof. vm_compute. reflexivity. Defined.

Definition sieve_β
  := matching_descend_β sieve_generator B sieve_value.

Definition sieve_η
  := matching_descend_η sieve_generator B sieve_descended.

Definition sieve_universal
  := matching_descend_universal sieve_generator B sieve_value.

(** Importing descent does not choose Kan structures. *)

(** 导入下降不选择 Kan 结构。 *)

Fail Definition no_kan (X : Fct (Δ^op) SetCat)
  : HasKanFillers X
  := _.

Fail Definition no_horn (X : Fct (Δ^op) SetCat)
  : HasHornFillers X 4 fin_first
  := _.
