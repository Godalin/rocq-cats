From Cats Require Export
  Cat.Monoidal.Center
  Cat.NaturalLaws.

Local Open Scope monoidal_scope.
Local Open Scope ob_scope.

(** * Associators on Fixed Tensor Actions

    An associator is chosen independently of any unit. One natural
    isomorphism family fixes its components and inverses in the last
    variable. The other directions, centrality and pentagon constrain
    those same maps. No interchange law is required. *)

(** * 固定张量作用上的结合子

    结合子的选择不依赖单位对象。一族在最后变量上的自然同构固定其分量及逆；
    其他方向、中心性和五边形约束同一映射，不要求交换律。 *)

Reserved Notation "'α[' X ';' Y ';' Z ']'"
  (at level 0).
Reserved Notation "'α⁻¹[' X ';' Y ';' Z ']'"
  (at level 0).

(** ** Properties of a Specified Associator

    Fix the category and tensor actions. Only the supplied natural
    isomorphisms appear in the laws; no unit or second associator is chosen. *)

(** ** 给定结合子的性质

    固定范畴及张量作用。定律只使用给定自然同构，不选择单位或第二份结合子。 *)

Minks.Mixin IsTensorAssoc (C : Cat)
    (a : ∀ X Y : C, ((X ⊗ Y) ⊗-) ≅N ((X ⊗-) ∘F (Y ⊗-)))
  extends HasBinoidal C
  :=
  { assoc_natural_l (Y Z : C)
    :: IsNatIso ((-⊗ Z) ∘F (-⊗ Y)) (-⊗ (Y ⊗ Z))
        (λ X, ((a X Y).1 Z; (a X Y).2 Z))

  ; assoc_natural_m (X Z : C)
    :: IsNatIso ((-⊗ Z) ∘F (X ⊗-))
        ((X ⊗-) ∘F (-⊗ Z))
        (λ Y, ((a X Y).1 Z; (a X Y).2 Z))

  (** The forward components are central; inverse centrality is derived. *)

  (** 正向分量为中心态射，逆的中心性由此导出。 *)

  ; assoc_central (X Y Z : C) : is_central ((a X Y).1 Z)

  (** The pentagon compares four tensor positions without a unit. *)

  (** 五边形比较四个张量位置，不使用单位。 *)

  ; assoc_pentagon (W X Y Z : C)
    : (a W X).1 (Y ⊗ Z) ∘ (a (W ⊗ X) Y).1 Z
      ≈ (W ⊲ (a X Y).1 Z) ∘
          ((a W (X ⊗ Y)).1 Z ∘ ((a W X).1 Y ⊳ Z))
  }.

Arguments assoc_natural_l {C hasBinoidal a IsTensorAssoc} _ _.
Arguments assoc_natural_m {C hasBinoidal a IsTensorAssoc} _ _.
Arguments assoc_central {C hasBinoidal a IsTensorAssoc} _ _ _.
Arguments assoc_pentagon {C hasBinoidal a IsTensorAssoc} _ _ _ _.

(** Choose the associator and its characterization on these exact actions. *)

(** 在同一组作用上选择结合子及其刻画。 *)

Minks.Mixin HasTensorAssoc (C : Cat)
  extends HasBinoidal C
  :=
  { TensorAssocRIso (X Y : C)
    : ((X ⊗ Y) ⊗-) ≅N ((X ⊗-) ∘F (Y ⊗-))
    where "'α[' X ';' Y ';' Z ']'" := ((TensorAssocRIso X Y).1 Z)
      : monoidal_scope
    and "'α⁻¹[' X ';' Y ';' Z ']'" := (((TensorAssocRIso X Y).2 Z).1)
      : monoidal_scope

  (** This component view stores no additional map or inverse. *)

  (** 此分量视图不另存映射或逆。 *)

  ; tensor_assoc (X Y Z : C)
    : ((X ⊗ Y) ⊗ Z) ≅ (X ⊗ (Y ⊗ Z))
    := (α[X; Y; Z]; (TensorAssocRIso X Y).2 Z)

  ; isTensorAssoc :: @IsTensorAssoc C hasBinoidal TensorAssocRIso
  }.

Arguments TensorAssocRIso {_ _ _} _ _.
Arguments tensor_assoc {_ _ _} _ _ _.
Arguments isTensorAssoc {_ _ _}.

Notation "'α[' X ';' Y ';' Z ']'"
  := (tensor_assoc X Y Z).1
  (at level 0)
  : monoidal_scope.
Notation "'α⁻¹[' X ';' Y ';' Z ']'"
  := (tensor_assoc X Y Z).2.1
  (at level 0)
  : monoidal_scope.

(** ** Natural Views and Selected Laws

    Fix an associator without assuming unitors. All views retain the
    stored forward and inverse components; the laws select its evidence. *)

(** ** 自然视图及选定定律

    固定结合子，不假设单位子。所有视图保留保存的正向及逆分量，定律读取其证据。 *)

Section Laws.
Context {C : Cat}
  `{BC : !HasBinoidal C} `{AC : !@HasTensorAssoc C BC}.

(** The first-variable natural isomorphism uses the shared components. *)

(** 第一变量的自然同构使用共享分量。 *)

Definition TensorAssocLIso (Y Z : C)
  : ((-⊗ Z) ∘F (-⊗ Y)) ≅N (-⊗ (Y ⊗ Z))
  := NatIsoOfComponents (assoc_natural_l Y Z).

(** The middle-variable view uses the same components and inverses. *)

(** 中间变量视图使用同一分量及逆。 *)

Definition TensorAssocMIso (X Z : C)
  : ((-⊗ Z) ∘F (X ⊗-))
    ≅N ((X ⊗-) ∘F (-⊗ Z))
  := NatIsoOfComponents (assoc_natural_m X Z).

(** The selected associator is central. *)

(** 选定结合子为中心态射。 *)

Definition tensor_assoc_central (X Y Z : C)
  : is_central α[X; Y; Z]
  := assoc_central X Y Z.

(** Naturality in the first tensor position. *)

(** 第一张量位置的自然性。 *)

Lemma tensor_assoc_natural_l {X X' : C} (Y Z : C)
    (f : Hom X X')
  : α[X'; Y; Z] ∘ ((f ⊳ Y) ⊳ Z)
    ≈ (f ⊳ (Y ⊗ Z)) ∘ α[X; Y; Z].
Proof.
  exact (nat_naturality (TensorAssocLIso Y Z).1 f).
Qed.

(** Naturality in the middle tensor position. *)

(** 中间张量位置的自然性。 *)

Lemma tensor_assoc_natural_m {Y Y' : C} (X Z : C)
    (g : Hom Y Y')
  : α[X; Y'; Z] ∘ ((X ⊲ g) ⊳ Z)
    ≈ (X ⊲ (g ⊳ Z)) ∘ α[X; Y; Z].
Proof.
  exact (nat_naturality (TensorAssocMIso X Z).1 g).
Qed.

(** Naturality in the last position is stored by the primary isomorphism. *)

(** 最后位置的自然性由主要自然同构保存。 *)

Lemma tensor_assoc_natural_r {Z Z' : C} (X Y : C)
    (h : Hom Z Z')
  : α[X; Y; Z'] ∘ ((X ⊗ Y) ⊲ h)
    ≈ (X ⊲ (Y ⊲ h)) ∘ α[X; Y; Z].
Proof.
  exact (nat_naturality (TensorAssocRIso X Y).1 h).
Qed.

(** The selected associator satisfies the unit-free pentagon. *)

(** 选定结合子满足不含单位的五边形。 *)

Lemma tensor_assoc_pentagon (W X Y Z : C)
  : α[W; X; Y ⊗ Z] ∘ α[W ⊗ X; Y; Z]
    ≈ (W ⊲ α[X; Y; Z])
      ∘ (α[W; X ⊗ Y; Z] ∘ (α[W; X; Y] ⊳ Z)).
Proof. exact (assoc_pentagon W X Y Z). Qed.

End Laws.

(** Separate associator naturality also respects ordered sequences of
    three arrows. This does not require joint functoriality of the tensor. *)

(** 结合子的分别自然性也保持三条态射的有序组合，不要求张量的联合函子性。 *)

Lemma tensor_assoc_sequence_natural {C : Cat}
    `{BC : !HasBinoidal C} `{AC : !@HasTensorAssoc C BC}
    {X X' Y Y' Z Z' : @Ob C}
    (f : Hom X X') (g : Hom Y Y') (h : Hom Z Z')
  : α[X'; Y'; Z']
        ∘ tensor_sequence (tensor_sequence f g) h
      ≈ tensor_sequence f (tensor_sequence g h)
          ∘ α[X; Y; Z].
Proof.
  unfold tensor_sequence.
  rewrite tensor_r_comp, tensor_l_comp, <- !comp_assoc.
  rewrite (@tensor_assoc_natural_r C BC AC Z Z' X' Y' h).
  rewrite !comp_assoc. apply comp_proper; [reflexivity |].
  rewrite <- comp_assoc,
    (@tensor_assoc_natural_m C BC AC Y Y' X' Z g), comp_assoc.
  apply comp_proper; [reflexivity |].
  exact (@tensor_assoc_natural_l C BC AC X X' Y Z f).
Qed.
