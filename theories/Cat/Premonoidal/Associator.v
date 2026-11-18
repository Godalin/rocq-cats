From Cats Require Export
  Cat.Binoidal.Center
  Cat.NaturalLaws.

Local Open Scope binoidal_scope.

(** * Associators on Fixed Tensor Actions

    An associator is chosen independently of any unit. One natural
    isomorphism family fixes its components and inverses in the last
    variable. The other directions, centrality and pentagon constrain
    those same maps. No interchange law is required. *)

(** * 固定张量作用上的结合子

    结合子的选择不依赖单位对象。一族在最后变量上的自然同构固定其分量及逆；
    其他方向、中心性和五边形约束同一映射，不要求交换律。 *)

Declare Scope premonoidal_scope.
Delimit Scope premonoidal_scope with premonoidal.
Reserved Notation "'αₚ[' X ';' Y ';' Z ']'"
  (at level 0).
Reserved Notation "'αₚ⁻¹[' X ';' Y ';' Z ']'"
  (at level 0).

(** ** Properties of a Specified Associator

    Fix the category and tensor actions. Only the supplied natural
    isomorphisms appear in the laws; no unit or second associator is chosen. *)

(** ** 给定结合子的性质

    固定范畴及张量作用。定律只使用给定自然同构，不选择单位或第二份结合子。 *)

Section Characterization.
Context {C : Cat} `{BC : !HasBinoidal C}
  (a : ∀ X Y : C,
    BinoidalLF (X ⊗ Y) ≅N (BinoidalLF X ∘F BinoidalLF Y)).

Class IsAssociator
  :=
  { assoc_natural_l (Y Z : C)
    :: IsNatIso (BinoidalRF Z ∘F BinoidalRF Y) (BinoidalRF (Y ⊗ Z))
        (λ X, ((a X Y).1 Z; (a X Y).2 Z))

  ; assoc_natural_m (X Z : C)
    :: IsNatIso (BinoidalRF Z ∘F BinoidalLF X)
        (BinoidalLF X ∘F BinoidalRF Z)
        (λ Y, ((a X Y).1 Z; (a X Y).2 Z))

  (** The forward components are central; inverse centrality is derived. *)

  (** 正向分量为中心态射，逆的中心性由此导出。 *)

  ; assoc_central (X Y Z : C) : is_central ((a X Y).1 Z)

  (** The pentagon compares four tensor positions without a unit. *)

  (** 五边形比较四个张量位置，不使用单位。 *)

  ; assoc_pentagon (W X Y Z : C)
    : (a W X).1 (Y ⊗ Z) ∘ (a (W ⊗ X) Y).1 Z ≈
        (W ⊲ (a X Y).1 Z) ∘
          ((a W (X ⊗ Y)).1 Z ∘ ((a W X).1 Y ⊳ Z))
  }.

End Characterization.

Arguments assoc_natural_l {C BC a IsAssociator} _ _.
Arguments assoc_natural_m {C BC a IsAssociator} _ _.
Arguments assoc_central {C BC a IsAssociator} _ _ _.
Arguments assoc_pentagon {C BC a IsAssociator} _ _ _ _.

(** Choose the associator and its characterization on these exact actions. *)

(** 在同一组作用上选择结合子及其刻画。 *)

Section Choice.
Context (C : Cat) `{BC : !HasBinoidal C}.

Class HasAssociator
  :=
  { PremonoidalAssocRIso (X Y : C)
    : BinoidalLF (X ⊗ Y) ≅N (BinoidalLF X ∘F BinoidalLF Y)
    where "'αₚ[' X ';' Y ';' Z ']'" := ((PremonoidalAssocRIso X Y).1 Z)
      : premonoidal_scope
    and "'αₚ⁻¹[' X ';' Y ';' Z ']'" := (((PremonoidalAssocRIso X Y).2 Z).1)
      : premonoidal_scope

  (** This component view stores no additional map or inverse. *)

  (** 此分量视图不另存映射或逆。 *)

  ; premonoidal_associator (X Y Z : C)
    : ((X ⊗ Y) ⊗ Z) ≅ (X ⊗ (Y ⊗ Z))
    := (αₚ[X; Y; Z]; (PremonoidalAssocRIso X Y).2 Z)

  ; isAssociator :: IsAssociator PremonoidalAssocRIso
  }.

End Choice.

Arguments HasAssociator C BC : clear implicits.
Arguments PremonoidalAssocRIso {_ _ _} _ _.
Arguments premonoidal_associator {_ _ _} _ _ _.
Arguments isAssociator {_ _ _}.

Notation "'αₚ[' X ';' Y ';' Z ']'" := (premonoidal_associator X Y Z).1
  : premonoidal_scope.
Notation "'αₚ⁻¹[' X ';' Y ';' Z ']'" := (premonoidal_associator X Y Z).2.1
  : premonoidal_scope.
Local Open Scope premonoidal_scope.

(** ** Natural Views and Selected Laws

    Fix an associator without assuming unitors. All views retain the
    stored forward and inverse components; the laws select its evidence. *)

(** ** 自然视图及选定定律

    固定结合子，不假设单位子。所有视图保留保存的正向及逆分量，定律读取其证据。 *)

Section Laws.
Context {C : Cat} `{BC : !HasBinoidal C} `{AC : !HasAssociator C BC}.

(** The first-variable natural isomorphism uses the shared components. *)

(** 第一变量的自然同构使用共享分量。 *)

Definition PremonoidalAssocLIso (Y Z : C)
  : (BinoidalRF Z ∘F BinoidalRF Y) ≅N BinoidalRF (Y ⊗ Z)
  := NatIsoOfComponents (assoc_natural_l (IsAssociator := isAssociator) Y Z).

(** The middle-variable view uses the same components and inverses. *)

(** 中间变量视图使用同一分量及逆。 *)

Definition PremonoidalAssocMIso (X Z : C)
  : (BinoidalRF Z ∘F BinoidalLF X) ≅N (BinoidalLF X ∘F BinoidalRF Z)
  := NatIsoOfComponents (assoc_natural_m (IsAssociator := isAssociator) X Z).

(** The selected associator is central. *)

(** 选定结合子为中心态射。 *)

Definition premonoidal_assoc_central (X Y Z : C)
  : is_central αₚ[X; Y; Z]
  := assoc_central (IsAssociator := isAssociator) X Y Z.

(** Naturality in the first tensor position. *)

(** 第一张量位置的自然性。 *)

Lemma premonoidal_assoc_natural_l {X X' : C} (Y Z : C) (f : Hom X X')
  : αₚ[X'; Y; Z] ∘ ((f ⊳ Y) ⊳ Z) ≈ (f ⊳ (Y ⊗ Z)) ∘ αₚ[X; Y; Z].
Proof. exact (nat_naturality (PremonoidalAssocLIso Y Z).1 f). Qed.

(** Naturality in the middle tensor position. *)

(** 中间张量位置的自然性。 *)

Lemma premonoidal_assoc_natural_m {Y Y' : C} (X Z : C) (g : Hom Y Y')
  : αₚ[X; Y'; Z] ∘ ((X ⊲ g) ⊳ Z) ≈ (X ⊲ (g ⊳ Z)) ∘ αₚ[X; Y; Z].
Proof. exact (nat_naturality (PremonoidalAssocMIso X Z).1 g). Qed.

(** Naturality in the last position is stored by the primary isomorphism. *)

(** 最后位置的自然性由主要自然同构保存。 *)

Lemma premonoidal_assoc_natural_r {Z Z' : C} (X Y : C) (h : Hom Z Z')
  : αₚ[X; Y; Z'] ∘ ((X ⊗ Y) ⊲ h) ≈ (X ⊲ (Y ⊲ h)) ∘ αₚ[X; Y; Z].
Proof. exact (nat_naturality (PremonoidalAssocRIso X Y).1 h). Qed.

(** The selected associator satisfies the unit-free pentagon. *)

(** 选定结合子满足不含单位的五边形。 *)

Lemma premonoidal_pentagon (W X Y Z : C)
  : αₚ[W; X; Y ⊗ Z] ∘ αₚ[W ⊗ X; Y; Z] ≈
      (W ⊲ αₚ[X; Y; Z]) ∘ (αₚ[W; X ⊗ Y; Z] ∘ (αₚ[W; X; Y] ⊳ Z)).
Proof. exact (assoc_pentagon (IsAssociator := isAssociator) W X Y Z). Qed.

End Laws.
