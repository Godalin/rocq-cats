From Cats Require Export
  Cat.Monoidal.Center
  Cat.NaturalLaws.
From Cats Require Import
  Cat.Isomorphism.

Local Open Scope monoidal_scope.
Local Open Scope ob_scope.

(** * Unit Objects and Unitors

    A common object and two central natural isomorphisms form the unitor
    package. This choice uses no associator. Their triangle compatibility
    is specified only when the two packages are combined. *)

(** * 单位对象及单位子

    共同对象及两个中心自然同构构成单位子包，不使用结合子。两份选择组合时，
    才规定它们的三角形相容性。 *)

Reserved Notation "'𝐈'"
  (at level 0).
Reserved Notation "'λ[' X ']'"
  (at level 0).
Reserved Notation "'ρ[' X ']'"
  (at level 0).
Reserved Notation "'λ⁻¹[' X ']'"
  (at level 0).
Reserved Notation "'ρ⁻¹[' X ']'"
  (at level 0).

(** ** Characterization at a Fixed Unit

    The supplied natural isomorphisms already contain their inverses and
    naturality. Only forward centrality remains; inverse centrality follows. *)

(** ** 固定单位上的刻画

    给定自然同构已包含其逆及自然性；这里只需正向中心性，逆的中心性由此推出。 *)

Minks.Mixin IsTensorUnitors {C : Cat}
    `{hasBinoidal : HasBinoidal C}
    (I : C) (L : (I ⊗-) ≅N IdF) (R : (-⊗ I) ≅N IdF)
  :=
  { unitor_l_central (X : C)
    : is_central (L.1 X)
  ; unitor_r_central (X : C)
    : is_central (R.1 X)
  }.

Arguments unitor_l_central {_ _ _ _ _ _} _.
Arguments unitor_r_central {_ _ _ _ _ _} _.

(** Choose one shared unit and the two natural isomorphisms. *)

(** 选择唯一共享单位及两份自然同构。 *)

Minks.Mixin HasTensorUnitors (C : Cat)
  extends HasBinoidal C
  :=
  { tensor_unit : C
    where "'𝐈'" := tensor_unit
      : monoidal_scope

  ; TensorUnitorLIso
    : (𝐈 ⊗-) ≅N IdF
    where "'λ[' X ']'" := (TensorUnitorLIso.1 X)
      : monoidal_scope
    and "'λ⁻¹[' X ']'" := ((TensorUnitorLIso.2 X).1)
      : monoidal_scope

  (** Component views retain the selected inverse witnesses. *)

  (** 分量视图保留选定逆的见证。 *)

  ; tensor_unitor_l (X : C)
    : (𝐈 ⊗ X) ≅ X
    := (λ[X]; TensorUnitorLIso.2 X)
  ; TensorUnitorRIso
    : (-⊗ 𝐈) ≅N IdF
    where "'ρ[' X ']'" := (TensorUnitorRIso.1 X)
      : monoidal_scope
    and "'ρ⁻¹[' X ']'" := ((TensorUnitorRIso.2 X).1)
      : monoidal_scope
  ; tensor_unitor_r (X : C)
    : (X ⊗ 𝐈) ≅ X
    := (ρ[X]; TensorUnitorRIso.2 X)
  ; isTensorUnitors
    :: IsTensorUnitors 𝐈 TensorUnitorLIso TensorUnitorRIso
  }.

Arguments tensor_unit {_ _} _.
Arguments TensorUnitorLIso {_ _} _.
Arguments TensorUnitorRIso {_ _} _.
Arguments tensor_unitor_l {_ _ _} _.
Arguments tensor_unitor_r {_ _ _} _.
Arguments isTensorUnitors {_ _ _}.

Notation "'𝐈'" := (tensor_unit _)
  (at level 0)
  : monoidal_scope.
Notation "'𝐈[' P ']'" := (tensor_unit P)
  (at level 0, format "'𝐈[' P ]")
  : monoidal_scope.
Notation "'λ[' X ']'" := (tensor_unitor_l X).1
  (at level 0)
  : monoidal_scope.
Notation "'ρ[' X ']'" := (tensor_unitor_r X).1
  (at level 0)
  : monoidal_scope.
Notation "'λ⁻¹[' X ']'" := (tensor_unitor_l X).2.1
  (at level 0)
  : monoidal_scope.
Notation "'ρ⁻¹[' X ']'" := (tensor_unitor_r X).2.1
  (at level 0)
  : monoidal_scope.

(** ** Selected Unitor Laws

    Fix the unitors independently of associativity. Component centrality
    and naturality read their stored evidence directly. *)

(** ** 选定单位子的定律

    固定单位子，不假设结合性；分量中心性及自然性直接读取保存的证据。 *)

Section Laws.
Context {C : Cat} `{BC : !HasBinoidal C}
  `{UC : !@HasTensorUnitors C BC}.

(** The left unitor is central. *)

(** 左单位子为中心态射。 *)

Definition tensor_unitor_l_central (X : C)
  : is_central λ[X]
  := unitor_l_central X.

(** The right unitor is central. *)

(** 右单位子为中心态射。 *)

Definition tensor_unitor_r_central (X : C)
  : is_central ρ[X]
  := unitor_r_central X.

(** Naturality of the selected left unitor. *)

(** 选定左单位子的自然性。 *)

Lemma tensor_unitor_l_natural {X Y : C} (f : Hom X Y)
  : λ[Y] ∘ (𝐈 ⊲ f) ≈ f ∘ λ[X].
Proof.
  exact (nat_naturality (TensorUnitorLIso UC).1 f).
Qed.

(** Naturality of the selected right unitor. *)

(** 选定右单位子的自然性。 *)

Lemma tensor_unitor_r_natural {X Y : C} (f : Hom X Y)
  : ρ[Y] ∘ (f ⊳ 𝐈) ≈ f ∘ ρ[X].
Proof.
  exact (nat_naturality (TensorUnitorRIso UC).1 f).
Qed.

(** The inverse left unitor is central. *)

(** 逆左单位子是中心态射。 *)

Definition tensor_unitor_l_inv_central (X : C)
  : is_central λ⁻¹[X]
  := central_inv (tensor_unitor_l X)
      (tensor_unitor_l_central X).

(** The inverse right unitor is central. *)

(** 逆右单位子是中心态射。 *)

Definition tensor_unitor_r_inv_central (X : C)
  : is_central ρ⁻¹[X]
  := central_inv (tensor_unitor_r X)
      (tensor_unitor_r_central X).

(** The inverse left unitor is natural in its variable. *)

(** 逆左单位子在其变量上自然。 *)

Lemma tensor_unitor_l_inv_natural {X Y : C} (f : Hom X Y)
  : λ⁻¹[Y] ∘ f ≈ (𝐈 ⊲ f) ∘ λ⁻¹[X].
Proof.
  exact (iso_square_inv
    (tensor_unitor_l X) (tensor_unitor_l Y)
    (𝐈 ⊲ f) f (tensor_unitor_l_natural f)).
Qed.

(** The inverse right unitor is natural in its variable. *)

(** 逆右单位子在其变量上自然。 *)

Lemma tensor_unitor_r_inv_natural {X Y : C} (f : Hom X Y)
  : ρ⁻¹[Y] ∘ f ≈ (f ⊳ 𝐈) ∘ ρ⁻¹[X].
Proof.
  exact (iso_square_inv
    (tensor_unitor_r X) (tensor_unitor_r Y)
    (f ⊳ 𝐈) f (tensor_unitor_r_natural f)).
Qed.

End Laws.
