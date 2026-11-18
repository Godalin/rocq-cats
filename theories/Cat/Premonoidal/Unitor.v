From Cats Require Export
  Cat.Binoidal.Center
  Cat.NaturalLaws.

Local Open Scope binoidal_scope.

(** * Unit Objects and Unitors

    A common object and two central natural isomorphisms form the unitor
    package. This choice uses no associator. Their triangle compatibility
    is specified only when the two packages are combined. *)

(** * 单位对象及单位子

    共同对象及两个中心自然同构构成单位子包，不使用结合子。两份选择组合时，
    才规定它们的三角形相容性。 *)

Declare Scope premonoidal_scope.
Delimit Scope premonoidal_scope with premonoidal.
Reserved Notation "'Iₚ'" (at level 0).
Reserved Notation "'Iₚ[' P ']'" (at level 0).
Reserved Notation "'λₚ[' X ']'" (at level 0).
Reserved Notation "'ρₚ[' X ']'" (at level 0).
Reserved Notation "'λₚ⁻¹[' X ']'" (at level 0).
Reserved Notation "'ρₚ⁻¹[' X ']'" (at level 0).

(** ** Characterization at a Fixed Unit

    The supplied natural isomorphisms already contain their inverses and
    naturality. Only forward centrality remains; inverse centrality follows. *)

(** ** 固定单位上的刻画

    给定自然同构已包含其逆及自然性；这里只需正向中心性，逆的中心性由此推出。 *)

Section Characterization.
Context {C : Cat} `{BC : !HasBinoidal C} (I : C)
  (L : BinoidalLF I ≅N IdF) (R : BinoidalRF I ≅N IdF).

Class IsUnitors
  :=
  { unitor_l_central (X : C) : is_central (L.1 X)
  ; unitor_r_central (X : C) : is_central (R.1 X)
  }.

End Characterization.

Arguments unitor_l_central {C BC I L R IsUnitors} _.
Arguments unitor_r_central {C BC I L R IsUnitors} _.

(** Choose one shared unit and the two natural isomorphisms. *)

(** 选择唯一共享单位及两份自然同构。 *)

Section Choice.
Context (C : Cat) `{BC : !HasBinoidal C}.

Class HasUnitors
  :=
  { PremonoidalUnit : C
    where "'Iₚ'" := PremonoidalUnit
      : premonoidal_scope

  ; PremonoidalUnitorLIso : BinoidalLF Iₚ ≅N IdF
    where "'λₚ[' X ']'" := (PremonoidalUnitorLIso.1 X)
      : premonoidal_scope
    and "'λₚ⁻¹[' X ']'" := ((PremonoidalUnitorLIso.2 X).1)
      : premonoidal_scope

  (** Component views retain the selected inverse witnesses. *)

  (** 分量视图保留选定逆的见证。 *)

  ; premonoidal_unitor_l (X : C)
    : (Iₚ ⊗ X) ≅ X
    := (λₚ[X]; PremonoidalUnitorLIso.2 X)
  ; PremonoidalUnitorRIso : BinoidalRF Iₚ ≅N IdF
    where "'ρₚ[' X ']'" := (PremonoidalUnitorRIso.1 X)
      : premonoidal_scope
    and "'ρₚ⁻¹[' X ']'" := ((PremonoidalUnitorRIso.2 X).1)
      : premonoidal_scope
  ; premonoidal_unitor_r (X : C)
    : (X ⊗ Iₚ) ≅ X
    := (ρₚ[X]; PremonoidalUnitorRIso.2 X)
  ; isUnitors :: IsUnitors Iₚ PremonoidalUnitorLIso
      PremonoidalUnitorRIso
  }.

End Choice.

Arguments HasUnitors C BC : clear implicits.
Arguments PremonoidalUnit {_ _} _.
Arguments PremonoidalUnitorLIso {_ _} _.
Arguments PremonoidalUnitorRIso {_ _} _.
Arguments premonoidal_unitor_l {_ _ _} _.
Arguments premonoidal_unitor_r {_ _ _} _.
Arguments isUnitors {_ _ _}.

Notation "'Iₚ'" := (PremonoidalUnit _) : premonoidal_scope.
Notation "'Iₚ[' P ']'" := (PremonoidalUnit P) : premonoidal_scope.
Notation "'λₚ[' X ']'" := (premonoidal_unitor_l X).1 : premonoidal_scope.
Notation "'ρₚ[' X ']'" := (premonoidal_unitor_r X).1 : premonoidal_scope.
Notation "'λₚ⁻¹[' X ']'" := (premonoidal_unitor_l X).2.1 : premonoidal_scope.
Notation "'ρₚ⁻¹[' X ']'" := (premonoidal_unitor_r X).2.1 : premonoidal_scope.
Local Open Scope premonoidal_scope.

(** ** Selected Unitor Laws

    Fix the unitors independently of associativity. Component centrality
    and naturality read their stored evidence directly. *)

(** ** 选定单位子的定律

    固定单位子，不假设结合性；分量中心性及自然性直接读取保存的证据。 *)

Section Laws.
Context {C : Cat} `{BC : !HasBinoidal C} `{UC : !HasUnitors C BC}.

(** The left unitor is central. *)

(** 左单位子为中心态射。 *)

Definition premonoidal_unit_l_central (X : C)
  : is_central λₚ[X]
  := unitor_l_central (IsUnitors := isUnitors) X.

(** The right unitor is central. *)

(** 右单位子为中心态射。 *)

Definition premonoidal_unit_r_central (X : C)
  : is_central ρₚ[X]
  := unitor_r_central (IsUnitors := isUnitors) X.

(** Naturality of the selected left unitor. *)

(** 选定左单位子的自然性。 *)

Lemma premonoidal_unit_l_natural {X Y : C} (f : Hom X Y)
  : λₚ[Y] ∘ (Iₚ[UC] ⊲ f) ≈ f ∘ λₚ[X].
Proof. exact (nat_naturality (PremonoidalUnitorLIso UC).1 f). Qed.

(** Naturality of the selected right unitor. *)

(** 选定右单位子的自然性。 *)

Lemma premonoidal_unit_r_natural {X Y : C} (f : Hom X Y)
  : ρₚ[Y] ∘ (f ⊳ Iₚ[UC]) ≈ f ∘ ρₚ[X].
Proof. exact (nat_naturality (PremonoidalUnitorRIso UC).1 f). Qed.

End Laws.
