From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Product.Core
  Cat.Limit.Core.
From Cats Require Import
  Cat.Adjunction
  Cat.Limit.Preservation.
From Cats Require Export Cat.Diagram.Shape.

(** * Binary Products as Limits of Discrete Diagrams *)

(** * 二元积作为离散图式的极限 *)

Section ProductLimits.
Context {C : Cat} {D : Fct PairShape C} {P : @Ob C} (κ : P ⇒Δ D).

(** The candidate binary product property gives a limit of the two-object
    discrete diagram. *)

(** 候选二元积性质给出两对象离散图式的极限。 *)

Definition product_limit
    (HP : is_product (D false) (D true) P (κ false) (κ true))
  : is_limit κ.
Proof.
  intros Z μ. destruct (HP Z (μ false) (μ true)) as [h Hh].
  exists h. refine {|this := _
                   ; that := _
                   |}.
  - intros []; [exact (snd (@this _ _ _ _ _ Hh)) | exact (fst (@this _ _ _ _ _ Hh))].
  - intros g Hg. apply (@that _ _ _ _ _ Hh). split; [exact (Hg false) | exact (Hg true)].
Defined.

(** A limit of the two-object discrete diagram satisfies the binary product
    property. *)

(** 两对象离散图式的极限满足二元积性质。 *)

Definition limit_product (Hκ : is_limit κ)
  : is_product (D false) (D true) P (κ false) (κ true).
Proof.
  intros Z f g.
  pose (μ := @DiscreteCone C bool D Z
    (λ b, if b as v return Hom Z (D v) then g else f)).
  destruct (Hκ Z μ) as [h Hh].
  exists h. refine {|this := _
                   ; that := _
                   |}.
  - split; [exact (@this _ _ _ _ _ Hh false) | exact (@this _ _ _ _ _ Hh true)].
  - intros k [Hf Hg]. apply (@that _ _ _ _ _ Hh).
    intros []; [exact Hg | exact Hf].
Defined.

(** The binary product property and the corresponding limiting-cone property
    are equivalent. *)

(** 二元积性质与相应极限锥性质等价。 *)

Theorem product_iff_limit
  : is_product (D false) (D true) P (κ false) (κ true) ↔ is_limit κ.
Proof. split; [apply product_limit | apply limit_product]. Defined.

End ProductLimits.

(** Chosen products give all diagrams of this shape a chosen limit. These
    structures must be explicitly enabled. *)

(** 选定积为该形状的任意图式给出选定极限；这些结构须显式启用。 *)

Program Definition ProductDiagramLimit {C : Cat} `{HP : !HasProduct C}
    (D : Fct PairShape C)
  : HasLimit C D
  :=
  {|Lim := D false × D true
  ; limit_cone := @DiscreteCone C bool D (D false × D true)
      (λ b, if b as v return Hom (D false × D true) (D v) then π2 else π1)
  |}.
Next Obligation. apply product_limit. apply product_universal. Defined.

(** Choose limits of all two-object discrete diagrams from the selected binary
    product structure. *)

(** 由选定二元积结构选择全部两对象离散图式的极限。 *)

Program Definition ProductLimits {C : Cat} `{HP : !HasProduct C}
  : HasLimitsOfShape C PairShape
  :=
  {|hasLimit := ProductDiagramLimit
  |}.

(** Recover selected binary products from limits of the two-object discrete
    shape. *)

(** 由两对象离散形状的极限恢复选定二元积。 *)

Program Definition PairLimitsProduct {C : Cat}
    `{HL : !HasLimitsOfShape C PairShape}
  : HasProduct C
  :=
  {|Prod X Y := lim ⟨X, Y⟩D
  ; π1 X Y := πlim[⟨X, Y⟩D] false
  ; π2 X Y := πlim[⟨X, Y⟩D] true
  |}.
Next Obligation.
  exact (limit_product (πlim[⟨X, Y⟩D]) (limit_universal ⟨X, Y⟩D)).
Defined.

(** Preservation follows from the general limit theorem. *)

(** 保持性质来自一般极限定理。 *)

Definition right_adjoint_preserves_product {C D : Cat}
    {F : Fct C D} {G : Fct D C} (A : F ⊣ G)
    {X Y P : @Ob D} {p : Hom P X} {q : Hom P Y}
    (HP : is_product X Y P p q)
  : is_product (G X) (G Y) (G P) (fmap G p) (fmap G q)
  := limit_product (MapCone G (PairCone p q))
    (right_adjoint_preserves_limit A (product_limit (PairCone p q) HP)).
