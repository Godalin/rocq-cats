From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Adjunction.
From Cats Require Import
  Cat.Diagram.Core
  Cat.Limit.Core.

(** * Limits as Right Adjoints to the Diagonal

    Functoriality of the selected limits is derived from their universal
    properties. No separate coherence choices for limit maps are stored. *)

(** * 极限作为对角函子的右伴随

    选定极限的函子性由泛性质导出，不额外存储极限映射的相干选择。 *)

Section ChosenLimits.
Context {J C : Cat} `{HL : !HasLimitsOfShape C J}.

(** The universal-mediator operation as a respectful hom-setoid map. *)

(** 泛中介运算作为 Hom 广集间的保相等映射。 *)

Program Definition limit_lift_resp {X : @Ob C} {D : Functor J C}
  : @HomSet (Fct J C) (ConstF J X) D →r HomSet X (lim D)
  :=
  {|func := limit_lift
  |}.

(** The inverse hom correspondence sends an arrow to the precomposed limiting
    cone. *)

(** Hom 对应的逆将箭头送到预合成后的极限锥。 *)

Program Definition limit_cone_resp {X : @Ob C} {D : Functor J C}
  : HomSet X (lim D) →r @HomSet (Fct J C) (ConstF J X) D
  :=
  {|func f := πlim[D] ∘Cone f
  |}.
Next Obligation. intros f g H j. cbn. rewrite H. reflexivity. Defined.

(** The diagonal functor is left adjoint to the selected-limit functor. *)

(** 对角函子左伴随于选定极限函子。 *)

Definition LimitAdjunction
  : Δ[J,C] ⊣ LimitF.
Proof.
  refine (AdjunctionFromHom Δ[J,C] LimitF
    (λ X D, limit_lift_resp) (λ X D, limit_cone_resp) _ _ _ _).
  - intros X D κ. apply limit_β.
  - intros X D f. apply limit_η.
  - intros X Y D κ f.
    change (lim⟨ κ ∘Cone f ⟩ ≈ lim⟨ κ ⟩ ∘ f). apply limit_lift_comp.
  - intros X D E α κ.
    change (lim⟨ α ∘Nv κ ⟩ ≈ limit_map α ∘ lim⟨ κ ⟩). apply limit_lift_map.
Defined.

End ChosenLimits.

(** Conversely, the counit of a diagonal adjunction supplies limiting cones.
    This constructs chosen limits explicitly; it is not a global instance. *)

(** 反过来，对角伴随的余单位给出极限锥；选定极限通过显式构造获得，不注册为全局
    实例。 *)

Section DiagonalAdjunction.
Context {J C : Cat} {R : Functor (Fct J C) C} (A : Δ[J,C] ⊣ R).

(** The counit of a diagonal adjunction selects a limit of one diagram. *)

(** 对角伴随的余单位为单个图式选择极限。 *)

Program Definition DiagonalAdjunctionLimit (D : Functor J C)
  : HasLimit C D
  :=
  {|Lim := R D
  ; limit_cone := adjunction_counit A D
  |}.
Next Obligation.
  intros X κ. exists (κ^♯[A]). refine {|this := _
                                      ; that := _
                                      |}.
  - intros j.
    exact (transitivity (symmetry (unadjunct_counit A (κ^♯[A]) j))
      (adjunction_β A κ j)).
  - intros f H. symmetry. apply (snd (adjunct_iff A κ f)).
    transitivity (adjunction_counit A D ∘Nv fmap Δ[J,C] f).
    + symmetry. exact H.
    + exact (symmetry (unadjunct_counit A f)).
Defined.

(** A right adjoint to the diagonal supplies limits of its entire shape. *)

(** 对角函子的右伴随给出该形状的全部选定极限。 *)

Program Definition DiagonalAdjunctionLimits
  : HasLimitsOfShape C J
  :=
  {|hasLimit := DiagonalAdjunctionLimit
  |}.

End DiagonalAdjunction.

(** Chosen limits of a shape correspond to a chosen right adjoint of its
    diagonal. *)

(** 某形状的选定极限与其对角函子的选定右伴随对应。 *)

Theorem limits_iff_diagonal_right_adjoint (J C : Cat)
  : HasLimitsOfShape C J ↔ ∃ R : Functor (Fct J C) C, Δ[J,C] ⊣ R.
Proof.
  split.
  - intros HL. exists (@LimitF J C HL). exact (@LimitAdjunction J C HL).
  - intros [R A]. exact (DiagonalAdjunctionLimits A).
Defined.
