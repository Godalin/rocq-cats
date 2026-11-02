From Cats Require Import
  Cat.Core
  Cat.Functor
  Cat.Natural
  Cat.Pullback
  Cat.Limit.
From Cats Require Import
  Cat.Adjunction
  Cat.Limit.Preservation.
From Cats Require Export Cat.Diagram.Shape.

(** * Pullbacks as Limits of Cospans *)

(** * 拉回作为余跨度图式的极限 *)

Section PullbackLimits.
Context {C : Cat} {D : Functor CospanShape C} {P : @Ob C} (κ : P ⇒Δ D).

(** The candidate pullback property gives a limit of the cospan diagram. *)

(** 候选拉回性质给出余跨度图式的极限。 *)

Definition pullback_limit
    (HP : is_pullback
      (fmap D (path_edge cospan_l)) (fmap D (path_edge cospan_r))
      P (κ cospan_left) (κ cospan_right))
  : is_limit κ.
Proof.
  intros Q μ.
  destruct (snd HP Q (μ cospan_left) (μ cospan_right) (cospan_cone_comm μ)) as [h Hh].
  exists h. refine {|this := _
                   ; that := _
                   |}.
  - intros v. destruct v; cbn.
    + exact (fst (@this _ _ _ _ _ Hh)).
    + exact (snd (@this _ _ _ _ _ Hh)).
    + transitivity ((fmap D (path_edge cospan_l) ∘ κ cospan_left) ∘ h).
      * apply comp_r. symmetry. exact (free_cone_edge κ cospan_l).
      * rewrite comp_assoc, (fst (@this _ _ _ _ _ Hh)).
        exact (free_cone_edge μ cospan_l).
  - intros k Hk. apply (@that _ _ _ _ _ Hh).
    split; [exact (Hk cospan_left) | exact (Hk cospan_right)].
Defined.

(** A limit of the cospan diagram satisfies the pullback property. *)

(** 余跨度图式的极限满足拉回性质。 *)

Definition limit_pullback (Hκ : is_limit κ)
  : is_pullback (fmap D (path_edge cospan_l)) (fmap D (path_edge cospan_r))
      P (κ cospan_left) (κ cospan_right).
Proof.
  split; [apply cospan_cone_comm |].
  intros Q p q Hpq.
  destruct (Hκ Q (@CospanConeOver C D Q p q Hpq)) as [h Hh].
  exists h. refine {|this := _
                   ; that := _
                   |}.
  - split; [exact (@this _ _ _ _ _ Hh cospan_left) | exact (@this _ _ _ _ _ Hh cospan_right)].
  - intros k [Hk1 Hk2]. apply (@that _ _ _ _ _ Hh).
    intros v. destruct v; cbn; [exact Hk1 | exact Hk2 |].
    transitivity (fmap D (path_edge cospan_l) ∘ κ cospan_left ∘ k).
    + apply comp_r. symmetry. exact (free_cone_edge κ cospan_l).
    + rewrite comp_assoc, Hk1. reflexivity.
Defined.

(** The pullback property and the corresponding limiting-cone property are
    equivalent. *)

(** 拉回性质与相应极限锥性质等价。 *)

Theorem pullback_iff_limit
  : is_pullback (fmap D (path_edge cospan_l)) (fmap D (path_edge cospan_r))
      P (κ cospan_left) (κ cospan_right) ↔ is_limit κ.
Proof. split; [apply pullback_limit | apply limit_pullback]. Defined.

End PullbackLimits.

(** Select the limit of a cospan diagram using the chosen pullback structure. *)

(** 用选定拉回结构选择余跨度图式的极限。 *)

Program Definition PullbackDiagramLimit {C : Cat} `{HP : !HasPullback C}
    {X Y Z : @Ob C} (f : Hom X Z) (g : Hom Y Z)
  : HasLimit C ⟨f →← g⟩D
  :=
  {|Lim := Pb f g
  ; limit_cone := CospanCone (pb1 f g) (pb2 f g) pullback_comm
  |}.
Next Obligation.
  apply pullback_limit. exact pullback_universal.
Defined.

(** Choose limits of all cospan diagrams from the selected pullback structure. *)

(** 由选定拉回结构选择全部余跨度图式的极限。 *)

Program Definition PullbackLimits {C : Cat} `{HP : !HasPullback C}
  : HasLimitsOfShape C CospanShape
  :=
  {|hasLimit D :=
      {|Lim := Pb (fmap D (path_edge cospan_l)) (fmap D (path_edge cospan_r))
      ; limit_cone := @CospanConeOver C D _
          (pb1 _ _) (pb2 _ _) pullback_comm
      |}
  |}.
Next Obligation. apply pullback_limit. exact pullback_universal. Defined.

(** Recover selected pullbacks from limits of the cospan shape. *)

(** 由余跨度形状的极限恢复选定拉回。 *)

Program Definition CospanLimitsPullback {C : Cat}
    `{HL : !HasLimitsOfShape C CospanShape}
  : HasPullback C
  :=
  {|Pb X Y Z f g := lim ⟨f →← g⟩D
  ; pb1 X Y Z f g := πlim[⟨f →← g⟩D] cospan_left
  ; pb2 X Y Z f g := πlim[⟨f →← g⟩D] cospan_right
  |}.
Next Obligation.
  exact (limit_pullback (πlim[⟨f →← g⟩D]) (limit_universal ⟨f →← g⟩D)).
Defined.

(** The image cone is a pullback by the general right-adjoint theorem. *)

(** 由一般右伴随保持定理，像锥仍为拉回。 *)

Definition right_adjoint_preserves_pullback {C D : Cat}
    {F : Functor C D} {G : Functor D C} (A : F ⊣ G)
    {X Y Z P : @Ob D} {f : Hom X Z} {g : Hom Y Z}
    {p : Hom P X} {q : Hom P Y} (HP : is_pullback f g P p q)
  : is_pullback (fmap G f) (fmap G g) (G P) (fmap G p) (fmap G q)
  := limit_pullback (MapCone G (CospanCone p q (fst HP)))
    (right_adjoint_preserves_limit A
      (pullback_limit (CospanCone p q (fst HP)) HP)).
