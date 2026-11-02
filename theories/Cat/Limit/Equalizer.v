From Cats Require Import
  Cat.Core
  Cat.Functor
  Cat.Natural
  Cat.Equalizer
  Cat.Limit.
From Cats Require Import
  Cat.Adjunction
  Cat.Limit.Preservation.
From Cats Require Export Cat.Diagram.Arrow.

(** * Equalizers as Limits of Parallel Pairs *)
Section EqualizerLimits.
Context {C : Cat} {D : Functor ParallelShape C} {E : @Ob C} (κ : E ⇒Δ D).

Definition equalizer_limit
    (HE : is_equalizer
      (fmap D (path_edge parallel_l)) (fmap D (path_edge parallel_r))
      E (κ false))
  : is_limit κ.
Proof.
  intros Q μ.
  destruct (snd HE Q (μ false) (parallel_cone_comm μ)) as [h Hh].
  exists h. refine {| this := _; that := _ |}.
  - intros b. destruct b.
    + transitivity ((fmap D (path_edge parallel_l) ∘ κ false) ∘ h).
      * apply comp_r. symmetry. exact (free_cone_edge κ parallel_l).
      * rewrite comp_assoc, (@this _ _ _ _ _ Hh). exact (free_cone_edge μ parallel_l).
    + exact (@this _ _ _ _ _ Hh).
  - intros k Hk. apply (@that _ _ _ _ _ Hh). exact (Hk false).
Defined.

Definition limit_equalizer (Hκ : is_limit κ)
  : is_equalizer (fmap D (path_edge parallel_l)) (fmap D (path_edge parallel_r))
      E (κ false).
Proof.
  split; [apply parallel_cone_comm |].
  intros Q q Hq. destruct (Hκ Q (ParallelConeOver q Hq)) as [h Hh].
  exists h. refine {| this := _; that := _ |}.
  - exact (@this _ _ _ _ _ Hh false).
  - intros k Hk. apply (@that _ _ _ _ _ Hh).
    intros b. destruct b; cbn; [| exact Hk].
    transitivity ((fmap D (path_edge parallel_l) ∘ κ false) ∘ k).
    + apply comp_r. symmetry. exact (free_cone_edge κ parallel_l).
    + rewrite comp_assoc, Hk. reflexivity.
Defined.

Theorem equalizer_iff_limit
  : is_equalizer (fmap D (path_edge parallel_l)) (fmap D (path_edge parallel_r))
      E (κ false) ↔ is_limit κ.
Proof. split; [apply equalizer_limit | apply limit_equalizer]. Defined.

End EqualizerLimits.

Program Definition EqualizerDiagramLimit {C : Cat} `{HE : !HasEqualizer C}
    (D : Functor ParallelShape C)
  : HasLimit C D
  := {| Lim := Eq[fmap D (path_edge parallel_l), fmap D (path_edge parallel_r)]
      ; limit_cone := ParallelConeOver (eqι _ _) equalizer_comm |}.
Next Obligation. apply equalizer_limit. exact equalizer_universal. Defined.

Program Definition EqualizerLimits {C : Cat} `{HE : !HasEqualizer C}
  : HasLimitsOfShape C ParallelShape
  := {| hasLimit := EqualizerDiagramLimit |}.

Program Definition ParallelLimitsEqualizer {C : Cat}
    `{HL : !HasLimitsOfShape C ParallelShape}
  : HasEqualizer C
  := {| EqObj X Y f g := lim ⟨f ⇉ g⟩D
      ; eqι X Y f g := πlim[⟨f ⇉ g⟩D] false |}.
Next Obligation.
  exact (limit_equalizer (πlim[⟨f ⇉ g⟩D]) (limit_universal ⟨f ⇉ g⟩D)).
Defined.

(** Object uniqueness reuses general uniqueness of limits. *)
Definition equalizer_unique {C : Cat} {X Y E E' : @Ob C} {f g : Hom X Y}
    {e : Hom E X} {e' : Hom E' X}
    (HE : is_equalizer f g E e) (HE' : is_equalizer f g E' e')
  : E ≅[C] E'
  := limit_unique (equalizer_limit (ParallelCone e (fst HE)) HE)
    (equalizer_limit (ParallelCone e' (fst HE')) HE').

Definition right_adjoint_preserves_equalizer {C D : Cat}
    {F : Functor C D} {G : Functor D C} (A : F ⊣ G)
    {X Y E : @Ob D} {f g : Hom X Y} {e : Hom E X}
    (HE : is_equalizer f g E e)
  : is_equalizer (fmap G f) (fmap G g) (G E) (fmap G e)
  := limit_equalizer (MapCone G (ParallelCone e (fst HE)))
    (right_adjoint_preserves_limit A (equalizer_limit (ParallelCone e (fst HE)) HE)).
