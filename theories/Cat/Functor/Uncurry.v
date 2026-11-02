From Cats Require Import
  Cat.Core
  Cat.Functor
  Cat.Natural.

(** * Uncurrying a Functor-Valued Functor

    The outer functor's naturality is precisely what allows the two
    independent variables to commute. *)

(** * 函子值函子的去柯里化

    外层函子的自然性恰好保证两个独立变量的作用交换。 *)

Program Definition UncurryF {A B C : Cat} (F : Functor A (Fct B C))
  : Functor (A ×C B) C
  :=
  {|F0 p := F (fst p) (snd p)
  ; F1 X Y f := fmap (F (fst Y)) (snd f) ∘ (fmap F (fst f)) (snd X)
  |}.
Next Obligation.
  intros [u v] [u' v'] [Hu Hv]. cbn in *.
  apply comp_proper.
  - apply functor_fmap_proper. exact Hv.
  - exact (@functor_fmap_proper A (Fct B C) F _ _ u u' Hu (snd X)).
Defined.

Next Obligation.
  destruct X as [a b]. cbn.
  rewrite (@functor_id A (Fct B C) F a b). cbn.
  rewrite functor_id, comp_id_r. reflexivity.
Defined.
Next Obligation.
  destruct X as [a b], Y as [a' b'], Z as [a'' b''], f as [u' v'], g as [u v].
  cbn.
  rewrite (@functor_comp A (Fct B C) F a a' a'' u' u b). cbn.
  rewrite (@functor_comp B C (F a'') b b' b'' v' v).
  repeat rewrite comp_assoc.
  rewrite <- (comp_assoc (fmap (F a'') v) (fmap F u' b) (fmap F u b)).
  rewrite <- (nt_naturality (fmap F u') v).
  repeat rewrite comp_assoc. reflexivity.
Defined.

Notation "F '^uncF'" := (UncurryF F) (at level 35) : cat_scope.

(** Uncurry a natural transformation between functor-valued functors. *)

(** 对函子值函子之间的自然变换去柯里化。 *)

Program Definition UncurryN {A B C : Cat} {F G : Functor A (Fct B C)}
    (α : F ⇒ G)
  : F^uncF ⇒ G^uncF
  :=
  {|nt p := α (fst p) (snd p)
  |}.
Next Obligation.
  destruct X as [a b], Y as [a' b'], f as [u v]. cbn.
  pose proof (nt_naturality α u b) as Hu. cbn in Hu.
  change (α a' b' ∘ (fmap (F a') v ∘ fmap F u b) ≈
    (fmap (G a') v ∘ fmap G u b) ∘ α a b).
  transitivity (fmap (G a') v ∘ (α a' b ∘ fmap F u b)).
  - rewrite <- (comp_assoc (fmap (G a') v) (α a' b) (fmap F u b)),
      <- (comp_assoc (α a' b') (fmap (F a') v) (fmap F u b)).
    apply comp_r. exact (nt_naturality (α a') v).
  - transitivity (fmap (G a') v ∘ (fmap G u b ∘ α a b)).
    + apply comp_l. exact Hu.
    + symmetry. apply comp_assoc.
Defined.

Notation "α '^uncN'" := (UncurryN α) (at level 35) : cat_scope.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance UncurryN_proper {A B C : Cat} {F G : Functor A (Fct B C)}
  : Proper (NatEq ==> NatEq) (@UncurryN A B C F G).
Proof. intros α β H [a b]. exact (H a b). Defined.

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance UncurryF_proper {A B C : Cat}
  : Proper (NatIso ==> NatIso) (@UncurryF A B C).
Proof.
  intros F G [α Hα]. exists (α^uncN). intros [a b].
  exact (is_iso_NatIso (α a) (Hα a) b).
Defined.
