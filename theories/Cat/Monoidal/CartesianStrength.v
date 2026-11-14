From Cats Require Export
  Cat.Terminal
  Cat.Product.Core
  Cat.Monoidal.Strength
  Cat.Monoidal.Cartesian.

Local Open Scope monoidal_scope.

(** * Cartesian Strength and Context Projection *)

(** * 笛卡尔强度与上下文投影 *)

Section Projection.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    {F : Fct C C} (S : HasStrength (@CartesianMonoidal C HT HP) F).

(** Discarding the ordinary context after strength preserves the effectful
    input. This follows from naturality into the terminal context and the
    strength unit law, without assuming the functor preserves products. *)

(** 强度之后丢弃通常上下文，保留带效应输入。这来自到终上下文的自然性及强度
    单位律，不假定函子保持积。 *)

Lemma cartesian_strength_projection (X Y : @Ob C)
  : fmap F (π2 : Hom (X × Y) Y) ∘ st[S; X; Y] ≈ π2.
Proof.
  pose proof (strength_natural S (! : Hom X 1) (@id Y)) as H.
  rewrite !cartesian_tensor_map in H.
  change (st[S; 1; Y] ∘ (! × fmap F (@id Y)) ≈
    fmap F (! × @id Y) ∘ st[S; X; Y]) in H.
  rewrite functor_id in H.
  transitivity ((fmap F (π2 : Hom (1 × Y) Y) ∘ st[S; 1; Y]) ∘
    ((! : Hom X 1) × @id (F Y))).
  - rewrite comp_assoc, H, <- comp_assoc, <- functor_comp,
      cross_η, product_β2, comp_id_l. reflexivity.
  - rewrite (strength_unit S Y). cbn.
    rewrite cross_η, product_β2, comp_id_l.
    reflexivity.
Qed.

End Projection.
