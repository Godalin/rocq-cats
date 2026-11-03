From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Adjunction
  Cat.Diagram.Dual
  Cat.Colimit.Core
  Cat.Limit.Transport
  Cat.Limit.Preservation.

(** * Left Adjoints Preserve Colimits *)

(** * 左伴随保持余极限 *)

(** Apply right-adjoint limit preservation in the opposite categories.
    Only this particular cocone must already be colimiting. *)

(** 在反范畴中应用右伴随保极限定理；只要求给定余锥已经为余极限。 *)

Definition left_adjoint_preserves_colimit {C D J : Cat}
    {F : Functor C D} {G : Functor D C} (A : F ⊣ G)
    {K : Functor J C} {L : @Ob C} {κ : K ⇒∇ L}
    (Hκ : is_colimit κ)
  : is_colimit (MapCocone F κ).
Proof.
  refine (limit_cone_equiv
    (μ := CoconeOp (MapCocone F κ))
    (limit_transport
      ((OpF_comp F K).1 ^-1N (OpF_comp F K).2)
      (NatIso_inv_NatIso (OpF_comp F K).1 (OpF_comp F K).2)
      (right_adjoint_preserves_limit (OpAdjunction A) Hκ)) _).
  intros j. exact (@comp_id_l (D^op) _ _ (fmap F (κ j))).
Defined.
