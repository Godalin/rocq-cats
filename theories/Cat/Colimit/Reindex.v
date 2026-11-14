From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Limit.Core
  Cat.Limit.Reindex
  Cat.Limit.Transport.
From Cats Require Export
  Cat.Colimit.Core
  Cat.Diagram.Reindex.

(** * Colimits along Full, Essentially Surjective Functors *)

(** * 沿满且本质满函子传递余极限 *)

(** Full, essentially surjective restriction preserves colimiting cocones
    through the original opposite restriction and diagram transport. *)

(** 满且本质满的限制通过原反限制与图式运输保持余极限余锥。 *)

Definition restrict_colimit {I J C : Cat} {Q : Fct I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q)
    {D : Fct J C} {L : @Ob C} {κ : D ⇒∇ L}
    (Hκ : is_colimit κ)
  : is_colimit (κ ∘∇F Q)
  := limit_transport ((OpF_comp D Q).1 ^-1N (OpF_comp D Q).2)
      (NatIso_inv_NatIso (OpF_comp D Q).1 (OpF_comp D Q).2)
      (restrict_limit (functor_op_full HF)
        (functor_op_essentially_surjective HQ) Hκ).

(** Essential surjectivity alone detects colimiting cocones. *)

(** 仅本质满就能检测余极限余锥。 *)

Definition colimit_of_restrict {I J C : Cat} {Q : Fct I J}
    (HQ : is_essentially_surjective Q)
    {D : Fct J C} {L : @Ob C} {κ : D ⇒∇ L}
    (Hκ : is_colimit (κ ∘∇F Q))
  : is_colimit κ.
Proof.
  apply (limit_of_restrict (functor_op_essentially_surjective HQ)).
  refine (limit_cone_equiv
    (limit_transport (OpF_comp D Q).1 (OpF_comp D Q).2 Hκ) _).
  intros i. cbn. rewrite !comp_id_r. reflexivity.
Defined.

(** Restriction preserves and reflects colimits under the original hypotheses. *)

(** 限制在原假设下保持并反映余极限。 *)

Theorem colimit_iff_restrict {I J C : Cat} {Q : Fct I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q)
    {D : Fct J C} {L : @Ob C} (κ : D ⇒∇ L)
  : is_colimit κ ↔ is_colimit (κ ∘∇F Q).
Proof.
  split; [apply (restrict_colimit HF HQ) | apply (colimit_of_restrict HQ)].
Defined.

(** Original opposite extension gives the extended cocone's colimit property. *)

(** 原反延拓给出延拓余锥的余极限性质。 *)

Definition extend_colimit {I J C : Cat} {Q : Fct I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q)
    {D : Fct J C} {L : @Ob C} {κ : (D ∘F Q) ⇒∇ L}
    (Hκ : is_colimit κ)
  : is_colimit (ExtendCocone HF HQ κ)
  := extend_limit (functor_op_full HF)
      (functor_op_essentially_surjective HQ)
      (limit_transport (OpF_comp D Q).1 (OpF_comp D Q).2 Hκ).

(** Select a colimit by extending its original opposite limit. *)

(** 通过延拓原反极限选择余极限。 *)

Program Definition ReindexedColimit {I J C : Cat} {Q : Fct I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q)
    (D : Fct J C) `{HC : !HasColimit C (D ∘F Q)}
  : HasColimit C D
  :=
  {|hasOpLimit := @ReindexedLimit (I^op) (J^op) (C^op) (Q^opF)
      (functor_op_full HF) (functor_op_essentially_surjective HQ) (D^opF)
      (TransportedLimit (OpF_comp D Q).1 (OpF_comp D Q).2)
  |}.

(** Restrict a selected colimit through opposite restriction and transport. *)

(** 通过反限制及运输限制选定余极限。 *)

Program Definition RestrictedColimit {I J C : Cat} {Q : Fct I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q)
    (D : Fct J C) `{HC : !HasColimit C D}
  : HasColimit C (D ∘F Q)
  :=
  {|hasOpLimit := @TransportedLimit (I^op) (C^op) _ _
      ((OpF_comp D Q).1 ^-1N (OpF_comp D Q).2)
      (NatIso_inv_NatIso (OpF_comp D Q).1 (OpF_comp D Q).2)
      (RestrictedLimit (functor_op_full HF)
        (functor_op_essentially_surjective HQ) (D^opF))
  |}.

(** Transfer all selected colimits of a shape by the original opposite
    shape-transfer theorem. No choices are enabled by import. *)

(** 用原反形状传递定理传递整个形状的选定余极限；导入不启用任何选择。 *)

Program Definition ReindexedColimits {I J C : Cat} {Q : Fct I J}
    (HF : is_full Q) (HQ : is_essentially_surjective Q)
    `{HC : !HasColimitsOfShape C I}
  : HasColimitsOfShape C J
  :=
  {|hasOpLimits := ReindexedLimits (functor_op_full HF)
      (functor_op_essentially_surjective HQ)
  |}.
