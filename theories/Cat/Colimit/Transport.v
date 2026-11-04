From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Limit.Transport.
From Cats Require Export
  Cat.Colimit.Core.

(** * Transporting Colimiting Cocones *)

(** * 运输余极限余锥 *)

(** Equal cocone legs retain the original opposite limit property, without
    comparing naturality witnesses. *)

(** 相等余锥腿保留原反极限性质，不比较自然性见证。 *)

Definition colimit_cocone_equiv {J C : Cat} {D : Functor J C} {L : @Ob C}
    {κ μ : D ⇒∇ L} (Hκ : is_colimit κ) (H : κ ≈N μ)
  : is_colimit μ
  := limit_cone_equiv Hκ H.

(** Restrict along an invertible diagram transformation by original opposite
    limit transport. This keeps the original mediator arrows. *)

(** 沿可逆图式变换预合成，通过原反极限运输保留原中介箭头。 *)

Definition colimit_transport {J C : Cat} {D E : Functor J C}
    (α : D ⇒ E) (Hα : α ⦂ D ≅N E) {L : @Ob C}
    {κ : E ⇒∇ L} (Hκ : is_colimit κ)
  : is_colimit (κ ∘∇ α)
  := limit_transport (α^opN) (nt_op_NatIso α Hα) Hκ.

(** Selected colimits transport contravariantly in an invertible diagram
    transformation, retaining the selected apex and mediator data. *)

(** 选定余极限沿可逆图式变换逆向运输，保留选定顶点及中介数据。 *)

Program Definition TransportedColimit {J C : Cat} {D E : Functor J C}
    (α : D ⇒ E) (Hα : α ⦂ D ≅N E) `{HC : !HasColimit C E}
  : HasColimit C D
  :=
  {|hasOpLimit := TransportedLimit (α^opN) (nt_op_NatIso α Hα)
  |}.
