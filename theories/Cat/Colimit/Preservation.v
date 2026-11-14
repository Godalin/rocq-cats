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

(** Apply the original right-adjoint preservation theorem to the stored
    opposite cone, then use the composition comparison already in [MapCocone]. *)

(** 将原右伴随保持定理用于存储的反锥，再使用 [MapCocone] 中已有的复合比较。 *)

Definition left_adjoint_preserves_colimit {C D J : Cat}
    {F : Fct C D} {G : Fct D C} (A : F ⊣ G)
    {K : Fct J C} {L : @Ob C} {κ : K ⇒∇ L}
    (Hκ : is_colimit κ)
  : is_colimit (MapCocone F κ)
  := limit_transport
      ((OpF_comp F K).1 ^-1N (OpF_comp F K).2)
      (NatIso_inv_NatIso (OpF_comp F K).1 (OpF_comp F K).2)
      (right_adjoint_preserves_limit (OpAdj A) Hκ).
