From Cats Require Import
  Cat.Core
  Cat.Preorder
  Cat.Functor.Core
  Cat.Natural.

(** * Comparisons into a Codiscrete Category

    Any two diagrams into a codiscrete category have the unique component
    arrows as an invertible comparison. No equality of object maps is needed. *)

(** * 到余离散范畴的比较

    到余离散范畴的任意两个图式均以唯一分量态射组成可逆比较，
    不要求对象映射相等。 *)

Program Definition CodiscreteNatIso {J : Cat} {X : Type}
    (F G : Fct J (CodiscreteCat X))
  : F ≅N G
  := ({|nt x := tt
       |}; λ x, (tt; (tt, tt))).
Next Obligation. exact tt. Defined.
