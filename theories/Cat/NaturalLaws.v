From Cats Require Export
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Natural Isomorphisms on Shared Components

    Several naturality directions may refer to one family of isomorphisms.
    Keep that family fixed and supply only its naturality. The ordinary
    natural-isomorphism view reuses the same forward and inverse maps. *)

(** * 共享分量上的自然同构

    多个自然性方向可以引用同一同构族。固定该族，只补充自然性；普通自然同构
    视图复用同一份正向及逆向映射。 *)

Class IsNatIso {C D : Cat} (F G : Fct C D)
    (components : ∀ X : C, F X ≅ G X)
  :=
  { nat_iso_naturality {X Y : C} (f : Hom X Y)
    : (components Y).1 ∘ fmap F f ≈ fmap G f ∘ (components X).1
  }.

(** Package the fixed components, without selecting new inverses. *)

(** 打包固定分量，不另选逆映射。 *)

Definition NatIsoOfComponents {C D : Cat} {F G : Fct C D}
    {components : ∀ X : C, F X ≅ G X}
    (H : IsNatIso F G components)
  : F ≅N G.
Proof.
  exists (NatOfComponents (λ X, (components X).1)
    (λ X Y f, @nat_iso_naturality C D F G components H X Y f)).
  exact (λ X, (components X).2).
Defined.
