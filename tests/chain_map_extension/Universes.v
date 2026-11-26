From Cats Require Import
  Cat.Extension.Chain
  Cat.Functor.Core.

(** * Independent Object, Arrow and Equality Sizes *)

(** ** Chains with larger equality witnesses

    Keep all four sizes strictly distinct. The only selections are the
    explicit edge extensions; their functions have no Proper hypothesis. *)

Section largeEquality.
Universes o h p l.
Constraint o < h, h < p, p < l.
Context {C : Cat@{o h p l l}} {n : nat} (c : Chain C n) (Q : @Ob C).
Context (E : ∀ k, is_extension_target (chain_edge c k) Q).
Context (i j : Ordinal n) (f : (@Hom [Ord n]) i j).

Definition largeEquality_segments
  : is_extension_target (chain_segment c i j f) Q
  := chain_extension_target c Q E i j f.

Definition largeEquality_diagram
  : is_extension_target (fmap ⟦c⟧Ch f) Q
  := chain_extension_target c Q E i j f.

Context (a : (@Hom C) (c i) Q).
Let e
  := chain_extension_target c Q E i j f a.

Definition largeEquality_recovery
  : e.1 ∘ chain_segment c i j f ≈ a
  := e.2.

Definition largeEquality_fixed (D : @Ob C) (r : (@Hom C) D (c i))
    (d : (@Hom C) D Q) (H : a ∘ r ≈ d)
  : e.1 ∘ (chain_segment c i j f ∘ r) ≈ d
  := map_extension_preserves e.2 r d H.

End largeEquality.

(** ** Chains with smaller equality witnesses

    Keep all four sizes strictly distinct. The only selections are the
    explicit edge extensions; their functions have no Proper hypothesis. *)

Section smallEquality.
Universes o h p l.
Constraint p < h, h < o, o < l.
Context {C : Cat@{o h p l l}} {n : nat} (c : Chain C n) (Q : @Ob C).
Context (E : ∀ k, is_extension_target (chain_edge c k) Q).
Context (i j : Ordinal n) (f : (@Hom [Ord n]) i j).

Definition smallEquality_segments
  : is_extension_target (chain_segment c i j f) Q
  := chain_extension_target c Q E i j f.

Definition smallEquality_diagram
  : is_extension_target (fmap ⟦c⟧Ch f) Q
  := chain_extension_target c Q E i j f.

Context (a : (@Hom C) (c i) Q).
Let e
  := chain_extension_target c Q E i j f a.

Definition smallEquality_recovery
  : e.1 ∘ chain_segment c i j f ≈ a
  := e.2.

Definition smallEquality_fixed (D : @Ob C) (r : (@Hom C) D (c i))
    (d : (@Hom C) D Q) (H : a ∘ r ≈ d)
  : e.1 ∘ (chain_segment c i j f ∘ r) ≈ d
  := map_extension_preserves e.2 r d H.

End smallEquality.
