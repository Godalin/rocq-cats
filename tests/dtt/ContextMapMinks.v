From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Arrow.Core
  Instance.Set.Core
  Instance.Set.Fam.Core
  Instance.Set.Fam.Cat
  DTT.CwF
  DTT.Comprehension.

(* The generated view preserves the supplied square, including its witness. *)
Section SquareClients.
Context {C : Cat} (T : Fct (C^op) FamCat)
  `{HC : !HasContextExtension T} (X Y Z : ContextType T).
Context (s : ArrowHom (ContextProjectionArrow T X) (ContextProjectionArrow T Y)).

Example context_square_view
  : (MakeContextMap T X Y s
      : ArrowHom (ContextProjectionArrow T X) (ContextProjectionArrow T Y)) = s.
Proof. reflexivity. Qed.

Example context_identity_base
  : arrow_bottom (context_map_id T X) = id[X.1].
Proof. reflexivity. Qed.

Example context_identity_extension
  : arrow_top (context_map_id T X) = id[X.1 ▹[T] X.2].
Proof. reflexivity. Qed.

Example context_composite_base (f : ContextMap T X Y) (g : ContextMap T Y Z)
  : arrow_bottom (g ∘Ctx[T] f) = arrow_bottom g ∘ arrow_bottom f.
Proof. reflexivity. Qed.

Example context_composite_extension (f : ContextMap T X Y) (g : ContextMap T Y Z)
  : arrow_top (g ∘Ctx[T] f) = arrow_top g ∘ arrow_top f.
Proof. reflexivity. Qed.

Example context_base_rewrite (f g : ContextMap T X Y) (H : ContextMapEq T f g)
  : fmap (CwFBaseF T) f ≈ fmap (CwFBaseF T) g.
Proof. rewrite H. reflexivity. Qed.

Example context_extension_rewrite (f g : ContextMap T X Y)
    (H : ContextMapEq T f g)
  : fmap (CwFExtF T) f ≈ fmap (CwFExtF T) g.
Proof. rewrite H. reflexivity. Qed.

End SquareClients.

(* Large type/term fibers do not enter the universe of stored square data. *)
Section SquareLevels.
Universes o h p l a b c d.
Constraint Set < h.
Constraint h < p.
Constraint p < l.
Constraint l < a.
Constraint a < b.
Constraint b < c.
Constraint c < d.
Constraint d < o.
Context (C : Cat@{o h p l l}) (D : Cat@{o p h l l}).
Context (T : Fct (C^op) FamCat@{_ _ _ _ _ a c _ b d _ _ _ _ _ _})
  (U : Fct (D^op) FamCat@{_ _ _ _ _ c a _ d b _ _ _ _ _ _}).
Context (HC : HasContextExtension T) (KC : HasContextExtension U).
Local Existing Instance HC.
Local Existing Instance KC.

Definition high_equality_context_square (X Y : ContextType T)
  : Type@{p}
  := ContextMap T X Y.

Definition low_equality_context_square (X Y : ContextType U)
  : Type@{p}
  := ContextMap U X Y.

Definition high_equality_square_constructor (X Y : ContextType T)
    (s : ArrowHom (ContextProjectionArrow T X) (ContextProjectionArrow T Y))
  : ContextMap T X Y
  := MakeContextMap T X Y s.

Definition low_equality_square_constructor (X Y : ContextType U)
    (s : ArrowHom (ContextProjectionArrow U X) (ContextProjectionArrow U Y))
  : ContextMap U X Y
  := MakeContextMap U X Y s.

Fail Definition context_square_forced_small (X Y : ContextType T)
  : Type@{h}
  := ContextMap T X Y.

End SquareLevels.
