From Cats Require Export
  Algebra.Monoid.Category
  Algebra.Monoid.Chain.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Shape.Ordinal
  Instance.Nat.Order.

Local Open Scope nat_scope.
Local Open Scope monoid_scope.

(** * Arrow Chains as Single-Object Diagrams *)

(** * 箭头链的单对象图式解释 *)

(** Pointwise equal arrow data give an identity-component natural
    isomorphism of single-object diagrams. This is only a sufficient
    condition for natural isomorphism, not a new functor equality. *)

(** 逐点相等的箭头数据给出分量为恒等的单对象图式自然同构。这只是自然同构的
    充分条件，不另定义函子相等。 *)

Program Definition monoid_diagram_iso@{u p +}
    {M : SetC@{u p}} `{HM : !Monoid M}
    {J : Cat} (F G : Fct J B(M))
    (H : ∀ i j (f : (@Hom J) i j), fmap F f ≈S fmap G f)
  : F ≅N G
  := ({|nt j := 1
      |}; _).
Next Obligation.
  change (1 ⋅ fmap F f ≈S fmap G f ⋅ 1).
  rewrite monoid_unit_l, monoid_unit_r. apply H.
Defined.
Next Obligation.
  intros j. exists 1. split; change (1 ⋅ 1 ≈S (1 : M));
    apply monoid_unit_l.
Defined.

(** Interpret every ordered interval as its product in the arrow chain.
    The object map is constant; no equality between objects is needed. *)

(** 将每个有序区间解释为箭头链中的段积。对象映射为常映射，不需要比较对象。 *)

Program Definition MonoidChainF@{u p +}
    {M : SetC@{u p}} `{HM : !Monoid M}
    {n : nat} (xs : M ^S n)
  : Fct [Ord n] B(M)
  :=
  {|F0 i := tt
  ; F1 i j f := xs⟦i, j⟧⋅
  |}.
Next Obligation. intros f g H. reflexivity. Defined.
Next Obligation. apply monoid_segment_id. Defined.
Next Obligation.
  apply monoid_segment_comp; apply nat_le_to_le; assumption.
Defined.

(** Equal chains give naturally isomorphic diagrams. *)

(** 相等的箭头链给出自然同构的图式。 *)

Global Instance MonoidChainF_proper@{u p +}
    {M : SetC@{u p}} `{HM : !Monoid M}
    {n : nat}
  : Proper (carrier_equiv (M ^S n) ==> NatIso) (@MonoidChainF M HM n).
Proof.
  intros xs ys H. apply monoid_diagram_iso. intros i j f.
  apply monoid_segment_proper; [exact H | reflexivity | reflexivity].
Defined.

(** Chain substitution agrees with precomposition of the associated
    diagrams. The comparison uses the segment subdivision law. *)

(** 箭头链替换与对应图式的预复合相容；比较使用段积的细分定律。 *)

Definition monoid_chain_sub_iso@{u p +}
    {M : SetC@{u p}} `{HM : !Monoid M}
    {m n : nat} (f : Fct [Ord m] [Ord n]) (xs : M ^S n)
  : MonoidChainF xs[f]M ≅N (MonoidChainF xs ∘F f).
Proof.
  apply monoid_diagram_iso. intros i j a.
  apply monoid_segment_sub.
  - exact (ordinal_functor_monotone f).
  - exact (nat_le_to_le a).
Defined.
