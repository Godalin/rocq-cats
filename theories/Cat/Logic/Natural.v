From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Preorder.

(** * Pointwise Comparisons into Preorder Categories

    Fix an arbitrary source category and a Type-valued preorder target.
    Pointwise relation witnesses form natural transformations, because
    parallel target arrows have the specified thin equality. Retain both
    maps of mutual comparisons when forming natural isomorphisms. *)

(** * 到预序范畴的逐点比较

    固定任意源范畴及 Type 值预序目标。由于目标平行箭头具有指定薄相等，
    逐点关系见证组成自然变换；构造自然同构时保留相互比较的两个映射。 *)

Section PreorderNatural.
Universes x r p l.
Context {C : Cat} {X : Type@{x}} {R : crelation@{x r} X}
    `{HR : !PreOrder R}.
Let D
  : Cat@{x r p l l}
  := @PreorderCatAt@{x r p l} X R HR.
Context {F G : Fct C D}.

(** Assemble the supplied components into the existing natural
    transformation interface, without any thinness assumption on [C].
    Supply both functors explicitly to fix their chosen arrow maps. *)

(** 将给定分量组装为既有自然变换接口，不对 [C] 施加薄性假设。
    显式给出两个函子，以固定其选定箭头映射。 *)

Program Definition PreorderN (H : ∀ c, R (F c) (G c))
  : F ⇒ G
  :=
  {|nt := H
  |}.
Next Obligation. exact tt. Defined.

(** Components are definitionally the supplied relation witnesses. *)

(** 分量定义上就是给定的关系见证。 *)

Definition preorder_n_data (H : ∀ c, R (F c) (G c)) (c : @Ob C)
  : PreorderN H c = H c
  := eq_refl.

(** Mutual pointwise comparisons give an existing natural isomorphism.
    Both inverse laws use specified target equality, not witness equality. *)

(** 逐点相互比较给出既有自然同构；两个互逆律使用指定目标相等，不用见证相等。 *)

Definition PreorderNatIso (H : ∀ c, R (F c) (G c) ∧ R (G c) (F c))
  : F ≅N G.
Proof.
  exists (PreorderN (λ c, fst (H c))).
  intros c. exists (snd (H c)). split; exact tt.
Defined.

(** The forward transformation keeps the first selected comparison. *)

(** 正向变换保留第一个选定比较。 *)

Definition preorder_nat_iso_data
    (H : ∀ c, R (F c) (G c) ∧ R (G c) (F c)) (c : @Ob C)
  : (PreorderNatIso H).1 c = fst (H c)
  := eq_refl.

(** The inverse transformation, derived by the general inverse theory,
    computes to the second supplied comparison. *)

(** 由一般取逆理论推导的逆变换，计算为给定的第二个比较。 *)

Definition preorder_nat_iso_inv_data
    (H : ∀ c, R (F c) (G c) ∧ R (G c) (F c)) (c : @Ob C)
  : NatIso_inv (PreorderNatIso H).1 (PreorderNatIso H).2 c = snd (H c)
  := eq_refl.

(** All parallel natural transformations agree in the existing [NatEq].
    Their components and naturality records need not be natively equal. *)

(** 所有平行自然变换在既有 [NatEq] 下相等，不要求分量或自然性记录原生相等。 *)

Definition preorder_nat_eq (α β : F ⇒ G)
  : α ≈N β
  := λ c, tt.

End PreorderNatural.

Arguments PreorderN {C X R HR} F G H.
Arguments PreorderNatIso {C X R HR} F G H.
