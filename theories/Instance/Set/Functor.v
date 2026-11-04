From Cats Require Export
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core.
From Cats Require Import
  Cat.CatCat
  Instance.Set.Lift.

(** * Setoids of Functors

    Functors are compared by natural isomorphism, retaining the comparison
    and its inverse components. Domain and codomain sizes are independent. *)

(** * 函子广集

    函子按自然同构比较，保留比较及其逆分量；定义域和目标的大小相互独立。 *)

Program Definition FunctorS (C D : Cat)
  : SetC
  :=
  {|carrier := Functor C D
  ; carrier_equiv := NatIso
  ; carrier_setoid := NatIso_Equivalence
  |}.

(** Precomposition is a respectful map of functor setoids. *)

(** 预复合是函子广集之间的保相等映射。 *)

Program Definition functor_precomp_resp {A B C : Cat} (F : Functor A B)
  : FunctorS B C →r FunctorS A C
  :=
  {|func G := G ∘F F
  |}.
Next Obligation.
  intros G H E. exact (CompF_proper G H E F F (reflexivity F)).
Defined.

(** Postcomposition is a respectful map of functor setoids. *)

(** 后复合是函子广集之间的保相等映射。 *)

Program Definition functor_postcomp_resp {A B C : Cat} (G : Functor B C)
  : FunctorS A B →r FunctorS A C
  :=
  {|func F := G ∘F F
  |}.
Next Obligation.
  intros F H E. exact (CompF_proper G G (reflexivity G) F H E).
Defined.

(** Naturally isomorphic precomposition functors induce equal maps. *)

(** 自然同构的预复合函子诱导相等的映射。 *)

Global Instance functor_precomp_proper {A B C : Cat}
  : Proper (NatIso ==> FunEq) (@functor_precomp_resp A B C).
Proof.
  intros F G H K. exact (CompF_proper K K (reflexivity K) F G H).
Defined.

(** Naturally isomorphic postcomposition functors induce equal maps. *)

(** 自然同构的后复合函子诱导相等的映射。 *)

Global Instance functor_postcomp_proper {A B C : Cat}
  : Proper (NatIso ==> FunEq) (@functor_postcomp_resp A B C).
Proof.
  intros F G H K. exact (CompF_proper F G H K K (reflexivity K)).
Defined.

(** * Presheaves Defined by Category Probes

    Given a family of probe categories organized by a functor J, restrict
    functors from each probe to C by precomposition. Lifting puts native
    functor setoids into a common pair of value universes. *)

(** * 由范畴探测定义的预层

    给定由函子 J 组织的探测范畴族，对从各探测到 C 的函子作预复合限制。
    提升将原生函子广集放到共同的一对值宇宙中。 *)

Program Definition FunctorPresheaf@{u p +} {S : Cat}
    (J : Functor S CatCat) (C : Cat)
  : Functor (S^op) SetCat@{u p _ _ _ _ _}
  :=
  {|F0 s := LiftS (FunctorS (J s) C)
  ; F1 s t θ := (functor_precomp_resp (fmap J θ))^↑S
  |}.
Next Obligation.
  intros θ φ H [F]. refine {|lower := _
                           |}.
  apply CompF_proper. reflexivity. exact (functor_fmap_proper _ _ J _ _ H).
Defined.
Next Obligation.
  intros [F]. refine {|lower := _
                     |}.
  transitivity (F ∘F IdF).
  - apply CompF_proper. reflexivity. exact (functor_id _ _ J).
  - apply CompF_id_r.
Defined.
Next Obligation.
  intros [F]. refine {|lower := _
                     |}.
  transitivity (F ∘F (fmap J g ∘F fmap J f)).
  - apply CompF_proper. reflexivity. exact (functor_comp _ _ J g f).
  - symmetry. apply CompF_assoc.
Defined.

(** A functor of targets acts by postcomposition at every probe. *)

(** 目标之间的函子在每个探测处通过后复合作用。 *)

Program Definition FunctorPresheafN@{u p +} {S : Cat}
    (J : Functor S CatCat) {C D : Cat} (F : Functor C D)
  : (FunctorPresheaf J C : Functor (S^op) SetCat@{u p _ _ _ _ _}) ⇒
      FunctorPresheaf J D
  :=
  {|nt s := (functor_postcomp_resp F)^↑S
  |}.
Next Obligation.
  intros [G]. refine {|lower := _
                     |}. symmetry. apply CompF_assoc.
Defined.

(** Probe presheaves vary functorially in the target category. Functor
    equality in the source is natural isomorphism, as in CatCat. *)

(** 探测预层在目标范畴上构成函子；源中的函子相等沿用 CatCat 的自然同构。 *)

Program Definition FunctorPresheafF@{u p +} {S : Cat}
    (J : Functor S CatCat)
  : Functor CatCat (Fct (S^op) SetCat@{u p _ _ _ _ _})
  :=
  {|F0 C := FunctorPresheaf J C
  ; F1 C D F := FunctorPresheafN J F
  |}.
Next Obligation.
  intros F G H s [K]. refine {|lower := _
                             |}.
  apply CompF_proper. exact H. reflexivity.
Defined.
Next Obligation.
  intros s [F]. exact {|lower := CompF_id_l F
                      |}.
Defined.
Next Obligation.
  intros s [F]. exact {|lower := CompF_assoc f g F
                      |}.
Defined.
