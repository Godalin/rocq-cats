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

Program Definition FctS (C D : Cat)
  : SetC
  :=
  {|carrier := Fct C D
  ; carrier_equiv := NatIso
  ; carrier_setoid := NatIso_Equivalence
  |}.

(** Precomposition is a respectful map of functor setoids. *)

(** 预复合是函子广集之间的保相等映射。 *)

Program Definition fct_precomp_resp {A B C : Cat} (F : Fct A B)
  : FctS B C →r FctS A C
  :=
  {|func G := G ∘F F
  |}.
Next Obligation.
  intros G H E. exact (CompF_proper G H E F F (reflexivity F)).
Defined.

(** Postcomposition is a respectful map of functor setoids. *)

(** 后复合是函子广集之间的保相等映射。 *)

Program Definition fct_postcomp_resp {A B C : Cat} (G : Fct B C)
  : FctS A B →r FctS A C
  :=
  {|func F := G ∘F F
  |}.
Next Obligation.
  intros F H E. exact (CompF_proper G G (reflexivity G) F H E).
Defined.

(** Naturally isomorphic precomposition functors induce equal maps. *)

(** 自然同构的预复合函子诱导相等的映射。 *)

Global Instance fct_precomp_proper {A B C : Cat}
  : Proper (NatIso ==> FunEq) (@fct_precomp_resp A B C).
Proof.
  intros F G H K. exact (CompF_proper K K (reflexivity K) F G H).
Defined.

(** Naturally isomorphic postcomposition functors induce equal maps. *)

(** 自然同构的后复合函子诱导相等的映射。 *)

Global Instance fct_postcomp_proper {A B C : Cat}
  : Proper (NatIso ==> FunEq) (@fct_postcomp_resp A B C).
Proof.
  intros F G H K. exact (CompF_proper F G H K K (reflexivity K)).
Defined.

(** Keep the comparison witnesses for precomposition, postcomposition
    and probe presheaves transparent. They carry natural isomorphisms,
    whose inverse components can be computed by nerve clients. *)

(** 预复合、后复合及探测预层的比较见证保持透明。它们携带自然同构，
    nerve 的调用方可以计算其中的逆分量。 *)

(** * Presheaves Defined by Category Probes

    Given a family of probe categories organized by a functor J, restrict
    functors from each probe to C by precomposition. Lifting puts native
    functor setoids into a common pair of value universes. *)

(** * 由范畴探测定义的预层

    给定由函子 J 组织的探测范畴族，对从各探测到 C 的函子作预复合限制。
    提升将原生函子广集放到共同的一对值宇宙中。 *)

Program Definition FctPsh@{u p +} {S : Cat}
    (J : Fct S CatCat) (C : Cat)
  : Fct (S^op) SetCat@{u p _ _ _ _ _}
  :=
  {|fobj s := LiftS (FctS (J s) C)
  ; fmap s t θ := (fct_precomp_resp (fmap J θ))^↑S
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation.
  intros θ φ H [F]. refine {|lower := _
                           |}.
  apply CompF_proper. reflexivity. exact (fmap_proper (IsFct := isFct J) _ _ H).
Defined.
Next Obligation.
  intros [F]. refine {|lower := _
                     |}.
  transitivity (F ∘F IdF).
  - apply CompF_proper. reflexivity. exact (fmap_id (IsFct := isFct J)).
  - apply CompF_id_r.
Defined.
Next Obligation.
  intros [F]. refine {|lower := _
                     |}.
  transitivity (F ∘F (fmap J g ∘F fmap J f)).
  - apply CompF_proper. reflexivity. exact (fmap_comp (IsFct := isFct J) g f).
  - symmetry. apply CompF_assoc.
Defined.

(** A functor of targets acts by postcomposition at every probe. *)

(** 目标之间的函子在每个探测处通过后复合作用。 *)

Program Definition FctPshN@{u p +} {S : Cat}
    (J : Fct S CatCat) {C D : Cat} (F : Fct C D)
  : (FctPsh J C : Fct (S^op) SetCat@{u p _ _ _ _ _}) ⇒
      FctPsh J D
  :=
  {|nt s := (fct_postcomp_resp F)^↑S
  |}.
Next Obligation.
  intros [G]. refine {|lower := _
                     |}. symmetry. apply CompF_assoc.
Defined.

(** Probe presheaves vary functorially in the target category. Functor
    equality in the source is natural isomorphism, as in CatCat. *)

(** 探测预层在目标范畴上构成函子；源中的函子相等沿用 CatCat 的自然同构。 *)

Program Definition FctPshF@{u p +} {S : Cat}
    (J : Fct S CatCat)
  : Fct CatCat (FctCat (S^op) SetCat@{u p _ _ _ _ _})
  :=
  {|fobj C := FctPsh J C
  ; fmap C D F := FctPshN J F
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
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
