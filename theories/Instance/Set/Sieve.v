From Cats Require Export
  Cat.Sieve
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core
  Instance.Set.Presheaf
  Instance.Set.Yoneda.
From Cats Require Import
  Cat.Morphism
  Instance.Set.Lift.
From Cats.Set Require Export
  Subset.

(** * Sieves as Subpresheaves of Representables

    Membership witnesses belong to carriers, while specified equality
    compares only the underlying arrows. The selected value carrier universe
    must contain these witnesses; its equality universe remains independent. *)

(** * 作为可表预层子预层的筛

    隶属见证属于载体，指定相等只比较底层箭头。所选值载体宇宙须容纳这些见证；
    相等宇宙保持独立。 *)

(** Realize a sieve as a presheaf, raised to the chosen value universes. *)

(** 将筛实现为预层，并提升到所选值宇宙。 *)

Program Definition SievePsh@{u p +} {C : Cat} {A : @Ob C}
    (S : Sieve C A)
  : Functor (C^op) SetCat@{u p _ _ _ _ _}
  :=
  {|F0 X := LiftS (SubsetS (@HomSet C X A) (@sieve_member C A S X))
  ; F1 X Y f :=
      {|func x :=
        {|lower := ((lower x).1 ∘ f;
            sieve_precomp S (lower x).1 f (lower x).2)
        |}
      |}
  |}.
Next Obligation.
  intros [x] [y] [H]. exact {|lower := comp_proper _ _ H _ _ (reflexivity f)
                            |}.
Defined.
Next Obligation.
  intros f g H [x]. exact {|lower := comp_proper _ _ (reflexivity x.1) _ _ H
                           |}.
Defined.
Next Obligation.
  intros [x]. exact {|lower := comp_id_r x.1
                     |}.
Defined.
Next Obligation.
  intros [x]. exact {|lower := symmetry (comp_assoc x.1 g f)
                     |}.
Defined.

(** The inclusion forgets membership and is natural by construction. *)

(** 包含映射忘却隶属见证，并由构造满足自然性。 *)

Program Definition SieveInclusionN@{u p +} {C : Cat} {A : @Ob C}
    (S : Sieve C A)
  : (SievePsh S : Functor (C^op) SetCat@{u p _ _ _ _ _}) ⇒
      RaisedEmbedding A
  :=
  {|nt X :=
      {|func x :=
        {|lower := (lower x).1
        |}
      |}
  |}.
Next Obligation. intros x y H. exact H. Defined.
Next Obligation. intros x. reflexivity. Defined.

Notation "'ιSv[' S ']'" := (SieveInclusionN S) : hom_scope.

(** Membership witnesses do not affect equality, so the inclusion is monic. *)

(** 隶属见证不影响相等，因此包含映射是单态射。 *)

Lemma sieve_inclusion_mono@{u p +} {C : Cat} {A : @Ob C}
    (S : Sieve C A)
  : @is_mono (Fct (C^op) SetCat@{u p _ _ _ _ _}) _ _ ιSv[S].
Proof. intros P α β H X x. exact (H X x). Defined.

(** A containment of sieves induces a map preserving the underlying arrow. *)

(** 筛的包含关系诱导保留底层箭头的映射。 *)

Program Definition SieveMapN@{u p +} {C : Cat} {A : @Ob C}
    {S R : Sieve C A}
    (H : ∀ X (f : Hom X A), f ∈Sv S → f ∈Sv R)
  : (SievePsh S : Functor (C^op) SetCat@{u p _ _ _ _ _}) ⇒ SievePsh R
  :=
  {|nt X :=
      {|func x :=
        {|lower := ((lower x).1; H X (lower x).1 (lower x).2)
        |}
      |}
  |}.
Next Obligation. intros x y E. exact E. Defined.
Next Obligation.
  intros x. exact {|lower := reflexivity ((lower x).1 ∘ f)
                  |}.
Defined.

(** The containment map commutes with both inclusions. *)

(** 包含关系诱导的映射与两侧包含映射交换。 *)

Lemma sieve_map_inclusion@{u p +} {C : Cat} {A : @Ob C}
    {S R : Sieve C A}
    (H : ∀ X (f : Hom X A), f ∈Sv S → f ∈Sv R)
  : (ιSv[R] ∘Nv (SieveMapN H :
      (SievePsh S : Functor (C^op) SetCat@{u p _ _ _ _ _}) ⇒ _))
      ≈N ιSv[S].
Proof. intros X x. reflexivity. Defined.

(** Every member arrow determines a factorization of its representable map
    through the sieve. Its carrier is postcomposition by that arrow. *)

(** 每条属于筛的箭头使其可表映射经过该筛分解；载体映射为与该箭头后合成。 *)

Program Definition SieveFactorN@{u p +} {C : Cat} {A B : @Ob C}
    {S : Sieve C A} (f : Hom B A) (H : f ∈Sv S)
  : (RaisedEmbedding B : Functor (C^op) SetCat@{u p _ _ _ _ _}) ⇒
      SievePsh S
  :=
  {|nt X :=
      {|func x :=
        {|lower := (f ∘ lower x; sieve_precomp S f (lower x) H)
        |}
      |}
  |}.
Next Obligation.
  intros [x] [y] [E]. exact {|lower := comp_proper _ _ (reflexivity f) _ _ E
                            |}.
Defined.
Next Obligation.
  intros [x]. exact {|lower := symmetry (comp_assoc f x f0)
                     |}.
Defined.

(** The factorization recovers the representable action after inclusion. *)

(** 分解后接包含映射，恢复可表函子的箭头作用。 *)

Lemma sieve_factor_comm@{u p +} {C : Cat} {A B : @Ob C}
    {S : Sieve C A} (f : Hom B A) (H : f ∈Sv S)
  : (ιSv[S] ∘Nv (SieveFactorN f H :
      (RaisedEmbedding B : Functor (C^op) SetCat@{u p _ _ _ _ _}) ⇒ _))
      ≈N fmap RaisedEmbedding f.
Proof. intros X x. reflexivity. Defined.

(** Restrict the Yoneda map of an element to the sieve. This construction
    applies to every presheaf and keeps the original element computation. *)

(** 将元素的 Yoneda 映射限制到筛；此构造适用于任意预层，并保留原元素的计算。 *)

Program Definition sieve_restrict_resp@{u p +} {C : Cat} {A : @Ob C}
    (S : Sieve C A) {P : Functor (C^op) SetCat@{u p _ _ _ _ _}}
  : P A →r Nat_SetS (SievePsh S) P
  :=
  {|func x := presheaf_yoneda_inv_resp (C := C) (P := P) (X := A) x
      ∘Nv ιSv[S]
  |}.
Next Obligation.
  intros x y H X a.
  exact (@func_proper _ _ (fmap P (lower a).1) x y H).
Defined.

Notation "x '↾Sv[' P ';' S ']'" := (sieve_restrict_resp S (P := P) x)
  (at level 8, left associativity, format "x ↾Sv[ P ;  S ]") : hom_scope.

(** Extending a sieve map to a representable is equivalent to finding an
    element with that restriction. This is Yoneda, with retained extensions. *)

(** 将筛映射延拓到可表预层，等价于寻找具有该限制的元素；这是保留延拓数据的
    Yoneda 对应。 *)

Definition sieve_extension_iff@{u p +} {C : Cat} {A : @Ob C}
    (S : Sieve C A) {P : Functor (C^op) SetCat@{u p _ _ _ _ _}}
    (h : SievePsh S ⇒ P)
  : (∃ α : RaisedEmbedding A ⇒ P, (α ∘Nv ιSv[S]) ≈N h) ↔
      (∃ x : P A, x↾Sv[P; S] ≈N h).
Proof.
  split.
  - intros [α H]. exists (presheaf_yoneda_resp α).
    intros X a. transitivity (α X (ιSv[S] X a)).
    + exact (presheaf_yoneda_η α X (ιSv[S] X a)).
    + exact (H X a).
  - intros [x H].
    exists (presheaf_yoneda_inv_resp (C := C) (P := P) (X := A) x).
    exact H.
Defined.

(** Maps from a generated sieve agree exactly when they agree on its
    generating members. Naturality propagates equality to all factors;
    membership witnesses and their possible multiple presentations disappear
    only from the equality comparison. *)

(** 从生成筛出发的映射相等，当且仅当它们在生成元处相等。自然性将相等传播到
    全部因子；隶属见证及其可能的多种表示只在相等比较中被忽略。 *)

Definition generated_sieve_map_eq@{u p +} {C : Cat} {A : @Ob C}
    {I : Type} {D : I → @Ob C} (g : ∀ i, Hom (D i) A)
    {P : Functor (C^op) SetCat@{u p _ _ _ _ _}}
    (α β : SievePsh (GeneratedSieve D g) ⇒ P)
  : α ≈N β ↔ ∀ i,
      α (D i) {|lower := (g i; generated_sieve_member g i)
               |} ≈S
      β (D i) {|lower := (g i; generated_sieve_member g i)
               |}.
Proof.
  split.
  - intros H i. apply H.
  - intros H X [[f [i [h E]]]].
    pose (a := {|lower := (g i; generated_sieve_member g i)
                |} : SievePsh (GeneratedSieve D g) (D i)).
    transitivity (α X (fmap (SievePsh (GeneratedSieve D g)) h a)).
    + apply func_proper. exact {|lower := E
                               |}.
    + transitivity (fmap P h (α (D i) a)).
      * exact (nt_naturality α h a).
      * transitivity (fmap P h (β (D i) a)).
        -- apply func_proper. exact (H i).
        -- transitivity (β X (fmap (SievePsh (GeneratedSieve D g)) h a)).
           ++ symmetry. exact (nt_naturality β h a).
           ++ apply func_proper. exact {|lower := symmetry E
                                       |}.
Defined.
