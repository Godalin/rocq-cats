From Cats Require Export
  Instance.Set.Sieve.Core.
From Cats Require Import
  Instance.Set.Isomorphism
  Instance.Set.PresheafDescent.

(** * Matching Data for Generated Sieves

    A value on each generator, compatible on every common factor, gives a
    unique map from the generated sieve. Overlap witnesses stay in Type;
    neither a preferred factorization nor equality of witnesses is needed. *)

(** * 生成筛的匹配数据

    每个生成元上的值若在全部共同因子上相容，就唯一给出从生成筛出发的映射。
    交叠见证保留在 Type 中，不选取优先分解，也不比较见证。 *)

(** The retained membership factor is a cover of the sieve presheaf in the
    sense of %\coqref{Cats.Instance.Set.PresheafDescent.is presheaf cover}
    {%[is_presheaf_cover]%}%. The generator is its actual sieve member. *)

(** 保留的隶属分解给出筛预层的
    %\coqref{Cats.Instance.Set.PresheafDescent.is presheaf cover}
    {%[is_presheaf_cover]%}% 覆盖；生成元就是实际筛成员。 *)

Definition generated_sieve_cover@{u p +} {C : Cat} {A : @Ob C}
    {I : Type} {D : I → @Ob C} (g : ∀ i, Hom (D i) A)
  : is_presheaf_cover
      (Q := SievePsh (GeneratedSieve D g) :
        Fct (C^op) SetCat@{u p _ _ _ _ _})
      (λ i, {|lower := (g i; generated_sieve_member g i)
             |}).
Proof.
  intros X [[f [i [h E]]]]. exists i, h.
  exact {|lower := symmetry E
         |}.
Defined.

(** ** Matching and Descent

    Fix a generating arrow family and a target presheaf. The general
    presheaf-cover theorem now constructs descent and its universal
    property, retaining the original generator-value interface. *)

(** ** 匹配与下降

    固定生成箭头族和目标预层。以下由一般预层覆盖定理构造下降及其泛性质，
    保留原生成元值接口。 *)

Section Matching.
Universes v q.
Context {C : Cat} {A : @Ob C} {I : Type} {D : I → @Ob C}
    (g : ∀ i, Hom (D i) A)
    (P : Fct (C^op) SetCat@{v q _ _ _ _ _}).

(** Matching values satisfy the restriction equation on every overlap.
    Coercion evaluates the matching data at a generator as [a i]. *)

(** 匹配值在每个交叠上满足限制方程；强制转换以 [a i] 在生成元处求值。 *)

Record SieveMatching
  :=
  { matching_value (i : I) :> P (D i)
  ; matching_overlap (X : @Ob C) (i j : I)
      (f : Hom X (D i)) (h : Hom X (D j))
      (E : g i ∘ f ≈ g j ∘ h)
    : fmap P f (matching_value i) ≈S fmap P h (matching_value j)
  }.

(** Equality compares only generator values, with their specified equality. *)

(** 相等只按指定相等比较生成元处的值。 *)

Definition MatchingEq (a b : SieveMatching)
  : Type
  := ∀ i, a i ≈S b i.

(** Pointwise value equality supplies the equivalence laws. *)

(** 逐点值相等提供等价律。 *)

Global Instance MatchingEq_Equivalence
  : Equivalence MatchingEq.
Proof.
  split.
  - intros a i. reflexivity.
  - intros a b H i. symmetry. apply H.
  - intros a b c H K i. transitivity (b i); [apply H | apply K].
Defined.

(** The canonical matching setoid retains all overlap data in its carrier;
    its projection supports inference from the matching-data type. *)

(** 典范匹配广集在载体中保留全部交叠数据，其投影支持从匹配数据类型反推广集。 *)

Program Canonical SieveMatchingS
  : SetC
  :=
  {|carrier := SieveMatching
  ; carrier_equiv := MatchingEq
  |}.

(** A sieve overlap is exactly an equality of the generator restrictions
    in its presheaf. Membership witnesses need not agree. *)

(** 筛的交叠正是其预层中生成元限制的相等；隶属见证无需一致。 *)

Lemma sieve_matching_compatible (a : SieveMatching)
  : presheaf_values_compatible
      (Q := SievePsh (GeneratedSieve D g))
      (λ i, {|lower := (g i; generated_sieve_member g i)
             |}) (λ i, a i).
Proof. intros X i j f h [E]. exact (matching_overlap a X i j f h E). Defined.

(** Descend matching data by evaluating the same retained factorization
    as before. The general theorem supplies respectfulness and naturality. *)

(** 仍沿原保留分解求值使匹配数据下降；保相等性和自然性由一般定理提供。 *)

Program Definition SieveMatchingN (a : SieveMatching)
  : SievePsh (GeneratedSieve D g) ⇒ P
  :=
  {|nt X :=
      {|func x := match (lower x).2 with
          | (i; (h; _)) => fmap P h (a i)
          end
      |}
  |}.
Next Obligation.
  intros [[f [i [h E]]]] [[f' [j [k F]]]] [H].
  exact (@func_proper _ _
    (PresheafDescendN _ (generated_sieve_cover g) (λ i, a i)
      (sieve_matching_compatible a) X)
    {|lower := (f; (i; (h; E)))|}
    {|lower := (f'; (j; (k; F)))|} {|lower := H|}).
Defined.
Next Obligation.
  intros [[a0 [i [h E]]]].
  exact (nt_naturality
    (PresheafDescendN _ (generated_sieve_cover g) (λ i, a i)
      (sieve_matching_compatible a)) f
    {|lower := (a0; (i; (h; E)))|}).
Defined.

(** The original raw map is the general descent in specified natural
    equality. Keeping its original component expression also preserves
    conversion for clients with an opaque sieve element. *)

(** 原始映射按指定自然相等就是一般下降；保留原分量表达式也保持含不透明
    筛元素的客户端所需的定义转换。 *)

Lemma sieve_matching_descend_eq (a : SieveMatching)
  : PresheafDescendN _ (generated_sieve_cover g) (λ i, a i)
      (sieve_matching_compatible a) ≈N SieveMatchingN a.
Proof. intros X [[f [i [h E]]]]. reflexivity. Defined.

(** Restrict a sieve map to its generating members. Naturality and
    respectfulness provide all overlap equations. *)

(** 将筛映射限制到生成元；自然性及保相等性提供全部交叠方程。 *)

Program Definition SieveMatchingOfN
    (α : SievePsh (GeneratedSieve D g) ⇒ P)
  : SieveMatching
  :=
  {|matching_value i := α (D i)
      {|lower := (g i; generated_sieve_member g i)
      |}
  |}.
Next Obligation.
  pose (a := {|lower := (g i; generated_sieve_member g i)
              |} : SievePsh (GeneratedSieve D g) (D i)).
  pose (b := {|lower := (g j; generated_sieve_member g j)
              |} : SievePsh (GeneratedSieve D g) (D j)).
  transitivity (α X (fmap (SievePsh (GeneratedSieve D g)) f a)).
  - symmetry. exact (nt_naturality α f a).
  - transitivity (α X (fmap (SievePsh (GeneratedSieve D g)) h b)).
    + apply func_proper. exact {|lower := E
                               |}.
    + exact (nt_naturality α h b).
Defined.

(** Descent preserves pointwise equality of the matching values. *)

(** 下降保持匹配值的逐点相等。 *)

Program Definition matching_descend_resp
  : SieveMatchingS →r Nat_SetS (SievePsh (GeneratedSieve D g)) P
  :=
  {|func := SieveMatchingN
  |}.
Next Obligation.
  intros a b H X [[f [i [h E]]]].
  exact (presheaf_descend_proper _ (generated_sieve_cover g)
    (generated_sieve_cover g) (λ i, a i) (λ i, b i)
    (sieve_matching_compatible a) (sieve_matching_compatible b) H X
    {|lower := (f; (i; (h; E)))|}).
Defined.

(** Extraction preserves equality of natural transformations. *)

(** 提取保持自然变换的相等。 *)

Program Definition matching_extract_resp
  : Nat_SetS (SievePsh (GeneratedSieve D g)) P →r SieveMatchingS
  :=
  {|func := SieveMatchingOfN
  |}.
Next Obligation. intros α β H i. exact (H _ _). Defined.

(** Extracting the descended values recovers the original matching data. *)

(** 提取下降后的值，恢复原匹配数据。 *)

Lemma matching_descend_β (a : SieveMatching)
  : MatchingEq (SieveMatchingOfN (SieveMatchingN a)) a.
Proof.
  intros i. exact (presheaf_descend_β _ (generated_sieve_cover g)
    (λ i, a i) (sieve_matching_compatible a) i).
Defined.

(** Descending the generator values recovers the entire map. *)

(** 对生成元处的值作下降，恢复整个映射。 *)

Lemma matching_descend_η (α : SievePsh (GeneratedSieve D g) ⇒ P)
  : SieveMatchingN (SieveMatchingOfN α) ≈N α.
Proof.
  transitivity (PresheafDescendN _ (generated_sieve_cover g)
    (λ i, SieveMatchingOfN α i)
    (sieve_matching_compatible (SieveMatchingOfN α))).
  - symmetry. apply sieve_matching_descend_eq.
  - transitivity (PresheafDescendN _ (generated_sieve_cover g)
      (λ i, SieveMatchingOfN α i) (presheaf_map_values_compatible _ α)).
    + apply presheaf_descend_proper. intros i. reflexivity.
    + apply presheaf_descend_η.
Defined.

(** Matching data have a unique descent with the prescribed generator
    values. The universal property is the general cover descent theorem. *)

(** 匹配数据具有生成元值指定的唯一下降；泛性质复用一般覆盖下降定理。 *)

Definition matching_descend_universal (a : SieveMatching)
  : is_unique (R := @NatEq _ _ _ _)
      (λ α, MatchingEq (SieveMatchingOfN α) a) (SieveMatchingN a).
Proof.
  refine {|this := _
          ; that := _
          |}.
  - exact (matching_descend_β a).
  - intros α H.
    transitivity (PresheafDescendN _ (generated_sieve_cover g)
      (λ i, a i) (sieve_matching_compatible a)).
    + exact (@that _ _ _ _ _ (presheaf_descend_universal _ (generated_sieve_cover g)
        (λ i, a i) (sieve_matching_compatible a)) α H).
    + apply sieve_matching_descend_eq.
Defined.

End Matching.

(** Both correspondences form an isomorphism after ordinary size inclusion
    into common carrier and equality universes. *)

(** 双向对应经通常的大小嵌入进入共同载体及相等宇宙后，组成广集同构。 *)

Definition sieve_matching_iso@{u p v q +} {C : Cat} {A : @Ob C}
    {I : Type} {D : I → @Ob C} (g : ∀ i, Hom (D i) A)
    (P : Fct (C^op) SetCat@{v q _ _ _ _ _})
  : LiftS@{_ _ u p} (SieveMatchingS g P) ≅[SetCat]
      LiftS@{_ _ u p} (Nat_SetS (SievePsh (GeneratedSieve D g)) P).
Proof.
  exists ((matching_descend_resp g P)^↑S), ((matching_extract_resp g P)^↑S).
  split.
  - intros [a]. exact {|lower := matching_descend_β g P a
                       |}.
  - intros [α]. exact {|lower := matching_descend_η g P α
                       |}.
Defined.
