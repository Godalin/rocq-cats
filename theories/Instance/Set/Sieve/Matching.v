From Cats Require Export
  Instance.Set.Sieve.Core.
From Cats Require Import
  Instance.Set.Isomorphism.

(** * Matching Data for Generated Sieves

    A value on each generator, compatible on every common factor, gives a
    unique map from the generated sieve. Overlap witnesses stay in Type;
    neither a preferred factorization nor equality of witnesses is needed. *)

(** * 生成筛的匹配数据

    每个生成元上的值若在全部共同因子上相容，就唯一给出从生成筛出发的映射。
    交叠见证保留在 Type 中，不选取优先分解，也不比较见证。 *)

Section Matching.
Universes v q.
Context {C : Cat} {A : @Ob C} {I : Type} {D : I → @Ob C}
    (g : ∀ i, Hom (D i) A)
    (P : Functor (C^op) SetCat@{v q _ _ _ _ _}).

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

(** Descend matching data by evaluating any retained factorization. *)

(** 沿任一保留分解求值，使匹配数据下降。 *)

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
  apply (matching_overlap a X i j h k).
  transitivity f; [symmetry; exact E |].
  transitivity f'; [exact H | exact F].
Defined.
Next Obligation.
  intros [[a0 [i [h E]]]].
  exact (functor_comp _ _ P f h (a i)).
Defined.

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
  exact (@func_proper _ _ (fmap P h) _ _ (H i)).
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
Proof. intros i. exact (functor_id _ _ P (a i)). Defined.

(** Descending the generator values recovers the entire map. *)

(** 对生成元处的值作下降，恢复整个映射。 *)

Lemma matching_descend_η (α : SievePsh (GeneratedSieve D g) ⇒ P)
  : SieveMatchingN (SieveMatchingOfN α) ≈N α.
Proof.
  intros X [[f [i [h E]]]].
  pose (a := {|lower := (g i; generated_sieve_member g i)
              |} : SievePsh (GeneratedSieve D g) (D i)).
  transitivity (α X (fmap (SievePsh (GeneratedSieve D g)) h a)).
  - symmetry. exact (nt_naturality α h a).
  - apply func_proper. exact {|lower := symmetry E
                             |}.
Defined.

(** Matching data have a unique descent with the prescribed generator
    values. Uniqueness uses the general generator equality criterion. *)

(** 匹配数据具有生成元值指定的唯一下降；唯一性复用一般生成元判等。 *)

Definition matching_descend_universal (a : SieveMatching)
  : is_unique (R := @NatEq _ _ _ _)
      (λ α, MatchingEq (SieveMatchingOfN α) a) (SieveMatchingN a).
Proof.
  refine {|this := _
          ; that := _
          |}.
  - exact (matching_descend_β a).
  - intros α H.
    apply (snd (generated_sieve_map_eq g α (SieveMatchingN a))).
    intros i. transitivity (a i).
    + exact (H i).
    + symmetry. exact (matching_descend_β a i).
Defined.

End Matching.

(** Both correspondences form an isomorphism after ordinary size inclusion
    into common carrier and equality universes. *)

(** 双向对应经通常的大小嵌入进入共同载体及相等宇宙后，组成广集同构。 *)

Definition sieve_matching_iso@{u p v q +} {C : Cat} {A : @Ob C}
    {I : Type} {D : I → @Ob C} (g : ∀ i, Hom (D i) A)
    (P : Functor (C^op) SetCat@{v q _ _ _ _ _})
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
