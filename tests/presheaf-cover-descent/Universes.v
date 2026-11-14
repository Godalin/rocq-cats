From Cats Require Import
  Instance.Set.Lift
  Instance.Set.PresheafDescent
  Instance.Set.Sieve.Matching.
From Cats.Set Require Import
  Pi
  Subset.

(** * Independent Source, Target and Index Sizes *)

(** * 独立的来源、目标与索引大小 *)

(** ** Equality Below the Carrier

    The category, hom data and generator index are larger than the value
    carriers. Equality lies below the carrier in the first profile and
    above it in the second. No coherent or respectful cover is assumed. *)

(** ** 相等低于载体

    范畴、态射数据与生成元索引大于值载体；第一配置的相等低于载体，第二配置
    高于载体。不假定覆盖选择相干或保相等。 *)

Section LowerEquality.
Universes l u p r s.
Constraint l < u, u < p, p < r, r < s.
Context {C : Cat@{r r s _ _}}
    {Q : Fct (C^op) SetCat@{p u _ _ _ _ _}}
    {P : Fct (C^op) SetCat@{p u _ _ _ _ _}}
    {I : Type@{r}} {D : I → @Ob C} (e : ∀ i, Q (D i))
    (cover cover' : is_presheaf_cover e)
    (a b : ∀ i, P (D i))
    (H : presheaf_values_compatible e a)
    (K : presheaf_values_compatible e b).

(** The actual map keeps value carrier and equality bounds independent. *)

(** 实际映射保持值载体与相等界独立。 *)

Definition lower_equality_descent
  : Q ⇒ P
  := PresheafDescendN e cover a H.

(** Any supplied factor may compute the value. *)

(** 任意给定因子都可用于计算。 *)

Definition lower_equality_factor X (x : Q X) i (h : (@Hom C) X (D i))
    (E : fmap Q h (e i) ≈S x)
  : lower_equality_descent X x ≈S fmap P h (a i)
  := presheaf_descend_factor e cover a H X x i h E.

(** Generator recovery uses no native equality. *)

(** 生成元恢复不使用原生相等。 *)

Definition lower_equality_β i
  : lower_equality_descent (D i) (e i) ≈S a i
  := presheaf_descend_β e cover a H i.

(** Naturality supplies the compatibility of extracted values. *)

(** 自然性提供提取值的相容条件。 *)

Definition lower_equality_η (α : Q ⇒ P)
  : PresheafDescendN e cover (λ i, α (D i) (e i))
      (presheaf_map_values_compatible e α) ≈N α
  := presheaf_descend_η e cover α.

(** The unique extension is compared by specified natural equality. *)

(** 唯一延拓按指定自然相等比较。 *)

Definition lower_equality_universal
  : is_unique (R := @NatEq _ _ _ _)
      (λ α : Q ⇒ P, ∀ i, α (D i) (e i) ≈S a i) lower_equality_descent
  := presheaf_descend_universal e cover a H.

(** Generator equality detects map equality at these independent sizes. *)

(** 在这些独立大小下，生成元相等仍判定映射相等。 *)

Definition lower_equality_map_eq (α β : Q ⇒ P)
  : α ≈N β ↔ ∀ i, α (D i) (e i) ≈S β (D i) (e i)
  := presheaf_cover_map_eq e cover α β.

(** Different cover and overlap witnesses are permitted. *)

(** 允许覆盖及交叠见证不同。 *)

Definition lower_equality_independent (E : ∀ i, a i ≈S b i)
  : lower_equality_descent ≈N PresheafDescendN e cover' b K
  := presheaf_descend_proper e cover cover' a b H K E.

(** The existing subset and indexed-product equalities ignore proof data. *)

(** 既有子集及指标积的相等忽略证明数据。 *)

Definition lower_equality_resp
  : SubsetS (PiS I (λ i, P (D i))) (presheaf_values_compatible e) →r
      Nat_SetS Q P
  := presheaf_descend_resp e cover.

End LowerEquality.

(** ** Equality Above the Carrier

    The category, hom data and generator index are larger than the value
    carriers. Equality lies below the carrier in the first profile and
    above it in the second. No coherent or respectful cover is assumed. *)

(** ** 相等高于载体

    范畴、态射数据与生成元索引大于值载体；第一配置的相等低于载体，第二配置
    高于载体。不假定覆盖选择相干或保相等。 *)

Section HigherEquality.
Universes l u p r s.
Constraint l < u, u < p, p < r, r < s.
Context {C : Cat@{r s r _ _}}
    {Q : Fct (C^op) SetCat@{u p _ _ _ _ _}}
    {P : Fct (C^op) SetCat@{u p _ _ _ _ _}}
    {I : Type@{r}} {D : I → @Ob C} (e : ∀ i, Q (D i))
    (cover cover' : is_presheaf_cover e)
    (a b : ∀ i, P (D i))
    (H : presheaf_values_compatible e a)
    (K : presheaf_values_compatible e b).

(** The actual map keeps value carrier and equality bounds independent. *)

(** 实际映射保持值载体与相等界独立。 *)

Definition higher_equality_descent
  : Q ⇒ P
  := PresheafDescendN e cover a H.

(** Any supplied factor may compute the value. *)

(** 任意给定因子都可用于计算。 *)

Definition higher_equality_factor X (x : Q X) i (h : (@Hom C) X (D i))
    (E : fmap Q h (e i) ≈S x)
  : higher_equality_descent X x ≈S fmap P h (a i)
  := presheaf_descend_factor e cover a H X x i h E.

(** Generator recovery uses no native equality. *)

(** 生成元恢复不使用原生相等。 *)

Definition higher_equality_β i
  : higher_equality_descent (D i) (e i) ≈S a i
  := presheaf_descend_β e cover a H i.

(** Naturality supplies the compatibility of extracted values. *)

(** 自然性提供提取值的相容条件。 *)

Definition higher_equality_η (α : Q ⇒ P)
  : PresheafDescendN e cover (λ i, α (D i) (e i))
      (presheaf_map_values_compatible e α) ≈N α
  := presheaf_descend_η e cover α.

(** The unique extension is compared by specified natural equality. *)

(** 唯一延拓按指定自然相等比较。 *)

Definition higher_equality_universal
  : is_unique (R := @NatEq _ _ _ _)
      (λ α : Q ⇒ P, ∀ i, α (D i) (e i) ≈S a i) higher_equality_descent
  := presheaf_descend_universal e cover a H.

(** Generator equality detects map equality at these independent sizes. *)

(** 在这些独立大小下，生成元相等仍判定映射相等。 *)

Definition higher_equality_map_eq (α β : Q ⇒ P)
  : α ≈N β ↔ ∀ i, α (D i) (e i) ≈S β (D i) (e i)
  := presheaf_cover_map_eq e cover α β.

(** Different cover and overlap witnesses are permitted. *)

(** 允许覆盖及交叠见证不同。 *)

Definition higher_equality_independent (E : ∀ i, a i ≈S b i)
  : higher_equality_descent ≈N PresheafDescendN e cover' b K
  := presheaf_descend_proper e cover cover' a b H K E.

(** The existing subset and indexed-product equalities ignore proof data. *)

(** 既有子集及指标积的相等忽略证明数据。 *)

Definition higher_equality_resp
  : SubsetS (PiS I (λ i, P (D i))) (presheaf_values_compatible e) →r
      Nat_SetS Q P
  := presheaf_descend_resp e cover.

End HigherEquality.

(** ** The Existing Sieve Client

    Membership and indices fit in the common large value carrier. Its
    equality bound remains smaller and independent. *)

(** ** 既有筛客户端

    隶属及索引进入共同的较大值载体，相等界仍独立且更小。 *)

Section SieveClient.
Universes l u p r s.
Constraint l < u, u < p, p < r, r < s.
Context {C : Cat@{r p u _ _}} {A : @Ob C}
    {I : Type@{r}} {D : I → @Ob C} (g : ∀ i, Hom (D i) A)
    (P : Fct (C^op) SetCat@{s u _ _ _ _ _}).

(** The old interface still constructs a map with a large source. *)

(** 旧接口仍可构造来源较大的映射。 *)

Definition strict_sieve_descent (a : SieveMatching g P)
  : (SievePsh (GeneratedSieve D g) :
      Fct (C^op) SetCat@{s u _ _ _ _ _}) ⇒ P
  := SieveMatchingN g P a.

(** Retain the pre-refactor component expression, including Program's
    treatment of a dependent membership match. This compares computations,
    not respectfulness or naturality proof records. *)

(** 保留重构前的分量表达式，包括 Program 对依赖隶属匹配的处理；此处比较
    计算，不比较保相等或自然性证明记录。 *)

Program Definition original_sieve_evaluation (a : SieveMatching g P)
    X (x : (SievePsh (GeneratedSieve D g) :
      Fct (C^op) SetCat@{s u _ _ _ _ _}) X)
  : P X
  := match (lower x).2 with
      | (i; (h; _)) => fmap P h (a i)
      end.

(** The original computation converts even at an opaque input element. *)

(** 即使输入元素不透明，原计算仍定义转换相同。 *)

Definition sieve_evaluation_unchanged (a : SieveMatching g P)
    X (x : (SievePsh (GeneratedSieve D g) :
      Fct (C^op) SetCat@{s u _ _ _ _ _}) X)
  : strict_sieve_descent a X x = original_sieve_evaluation a X x
  := eq_refl.

End SieveClient.

(** ** Distinct Native Sizes by Explicit Inclusion

    Source and target have different native carrier/equality bounds.
    Their natural transformation uses ordinary independent upward lifts
    into a common SetCat, without equating either pair of native bounds. *)

(** ** 显式嵌入不同原生大小

    来源与目标具有不同的原生载体及相等界。自然变换分别向上提升到共同
    SetCat，不合并两端的任何原生界。 *)

Section NativeSizes.
Universes l u p r s.
Constraint l < u, u < p, p < r, r < s.
Context {C : Cat} {I : Type} {D : I → @Ob C}
    (Q : Fct (C^op) SetCat@{u l _ _ _ _ _})
    (P : Fct (C^op) SetCat@{l p _ _ _ _ _})
    (e : ∀ i, Q (D i)) (a : ∀ i, P (D i)).
Let Q'
  : Fct (C^op) SetCat@{r s _ _ _ _ _}
  := LiftF ∘F Q.
Let P'
  : Fct (C^op) SetCat@{r s _ _ _ _ _}
  := LiftF ∘F P.
Let e' (i : I)
  : Q' (D i)
  :=
  {|lower := e i|}.
Let a' (i : I)
  : P' (D i)
  :=
  {|lower := a i|}.
Context (cover : is_presheaf_cover e')
    (H : presheaf_values_compatible e' a').

(** No relation between native source/target bounds is inferred. *)

(** 不推出原生来源与目标界之间的关系。 *)

Definition native_lifted_descent
  : Q' ⇒ P'
  := PresheafDescendN e' cover a' H.

(** Generator recovery remains at the target's native equality. *)

(** 生成元恢复仍在目标的原生相等中成立。 *)

Definition native_lifted_β i
  : lower (native_lifted_descent (D i) (e' i)) ≈S a i
  := lower (presheaf_descend_β e' cover a' H i).

End NativeSizes.
