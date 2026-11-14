From Cats Require Export
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core
  Instance.Set.Yoneda.
From Cats.Set Require Import
  Pi
  Subset.

(** * Descent Along Representable Generators

    A presheaf need not be a subpresheaf of one representable. It is enough
    that each element has a supplied restriction from some generator.
    Compatible values on those generators extend uniquely to the presheaf.
    This is the common argument behind generated-sieve matching and the
    future gluing of the product cylinder covered by its staircases.

    A cover supplies computational factorizations, not a choice axiom.
    They need not be unique, respectful, or commute with restriction:
    compatibility compares their values whenever their images agree.
    Natural transformations have a common codomain [SetCat]; presheaves
    of different native sizes may first be raised by [LiftF]. This uses
    ordinary size inclusion, not resizing. *)

(** * 沿可表生成元下降

    预层不必是单个可表预层的子预层；只需每个元素都给定为某个生成元的限制。
    生成元上的相容值由此唯一延拓到整个预层。这是生成筛匹配与后续阶梯覆盖
    积柱粘合的共同论证。

    覆盖提供可计算分解，不是选择公理。分解无需唯一、保相等或与限制交换：
    只要像相等，相容条件就比较其值。
    自然变换共用目标范畴 [SetCat]；原生大小不同的预层可先由 [LiftF] 提升，
    使用通常大小嵌入，不使用大小重设。 *)

(** Under Yoneda, [e i] and [a i] denote maps from the representable
    [h(D i)]. The dashed map is constructed below. All triangles commute
    in specified natural equality, after any required common size
    inclusions; factorization witnesses are not equated.
    The existing
    %\coqref{Cats.Instance.Set.Sieve.Matching.SieveMatchingN}
    {%[SieveMatchingN]%}% now specializes this construction. *)

(** 按 Yoneda，[e i] 与 [a i] 表示从可表预层 [h(D i)] 出发的映射。下文构造
    虚线映射；按需先嵌入共同大小后，三角形按指定自然相等交换，不比较分解
    见证。现有
    %\coqref{Cats.Instance.Set.Sieve.Matching.SieveMatchingN}
    {%[SieveMatchingN]%}% 将复用此构造。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
h(D_i) \arrow[r,"{e_i}"] \arrow[dr,"{a_i}"']
  & Q \arrow[d,dashed,"{\alpha}"]
  & h(D_j) \arrow[l,"{e_j}"'] \arrow[dl,"{a_j}"] \\
  & P &
\end{tikzcd}
\end{center}%
*)

(** ** Covers and Compatible Values

    Fix a category, source and target presheaves at common ambient value
    bounds, and a family of generating elements. Cover witnesses and
    compatibility witnesses remain independent Type-valued data. *)

(** ** 覆盖与相容值

    固定范畴、处于共同环境取值界的来源及目标预层，以及生成元素族。载体与
    相等层级独立，覆盖与相容见证保留为 Type 值数据。 *)

Section PresheafDescent.
Universes u p.
Context {C : Cat}
    {Q : Fct (C^op) SetCat@{u p _ _ _ _ _}}
    {I : Type} {D : I → @Ob C} (e : ∀ i, Q (D i)).

(** Every source element has a retained generator and restriction arrow.
    The last equation uses the source's specified equality. *)

(** 每个来源元素保留一个生成元与限制箭头；末方程使用来源的指定相等。 *)

Definition is_presheaf_cover
  : Type
  := ∀ (X : @Ob C) (x : Q X), ∃ i, ∃ h : (@Hom C) X (D i), fmap Q h (e i) ≈S x.

Context {P : Fct (C^op) SetCat@{u p _ _ _ _ _}}.

(** Values agree on every pair of restrictions with equal source images.
    This includes different arrows and different generator indices. *)

(** 值在来源像相等的每对限制上相等，包括不同箭头及不同生成元索引。 *)

Definition presheaf_values_compatible (a : ∀ i, P (D i))
  : Type
  := ∀ X i j (f : (@Hom C) X (D i)) (h : (@Hom C) X (D j)),
      fmap Q f (e i) ≈S fmap Q h (e j) →
      fmap P f (a i) ≈S fmap P h (a j).

(** Naturality supplies compatibility for the values of an existing map. *)

(** 自然性使已有映射在生成元上的值满足相容条件。 *)

Lemma presheaf_map_values_compatible (α : Q ⇒ P)
  : presheaf_values_compatible (λ i, α (D i) (e i)).
Proof.
  intros X i j f h E.
  transitivity (α X (fmap Q f (e i))).
  - symmetry. exact (nt_naturality α f (e i)).
  - transitivity (α X (fmap Q h (e j))).
    + apply func_proper. exact E.
    + exact (nt_naturality α h (e j)).
Defined.

(** A cover detects equality of maps just on its generators. *)

(** 覆盖只凭生成元处的值即可判定映射相等。 *)

Definition presheaf_cover_map_eq (cover : is_presheaf_cover)
    (α β : Q ⇒ P)
  : α ≈N β ↔ ∀ i, α (D i) (e i) ≈S β (D i) (e i).
Proof.
  split.
  - intros H i. apply H.
  - intros H X x. destruct (cover X x) as [i [h E]].
    transitivity (α X (fmap Q h (e i))).
    + apply func_proper. symmetry. exact E.
    + transitivity (fmap P h (α (D i) (e i))).
      * exact (nt_naturality α h (e i)).
      * transitivity (fmap P h (β (D i) (e i))).
        -- apply func_proper. exact (H i).
        -- transitivity (β X (fmap Q h (e i))).
           ++ symmetry. exact (nt_naturality β h (e i)).
           ++ apply func_proper. exact E.
Defined.

(** Evaluate at the supplied factorization. Compatibility proves
    respectfulness and naturality even when the cover changes its choice. *)

(** 在给定分解处求值；即使覆盖改变所选分解，相容性仍给出保相等性与自然性。 *)

Program Definition PresheafDescendN (cover : is_presheaf_cover)
    (a : ∀ i, P (D i)) (H : presheaf_values_compatible a)
  : Q ⇒ P
  :=
  {|nt X :=
      {|func x := match cover X x with
          | (i; (h; _)) => fmap P h (a i)
          end
      |}
  |}.
Next Obligation.
  intros x y E. destruct (cover X x) as [i [h F]].
  destruct (cover X y) as [j [k G]].
  apply (H X i j h k).
  transitivity x; [exact F |].
  transitivity y; [exact E | symmetry; exact G].
Defined.
Next Obligation.
  intros x. destruct (cover X x) as [i [h E]].
  destruct (cover Y (fmap Q f x)) as [j [k F]].
  transitivity (fmap P (h ∘ f) (a i)).
  - apply (H Y j i k (h ∘ f)).
    transitivity (fmap Q f x); [exact F |].
    transitivity (fmap Q f (fmap Q h (e i))).
    + apply func_proper. symmetry. exact E.
    + symmetry. exact (functor_comp _ _ Q f h (e i)).
  - exact (functor_comp _ _ P f h (a i)).
Defined.

(** Any valid factorization computes the descended value, irrespective of
    which one the cover used. No equality of factorization witnesses occurs. *)

(** 任意有效分解都计算下降值，无论覆盖使用哪一份；不比较分解见证。 *)

Lemma presheaf_descend_factor (cover : is_presheaf_cover)
    (a : ∀ i, P (D i)) (H : presheaf_values_compatible a)
    X (x : Q X) i (h : (@Hom C) X (D i))
    (E : fmap Q h (e i) ≈S x)
  : PresheafDescendN cover a H X x ≈S fmap P h (a i).
Proof.
  cbn. destruct (cover X x) as [j [k F]].
  apply (H X j i k h). transitivity x; [exact F | symmetry; exact E].
Defined.

(** Generator evaluation recovers the prescribed value. *)

(** 在生成元处求值，恢复指定的值。 *)

Lemma presheaf_descend_β (cover : is_presheaf_cover)
    (a : ∀ i, P (D i)) (H : presheaf_values_compatible a) i
  : PresheafDescendN cover a H (D i) (e i) ≈S a i.
Proof.
  transitivity (fmap P (@Cat.Core.id C (D i)) (a i)).
  - apply presheaf_descend_factor. exact (functor_id _ _ Q (e i)).
  - exact (functor_id _ _ P (a i)).
Defined.

(** Descending the values of an existing map recovers that map. *)

(** 下降已有映射的生成元值，恢复该映射。 *)

Lemma presheaf_descend_η (cover : is_presheaf_cover) (α : Q ⇒ P)
  : PresheafDescendN cover (λ i, α (D i) (e i))
      (presheaf_map_values_compatible α) ≈N α.
Proof.
  apply (snd (presheaf_cover_map_eq cover _ _)).
  intros i. apply presheaf_descend_β.
Defined.

(** This is the full universal property: the given values have a unique
    extension, compared by natural specified equality. *)

(** 这是完整泛性质：给定值有唯一延拓，按自然的指定相等比较。 *)

Definition presheaf_descend_universal (cover : is_presheaf_cover)
    (a : ∀ i, P (D i)) (H : presheaf_values_compatible a)
  : is_unique (R := @NatEq _ _ _ _)
      (λ α : Q ⇒ P, ∀ i, α (D i) (e i) ≈S a i) (PresheafDescendN cover a H).
Proof.
  refine {|this := presheaf_descend_β cover a H
          ; that := _
          |}.
  intros α F. apply (snd (presheaf_cover_map_eq cover _ _)).
  intros i. transitivity (a i); [exact (F i) |].
  symmetry. apply presheaf_descend_β.
Defined.

(** Pointwise equal values give equal extensions under independently chosen
    covers and compatibility witnesses. Equality never compares these data. *)

(** 逐点相等的值在独立覆盖和相容见证下给出相等延拓；相等不比较这些数据。 *)

Lemma presheaf_descend_proper (cover cover' : is_presheaf_cover)
    (a b : ∀ i, P (D i)) (H : presheaf_values_compatible a)
    (K : presheaf_values_compatible b) (E : ∀ i, a i ≈S b i)
  : PresheafDescendN cover a H ≈N PresheafDescendN cover' b K.
Proof.
  apply (snd (presheaf_cover_map_eq cover _ _)).
  intros i. transitivity (a i); [apply presheaf_descend_β |].
  transitivity (b i); [exact (E i) | symmetry; apply presheaf_descend_β].
Defined.

(** Package descent as a respectful map, reusing the existing indexed
    product and retained subset. Their equality compares only the values. *)

(** 复用既有指标积与保留隶属的子集，将下降打包成保相等映射；相等只比较值。 *)

Program Definition presheaf_descend_resp (cover : is_presheaf_cover)
  : SubsetS (PiS I (λ i, P (D i))) presheaf_values_compatible →r
      Nat_SetS Q P
  :=
  {|func a := PresheafDescendN cover a.1 a.2
  |}.
Next Obligation.
  intros [a H] [b K] E. exact (presheaf_descend_proper cover cover a b H K E).
Defined.

End PresheafDescent.
