From Cats Require Export
  Algebra.Monoid.Diagram
  Instance.Set.Simplicial.Operators.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Lift
  Instance.Set.Simplicial.Nerve.

Local Open Scope nat_scope.
Local Open Scope monoid_scope.

(** * The Arrow-Chain Nerve of a Monoid

    The n-simplices are n-tuples with pointwise specified equality. A simplex
    operator substitutes its finite vertex map and composes each image
    segment. All six simplicial identities follow from functoriality. *)

(** * 幺半群的箭头链 nerve

    n-单形是带逐项指定相等的 n 元组。单纯算子通过其有限顶点映射替换，并复合
    各像段中的箭头；六类单纯恒等式全部由函子性导出。 *)

Program Definition MonoidNerve@{u p +} (M : SetC@{u p})
    `{HM : !Monoid M}
  : Functor (Δ^op) SetCat@{u p _ _ _ _ _}
  :=
  {|F0 n := M ^S n
  ; F1 n m θ :=
      {|func xs := xs[θ]M
      ; func_proper := monoid_chain_sub_proper θ
      |}
  |}.
Next Obligation.
  intros θ φ H xs. apply monoid_chain_sub_map.
  exact (fst (simplex_eq_iff θ φ) H).
Defined.
Next Obligation. intros xs. apply monoid_chain_sub_id. Defined.
Next Obligation.
  intros xs. symmetry. apply monoid_chain_sub_comp;
    apply ordinal_functor_monotone.
Defined.

Notation "'Nₘ(' M ')'" := (MonoidNerve M) : ob_scope.

(** Restriction multiplies the original segments between image endpoints. *)

(** 限制对原箭头链中像端点之间的各段取积。 *)

Lemma monoid_nerve_restrict@{u p +}
    {M : SetC@{u p}} `{HM : !Monoid M}
    {m n : nat} (θ : (@Hom Δ) m n) (xs : Nₘ(M) n)
    (i : Fin@{Set} m)
  : Nₘ(M)[θ]Δ xs i ≈S xs⟦θ (fin_weaken i), θ (fin_next i)⟧⋅.
Proof. reflexivity. Defined.

(** Every two zero-simplices are equal by their empty domain. *)

(** 零维单形因定义域为空而全部相等。 *)

Lemma monoid_nerve_zero_unique@{u p +}
    {M : SetC@{u p}} `{HM : !Monoid M}
    (x y : Nₘ(M) 0)
  : x ≈S y.
Proof. intros i. destruct i. Defined.

(** One-simplices compare exactly by their original entry, preserving the
    monoid's specified distinctions between loops. *)

(** 一维单形恰按原分量比较，因此保留幺半群指定相等对环路的区别。 *)

Lemma monoid_nerve_one_eq_iff@{u p +}
    {M : SetC@{u p}} `{HM : !Monoid M}
    (xs ys : Nₘ(M) 1%nat)
  : xs ≈S ys ↔ xs fin_first ≈S ys fin_first.
Proof.
  split.
  - intros H. exact (H fin_first).
  - intros H [[] | []]. exact H.
Defined.

(** The first face removes the first arrow. Other faces compose image
    segments by the same restriction formula. *)

(** 首面删除首箭头；其他面按同一个限制公式复合像段。 *)

Lemma monoid_nerve_face_first@{u p +}
    {M : SetC@{u p}} `{HM : !Monoid M}
    {n : nat} (xs : Nₘ(M) (S n))
  : d[Nₘ(M); n; fin_first] xs ≈S tuple_tail xs.
Proof.
  intros i. change (monoid_segment (tuple_tail xs)
    (fin_weaken i) (fin_next i) ≈S tuple_tail xs i).
  apply monoid_segment_step.
Defined.

(** The middle face of a pair composes the later arrow on the left. *)

(** 二元组的中间面复合两个箭头，后走的箭头乘在左侧。 *)

Lemma monoid_nerve_face_middle@{u p +}
    {M : SetC@{u p}} `{HM : !Monoid M} (a b : M)
  : d[Nₘ(M); 1%nat; fin_next fin_first] (a ∷S b ∷S []S) ≈S
      ((b ⋅ a) ∷S []S).
Proof.
  intros [[] | []]. change ((1 ⋅ b) ⋅ a ≈S b ⋅ a).
  rewrite monoid_unit_l. reflexivity.
Defined.

(** The last face of a pair removes its second arrow. *)

(** 二元组的末面删除第二个箭头。 *)

Lemma monoid_nerve_face_last_pair@{u p +}
    {M : SetC@{u p}} `{HM : !Monoid M} (a b : M)
  : d[Nₘ(M); 1%nat; fin_next (fin_next fin_first)] (a ∷S b ∷S []S) ≈S
      (a ∷S []S).
Proof. intros [[] | []]. change (1 ⋅ a ≈S a). apply monoid_unit_l. Defined.

(** Degenerating the empty chain gives the identity arrow. *)

(** 退化空链得到恒等箭头。 *)

Lemma monoid_nerve_degeneracy_zero@{u p +}
    {M : SetC@{u p}} `{HM : !Monoid M}
  : s[Nₘ(M); 0; fin_first] []S ≈S ((1 : M) ∷S []S).
Proof. intros [[] | []]. reflexivity. Defined.

(** Repeating the source vertex inserts a unit before a single arrow. *)

(** 重复源顶点，在单箭头前插入单位元。 *)

Lemma monoid_nerve_degeneracy_first@{u p +}
    {M : SetC@{u p}} `{HM : !Monoid M} (a : M)
  : s[Nₘ(M); 1%nat; fin_first] (a ∷S []S) ≈S (1 ∷S a ∷S []S).
Proof.
  intros [[] | [[] | []]]; [reflexivity |].
  change (1 ⋅ a ≈S a). apply monoid_unit_l.
Defined.

(** Repeating the target vertex inserts a unit after a single arrow. *)

(** 重复目标顶点，在单箭头后插入单位元。 *)

Lemma monoid_nerve_degeneracy_last@{u p +}
    {M : SetC@{u p}} `{HM : !Monoid M} (a : M)
  : s[Nₘ(M); 1%nat; fin_next fin_first] (a ∷S []S) ≈S (a ∷S 1 ∷S []S).
Proof.
  intros [[] | [[] | []]]; [|reflexivity].
  change (1 ⋅ a ≈S a). apply monoid_unit_l.
Defined.

(** * Comparison with the Diagram Nerve

    Diagram values can be larger than the native chain setoids. Raise the
    source explicitly; its own carrier and equality levels stay independent. *)

(** * 与图式 nerve 的比较

    图式值可以大于原生箭头链广集；显式提升源，保持其自身载体与相等层级独立。 *)

Program Definition MonoidDiagramN@{u p v q +} {M : SetC@{v q}}
    `{HM : !Monoid M}
  : (LiftF ∘F Nₘ(M) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) ⇒
      N≅(B(M))
  :=
  {|nt n :=
      {|func xs := ⟨MonoidChainF (lower xs)⟩N
      |}
  |}.
Next Obligation.
  intros [xs] [ys] [H]. refine {|lower := _
                              |}. apply MonoidChainF_proper. exact H.
Defined.
Next Obligation.
  intros [xs]. exact {|lower := monoid_chain_sub_iso f xs
                      |}.
Defined.
