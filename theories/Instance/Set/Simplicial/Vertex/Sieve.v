From Cats Require Export
  Instance.Set.Simplicial.Vertex.Edge
  Instance.Set.Sieve.Core.
From Cats Require Import
  Cat.Core
  Cat.Diagram.Core.

Local Open Scope nat_scope.

(** * Descent of Vertex Nerves along Sieves

    A sieve containing all vertices, edges and triangles determines a
    unique simplex of a vertex nerve. Triangles supply composition, without
    requiring invertible arrows. Membership and equality witnesses remain
    computational and may have different universe sizes. *)

(** * 顶点 nerve 沿筛的下降

    包含全部顶点、边与三角形的筛唯一确定顶点 nerve 的单形。三角形提供复合律，
    无需箭头可逆。隶属及相等见证保留计算行为，并允许不同的宇宙大小。 *)

Section SieveValues.
Universes u p.
Context {X : SetC} {C : Cat} (T : Functor (EqGpd X) C)
    {n : nat} (R : Sieve Δ n)
    (b : SievePsh R ⇒ (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _})).

(** Evaluate a sieve map with an explicit membership witness. *)

(** 使用显式隶属见证对筛映射求值。 *)

Definition vertex_sieve_value {m : nat} (f : (@Hom Δ) m n)
    (H : f ∈Sv R)
  : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) m
  := b m {|lower := (f; H)
          |}.

(** Naturality compares equal factorizations, independently of membership
    witnesses. *)

(** 自然性比较相等的分解，并且不依赖隶属见证。 *)

Lemma vertex_sieve_value_restrict {m k : nat}
    (f : (@Hom Δ) m n) (H : f ∈Sv R)
    (θ : (@Hom Δ) k m) (g : (@Hom Δ) k n) (K : g ∈Sv R)
    (E : f ∘ θ ≈ g)
  : Nᵥ(T)[θ]Δ (vertex_sieve_value f H) ≈S vertex_sieve_value g K.
Proof.
  transitivity (b k (fmap (SievePsh R) θ {|lower := (f; H)
                                        |})).
  - symmetry. apply (nt_naturality b θ).
  - apply func_proper. exact {|lower := E
                             |}.
Defined.

Context (V : ∀ f : (@Hom Δ) 0 n, f ∈Sv R).

(** Use the value at a constant vertex as the global label. *)

(** 使用常值顶点处的值作为全局标签。 *)

Definition vertex_sieve_label (i : Ordinal n)
  : X
  := lower (vertex_sieve_value
      (ConstF [Ord 0] (C := [Ord n]) i) (V _)) fin_first.

(** Every local occurrence agrees with the chosen global label. *)

(** 每个局部出现均与选定的全局标签相等。 *)

Definition vertex_sieve_label_value {m : nat}
    (f : (@Hom Δ) m n) (H : f ∈Sv R) (i : Ordinal m)
  : vertex_sieve_label (f i) ≈S lower (vertex_sieve_value f H) i.
Proof.
  symmetry. apply (fst (vertex_nerve_zero_eq_iff
    (Nᵥ(T)[ConstF [Ord 0] (C := [Ord m]) i]Δ (vertex_sieve_value f H))
    (vertex_sieve_value (ConstF [Ord 0] (C := [Ord n]) (f i)) (V _)))).
  apply (vertex_sieve_value_restrict f H
    (ConstF [Ord 0] (C := [Ord m]) i)).
  apply (snd (simplex_eq_iff _ _)). intros [[] | []]. reflexivity.
Defined.

Context (E : ∀ f : (@Hom Δ) 1 n, f ∈Sv R).

(** Read an edge, then align its endpoints with the global labels. *)

(** 读取一条边，再将其端点调整到全局标签。 *)

Definition vertex_sieve_arrow (i j : Ordinal n)
    (h : (@Hom [Ord n]) i j)
  : (@Hom (VertexCat T)) (vertex_sieve_label i) (vertex_sieve_label j)
  := let f := ⟦ArrowChain h⟧Ch in
    T⟦vertex_sieve_label_value f (E f) fin_first;
      fmap (lower (vertex_sieve_value f (E f))) (ordinal_step fin_first);
      vertex_sieve_label_value f (E f) (fin_next fin_first)⟧Ar.

(** Any local simplex computes the same global arrow. The global order
    witness is arbitrary; no equality of witnesses is required. *)

(** 任意局部单形都计算出相同的全局箭头。全局顺序见证任意，无需见证相等。 *)

Lemma vertex_sieve_arrow_value {m : nat}
    (f : (@Hom Δ) m n) (H : f ∈Sv R)
    (i j : Ordinal m) (h : (@Hom [Ord m]) i j)
    (g : (@Hom [Ord n]) (f i) (f j))
  : vertex_sieve_arrow (f i) (f j) g ≈
      T⟦vertex_sieve_label_value f H i;
        fmap (lower (vertex_sieve_value f H)) h;
        vertex_sieve_label_value f H j⟧Ar.
Proof.
  pose (Q := ⟦ArrowChain h⟧Ch).
  pose (P := ⟦ArrowChain g⟧Ch).
  assert (K : f ∘ Q ≈ P).
  { apply (snd (simplex_eq_iff _ _)).
    intros [[] | [[] | []]]; reflexivity. }
  pose (L := symmetry (vertex_sieve_value_restrict f H Q P (E P) K)).
  destruct L as [[e L]]. unfold vertex_sieve_arrow.
  transitivity (T⟦vertex_sieve_label_value f H i;
      fmap (lower (vertex_sieve_value f H)) (fmap Q (ordinal_step fin_first));
      vertex_sieve_label_value f H j⟧Ar).
  - exact (vertex_rebase_eq T _ _ _ _ (e fin_first)
      (e (fin_next fin_first)) _ _ (L _ _ (ordinal_step fin_first))).
  - apply func_proper. apply functor_fmap_proper. exact tt.
Defined.

(** Parallel order witnesses give equal arrows. *)

(** 平行顺序见证给出相等的箭头。 *)

Lemma vertex_sieve_arrow_proper (i j : Ordinal n)
    (g h : (@Hom [Ord n]) i j)
  : vertex_sieve_arrow i j g ≈ vertex_sieve_arrow i j h.
Proof.
  pose (f := ⟦ArrowChain g⟧Ch).
  transitivity (T⟦vertex_sieve_label_value f (E f) fin_first;
      fmap (lower (vertex_sieve_value f (E f))) (ordinal_step fin_first);
      vertex_sieve_label_value f (E f) (fin_next fin_first)⟧Ar).
  - exact (vertex_sieve_arrow_value f (E f) fin_first
      (fin_next fin_first) (ordinal_step fin_first) g).
  - symmetry. exact (vertex_sieve_arrow_value f (E f) fin_first
      (fin_next fin_first) (ordinal_step fin_first) h).
Defined.

(** Degenerate edges give the identity law. *)

(** 退化边给出恒等律。 *)

Lemma vertex_sieve_arrow_id (i : Ordinal n)
  : vertex_sieve_arrow i i id ≈ id.
Proof.
  pose (f := ConstF [Ord 0] (C := [Ord n]) i).
  etransitivity.
  - exact (vertex_sieve_arrow_value f (V f) fin_first fin_first
      (@Cats.Cat.Core.id [Ord 0] fin_first) (@Cats.Cat.Core.id [Ord n] i)).
  - change (T⟦symmetry (vertex_sieve_label_value f (V f) fin_first)⟧Ob ∘
      fmap (lower (vertex_sieve_value f (V f))) id ∘
        T⟦vertex_sieve_label_value f (V f) fin_first⟧Ob ≈ id).
    rewrite functor_id, comp_id_r. apply vertex_transport_inv.
Defined.

(** Vertices and edges alone reflect simplex equality. This does not
    require triangles or existence of extensions. *)

(** 仅顶点和边就可反映单形相等，无需三角形或延拓的存在性。 *)

Definition vertex_sieve_reflects
    (x y : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) n)
    (H : x↾Sv[Nᵥ(T); R] ≈N y↾Sv[Nᵥ(T); R])
  : x ≈S y.
Proof.
  pose (e := λ i : Ordinal n,
    (lower (H 0 {|lower := (ConstF [Ord 0] (C := [Ord n]) i; V _)
                 |})).1 fin_first).
  refine {|lower := (e; _)
          |}.
  intros i j h. pose (Q := ⟦ArrowChain h⟧Ch).
  destruct (lower (H 1 {|lower := (Q; E Q)
                       |})) as [d L].
  pose proof (L _ _ (ordinal_step fin_first)) as K.
  change (T⟦d (fin_next fin_first)⟧Ob ∘
      fmap (lower x) (fmap Q (ordinal_step fin_first)) ≈
    fmap (lower y) (fmap Q (ordinal_step fin_first)) ∘ T⟦d fin_first⟧Ob) in K.
  rewrite (vertex_transport_witness_independent T (e j) (d (fin_next fin_first))),
    (vertex_transport_witness_independent T (e i) (d fin_first)).
  transitivity (T⟦d (fin_next fin_first)⟧Ob ∘
    fmap (lower x) (fmap Q (ordinal_step fin_first))).
  - apply comp_proper; [reflexivity |].
    apply functor_fmap_proper. exact tt.
  - transitivity (fmap (lower y) (fmap Q (ordinal_step fin_first)) ∘
      T⟦d fin_first⟧Ob).
    + exact K.
    + apply comp_proper; [| reflexivity].
      apply functor_fmap_proper. exact tt.
Defined.

Context (D : ∀ f : (@Hom Δ) 2 n, f ∈Sv R).

(** A triangle's functor law gives composition of the reconstructed edges. *)

(** 三角形的函子律给出重构边的复合律。 *)

Lemma vertex_sieve_arrow_comp (i j k : Ordinal n)
    (g : (@Hom [Ord n]) j k) (h : (@Hom [Ord n]) i j)
  : vertex_sieve_arrow i k (g ∘ h) ≈
      vertex_sieve_arrow j k g ∘ vertex_sieve_arrow i j h.
Proof.
  pose (f := ⟦⟨h, g⟩Ch⟧Ch).
  pose (a := ordinal_step (n := 2) fin_first).
  pose (c := ordinal_step (n := 2) (fin_next fin_first)).
  etransitivity.
  - exact (vertex_sieve_arrow_value f (D f) _ _ (c ∘ a) (g ∘ h)).
  - transitivity (T⟦vertex_sieve_label_value f (D f) fin_first;
      fmap (lower (vertex_sieve_value f (D f))) c ∘
        fmap (lower (vertex_sieve_value f (D f))) a;
      vertex_sieve_label_value f (D f) (fin_next (fin_next fin_first))⟧Ar).
    + apply func_proper. apply functor_comp.
    + etransitivity; [apply vertex_rebase_comp |].
      apply comp_proper; symmetry.
      * exact (vertex_sieve_arrow_value f (D f) _ _ c g).
      * exact (vertex_sieve_arrow_value f (D f) _ _ a h).
Defined.

(** Reconstruct the ordinal diagram using the sieve's two-dimensional data. *)

(** 使用筛的二维数据重构序数图式。 *)

Program Definition VertexSieveF
  : Functor [Ord n] (VertexCat T)
  :=
  {|F0 := vertex_sieve_label
  ; F1 i j h := vertex_sieve_arrow i j h
  |}.
Next Obligation.
  intros f g H. exact (vertex_sieve_arrow_proper X0 Y f g).
Defined.
Next Obligation. exact (vertex_sieve_arrow_id X0). Defined.
Next Obligation. exact (vertex_sieve_arrow_comp X0 Y Z f g). Defined.

(** The reconstructed simplex restricts to the entire given sieve map. *)

(** 重构单形限制为整个给定的筛映射。 *)

Lemma vertex_sieve_filler
  : ⟨VertexSieveF⟩ᵥ↾Sv[Nᵥ(T); R] ≈N b.
Proof.
  intros m [[f H]]. refine {|lower := _
                          |}.
  exists (vertex_sieve_label_value f H). intros i j h.
  change (T⟦vertex_sieve_label_value f H j⟧Ob ∘
      vertex_sieve_arrow (f i) (f j) (fmap f h) ≈
    fmap (lower (vertex_sieve_value f H)) h ∘
      T⟦vertex_sieve_label_value f H i⟧Ob).
  rewrite (vertex_sieve_arrow_value f H i j h (fmap f h)).
  apply vertex_rebase_square.
Defined.

(** A sieve containing the two-dimensional skeleton has a unique
    extension, using specified simplex equality and transparent witnesses. *)

(** 包含二维骨架的筛具有唯一延拓，使用指定单形相等并保留透明见证。 *)

Definition vertex_sieve_universal
  : ∃ x : (Nᵥ(T) : Functor (Δ^op) SetCat@{u p _ _ _ _ _}) n,
      is_unique (R := carrier_equiv ((Nᵥ(T) :
        Functor (Δ^op) SetCat@{u p _ _ _ _ _}) n))
        (λ x, x↾Sv[Nᵥ(T); R] ≈N b) x.
Proof.
  exists ⟨VertexSieveF⟩ᵥ. refine
    {|this := _
    ; that := _
    |}.
  - exact vertex_sieve_filler.
  - intros y Hy. apply (vertex_sieve_reflects y ⟨VertexSieveF⟩ᵥ).
    transitivity b; [exact Hy | symmetry; exact vertex_sieve_filler].
Defined.

End SieveValues.
