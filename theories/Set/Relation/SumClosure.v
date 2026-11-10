From Cats.Set.Relation Require Export
  Sum
  Compatible.

(** * Context Closure and Alternative Rules *)

(** * 上下文闭包与备选规则 *)

Local Open Scope relation_scope.

(** An operation preserves a tagged alternative by preserving its chosen
    branch. Thus separately compatible rule sets can be combined. *)

(** 操作通过保持所选分支来保持带标签的备选关系，因此可组合分别相容的规则集。 *)

Definition family_relation_sum_compatible {I : Type} {A : I → Type}
    (K : ContextSystem A) {R S : RelationFamily A}
    (hr : is_compatible K R) (hs : is_compatible K S)
  : is_compatible K (R ⊕ᵢ S).
Proof.
  intros i j c x y [p | p].
  - exact (inl (hr i j c x y p)).
  - exact (inr (hs i j c x y p)).
Defined.

(** A context contains one generating edge, so its tag can be moved outside
    the context. Conversely, map each branch along its generator injection.
    This compares presentations by maps, not by equality of derivations. *)

(** 上下文包含一条生成边，因此可将其标签移到上下文外。反向则沿生成元注入
    映射各分支。这里用映射比较呈现，不比较推导的相等。 *)

Definition context_closure_sum {I : Type} {A : I → Type}
    (K : ContextSystem A) (R S : RelationFamily A)
  : (R ⊕ᵢ S)^C[K] ≈ᵢ (R^C[K] ⊕ᵢ S^C[K]).
Proof.
  apply relation_family_equiv_of_inclusions.
  - exact (context_closure_preserves K
      (family_relation_sum_compatible K
        (context_closure_compatible K R) (context_closure_compatible K S))
      (family_relation_sum_map
        (λ i x y p, context_step p) (λ i x y p, context_step p))).
  - exact (family_relation_sum_case
      (context_closure_map K (family_relation_sum_inl R S))
      (context_closure_map K (family_relation_sum_inr R S))).
Defined.
