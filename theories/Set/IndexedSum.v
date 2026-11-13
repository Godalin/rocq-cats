From Cats.Set Require Export
  Generated.

(** * Indexed Disjoint Sums *)

(** * 指标不交和 *)

(** Generate fiber equality within a fixed index. Taking its equivalence
    closure avoids comparing dependent equality witnesses or assuming UIP. *)

(** 在固定索引内生成纤维相等；取其等价闭包，避免比较依赖相等见证或假设 UIP。 *)

Inductive IndexedSumRel {I : Type} (D : I → SetC)
  : crelation (∃ i, D i)
  :=| indexed_sum_rel (i : I) {x y : D i}
        : x ≈S y → IndexedSumRel D (i; x) (i; y).

Arguments indexed_sum_rel {_ _} _ {_ _} _.

(** The carrier is a dependent sum of representatives. Generated equality
    retains index, carrier and fiber-relation data in its inferred universe. *)

(** 载体为代表的依赖和；生成相等在推导出的宇宙中保留索引、载体及纤维关系数据。 *)

Definition IndexedSumS {I : Type} (D : I → SetC)
  : SetC
  := GeneratedS (∃ i, D i) (IndexedSumRel D).

Notation "'∐S[' D ']'" := (IndexedSumS D) : set_scope.

(** Inject a fiber without changing its representative. *)

(** 注入纤维而不改变代表。 *)

Program Definition indexed_sum_inj_resp {I : Type} (D : I → SetC) (i : I)
  : D i →r ∐S[D]
  :=
  {|func x := (i; x)
  |}.
Next Obligation.
  intros x y H. exact (closure_step (indexed_sum_rel i H)).
Defined.

(** A family of maps descends through generated equality by the shared
    generator-preservation theorem. *)

(** 映射族通过共用生成元保持定理沿生成相等下降。 *)

Program Definition indexed_sum_case_resp {I : Type} {D : I → SetC}
    {X : SetC} (κ : ∀ i, D i →r X)
  : ∐S[D] →r X
  := generated_resp (λ a, κ a.1 a.2) _.
Next Obligation.
  destruct X0. apply func_proper. assumption.
Defined.
