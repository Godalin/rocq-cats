From Cats.Set.Relation Require Import SumClosure.
From Cats.Instance.Relation Require Import Coproduct.
From Cats Require Import
  Cat.Core
  Cat.Coproduct.Core.

(** * Relation Sum Interface Regressions *)

(** * 关系和接口的回归检查 *)

Local Open Scope relation_scope.
Local Open Scope cat_scope.

Section IndependentSizes.
Universes a r s.
Constraint r < s.
Constraint s < a.
Context (A : Type@{a}) (R : A → A → Type@{r}) (S : A → A → Type@{s}).

(** Small and differently sized summands do not enlarge to the carrier. *)

(** 较小且大小不同的加数不必提升到载体层级。 *)

Definition small_relation_sum
  : A → A → Type@{s}
  := R ⊕R S.

End IndependentSizes.

Section IndexedSizes.
Universes i a o r.
Constraint a < o.
Constraint o < r.
Constraint i < r.
Context (I : Type@{i}) (A : I → Type@{a}).
Context (K : ContextSystem@{i a o} A).
Context (R S : RelationFamily@{i a r _} A).

(** Distribution preserves the separated levels of indexed contexts. *)

(** 分配保持带索引上下文的各分离层级。 *)

Definition separated_context_sum
  : (R ⊕ᵢ S)^C[K] ≈ᵢ (R^C[K] ⊕ᵢ S^C[K])
  := context_closure_sum K R S.

(** The categorical coproduct interface accepts these same objects. *)

(** 范畴余积接口接受这些相同对象。 *)

Definition separated_relation_coproduct
  : @is_coproduct (RelationFamilyCat A) R S (R ⊕ᵢ S)
      (family_relation_sum_inl R S) (family_relation_sum_inr R S)
  := @coproduct_universal (RelationFamilyCat A)
      (RelationFamilyCat_HasCoproduct A) R S.

End IndexedSizes.

Section Computations.

(** These two rule families carry different data, retained by coproduct
    elimination through the categorical interface. *)

(** 两个规则族携带不同数据；经范畴接口作余积消去时仍保留这些数据。 *)

Definition NumberRule (_ : unit) (_ _ : bool)
  : Type
  := nat.

Definition BooleanRule (_ : unit) (_ _ : bool)
  : Type
  := bool.

Example categorical_copair_computes
  : @copair (RelationFamilyCat (λ _ : unit, bool))
      (RelationFamilyCat_HasCoproduct (λ _ : unit, bool))
      NumberRule BooleanRule NumberRule
      (λ i x y n, S n) (λ i x y b, if b then 7 else 9)
      tt false true (inr true) = 7.
Proof. reflexivity. Qed.

(** Importing relation paths and category notation together is supported.
    Moving a tag outside a context also retains the labeled operation. *)

(** 可同时导入关系路径与范畴记法。将标签移到上下文外，也保留带标签的操作。 *)

Program Definition BooleanContexts
  : ContextSystem (λ _ : unit, bool)
  :=
  {|context_operation i j := bool → bool
  ; context_action i j f := f
  |}.

Example context_sum_tag_computes
  : fst (context_closure_sum BooleanContexts NumberRule BooleanRule
      tt true false)
      (context_lift (K := BooleanContexts) (i := tt) (j := tt) negb
        (x := false) (y := true) (context_step (inr true))) =
      inr (context_lift (K := BooleanContexts) (i := tt) (j := tt) negb
        (x := false) (y := true) (context_step true)).
Proof. reflexivity. Qed.

End Computations.
