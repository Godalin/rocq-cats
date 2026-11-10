From Cats.Set.Relation Require Export Family.

(** * Sums of Relations

    A sum records which generating relation supplied an edge, retaining
    its witness. Combining reduction rules needs this choice, not sequential
    composition of relations. On the inclusion preorder it is a least upper
    bound; mutual inclusion does not identify its tagged witnesses. *)

(** * 关系的和

    和记录一条边来自哪个生成关系，并保留其见证。组合归约规则需要这种选择，
    而不是关系的顺序复合。在包含预序中，和是最小上界；相互包含不识别带标签
    的见证。 *)

Local Open Scope relation_scope.

(** Carrier and summand witness bounds are independent. *)

(** 载体与两个加数的见证界相互独立。 *)

Definition RelationSum {A : Type} (R S : crelation A)
  : crelation A
  := λ x y, (R x y + S x y)%type.

Infix "⊕R" := RelationSum (at level 55, right associativity) : relation_scope.

(** Inject a witness of the first generating relation. *)

(** 注入第一个生成关系的见证。 *)

Definition relation_sum_inl {A : Type} (R S : crelation A)
  : R ⊆R R ⊕R S
  := λ x y p, inl p.

(** Inject a witness of the second generating relation. *)

(** 注入第二个生成关系的见证。 *)

Definition relation_sum_inr {A : Type} (R S : crelation A)
  : S ⊆R R ⊕R S
  := λ x y p, inr p.

(** Merge two inclusions into a common target by inspecting the tag. *)

(** 检查标签，将两个包含合并到共同目标。 *)

Definition relation_sum_case {A : Type} {R S T : crelation A}
    (h : R ⊆R T) (k : S ⊆R T)
  : R ⊕R S ⊆R T
  := λ x y p, match p with inl q => h x y q | inr q => k x y q end.

(** The least-upper-bound property supplies both witness transformations.
    In a thin category this is precisely the coproduct property. *)

(** 最小上界性质给出两个方向的见证转换。在薄范畴中，这恰好就是余积性质。 *)

Definition relation_sum_universal {A : Type} (R S T : crelation A)
  : R ⊕R S ⊆R T ↔ (R ⊆R T ∧ S ⊆R T)
  := ((λ h, (relation_incl_comp (relation_sum_inl R S) h,
              relation_incl_comp (relation_sum_inr R S) h)),
      (λ h, relation_sum_case (fst h) (snd h))).

(** Map each summand independently, retaining its tag. *)

(** 分别映射两个加数，保留其标签。 *)

Definition relation_sum_map {A : Type} {R S T U : crelation A}
    (h : R ⊆R T) (k : S ⊆R U)
  : R ⊕R S ⊆R T ⊕R U
  := relation_sum_case (λ x y p, inl (h x y p))
      (λ x y p, inr (k x y p)).

(** The sum respects the specified equivalence of generating relations. *)

(** 和保持生成关系的指定等价。 *)

Global Instance RelationSum_proper {A : Type}
  : Proper (relation_equivalence ==> relation_equivalence ==>
      relation_equivalence) (@RelationSum A).
Proof.
  intros R R' h S S' k. apply relation_equiv_of_inclusions.
  - exact (relation_sum_map (relation_equiv_forward h)
      (relation_equiv_forward k)).
  - exact (relation_sum_map (relation_equiv_backward h)
      (relation_equiv_backward k)).
Defined.

(** The indexed sum acts in each fiber and never changes its index. *)

(** 带索引的和作用于每个纤维，不改变索引。 *)

Definition FamilyRelationSum {I : Type} {A : I → Type}
    (R S : RelationFamily A)
  : RelationFamily A
  := λ i, R i ⊕R S i.

Infix "⊕ᵢ" := FamilyRelationSum
  (at level 55, right associativity) : relation_scope.

(** The first family injection is pointwise. *)

(** 第一个族注入逐点给出。 *)

Definition family_relation_sum_inl {I : Type} {A : I → Type}
    (R S : RelationFamily A)
  : R ⊆ᵢ R ⊕ᵢ S
  := λ i, relation_sum_inl (R i) (S i).

(** The second family injection is pointwise as well. *)

(** 第二个族注入同样逐点给出。 *)

Definition family_relation_sum_inr {I : Type} {A : I → Type}
    (R S : RelationFamily A)
  : S ⊆ᵢ R ⊕ᵢ S
  := λ i, relation_sum_inr (R i) (S i).

(** Copair families of witness maps, preserving all endpoints. *)

(** 对见证映射族作余配对，保留全部端点。 *)

Definition family_relation_sum_case {I : Type} {A : I → Type}
    {R S T : RelationFamily A} (h : R ⊆ᵢ T) (k : S ⊆ᵢ T)
  : R ⊕ᵢ S ⊆ᵢ T
  := λ i, relation_sum_case (h i) (k i).

(** The indexed sum is a least upper bound without comparing functions. *)

(** 带索引的和是最小上界，不需要比较函数。 *)

Definition family_relation_sum_universal {I : Type} {A : I → Type}
    (R S T : RelationFamily A)
  : R ⊕ᵢ S ⊆ᵢ T ↔ (R ⊆ᵢ T ∧ S ⊆ᵢ T)
  := ((λ h, ((λ i, fst (fst (relation_sum_universal _ _ _) (h i))),
              (λ i, snd (fst (relation_sum_universal _ _ _) (h i))))),
      (λ h, family_relation_sum_case (fst h) (snd h))).

(** Map the two families independently. *)

(** 独立映射两个族。 *)

Definition family_relation_sum_map {I : Type} {A : I → Type}
    {R S T U : RelationFamily A} (h : R ⊆ᵢ T) (k : S ⊆ᵢ U)
  : R ⊕ᵢ S ⊆ᵢ T ⊕ᵢ U
  := λ i, relation_sum_map (h i) (k i).

(** The family operation respects pointwise equivalence in both arguments. *)

(** 族操作在两个参数上都保持逐点等价。 *)

Global Instance FamilyRelationSum_proper {I : Type} {A : I → Type}
  : Proper (RelationFamilyEq ==> RelationFamilyEq ==>
      RelationFamilyEq) (@FamilyRelationSum I A).
Proof.
  intros R R' h S S' k i. apply RelationSum_proper; [exact (h i) | exact (k i)].
Defined.
