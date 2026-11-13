From Cats.Set.Relation Require Export Compatible.

(** * Compatible Equivalence Closure

    Lift every generating edge of a finite zig-zag through a single-hole
    operation. Forward edges remain forward; backward edges use symmetry
    at the target. Consequently equivalence closure preserves compatibility.

    This gives precisely the one-sided interchange required by the generic
    composition theorem. Context closure followed by equivalence closure
    is therefore the least extension closed under both operations. *)

(** * 相容等价闭包

    将有限之字路径的每条生成边通过单孔操作提升。正向边保持正向，反向边使用
    目标的对称性。因此等价闭包保持相容性。

    这恰好给出一般复合定理所需的单向交换。先上下文闭包、再等价闭包，因而是
    同时对两个操作闭合的最小扩张。 *)

Local Open Scope relation_scope.

(** Path lifting follows from the existing fold along a function, applied
    to the action of the operation between its specified fibers. *)

(** 路径提升来自已有的沿函数折叠，应用于操作在指定纤维之间的作用。 *)

Definition family_equivalence_closure_compatible@{i a o r +}
    {I : Type@{i}} {A : I → Type@{a}}
    (K : ContextSystem@{i a o} A) {R : RelationFamily@{i a r _} A}
    (hr : is_compatible K R)
  : is_compatible K (R^≈ᵢ).
Proof.
  intros i j c x y p.
  exact (equivalence_closure_preserves (K i j c)
    (λ x y q, closure_inflate (EquivalenceClosure (A j)) (R j)
      (K i j c x) (K i j c y) (hr i j c x y q)) p).
Defined.

(** Move context iteration past equivalence closure in one direction.
    The reverse direction generally fails: independent contexts around
    adjacent path edges need not be one common context around the path. *)

(** 沿一个方向将上下文迭代移过等价闭包。反向一般不成立：相邻路径边外部的
    独立上下文不一定来自整条路径外部的同一个公共上下文。 *)

Definition compatible_equivalence_interchange@{i a o r +}
    {I : Type@{i}} {A : I → Type@{a}}
    (K : ContextSystem@{i a o} A) (R : RelationFamily@{i a r _} A)
  : (R^≈ᵢ)^C[K] ⊆ᵢ (R^C[K])^≈ᵢ
  := context_closure_preserves K
      (family_equivalence_closure_compatible K
        (context_closure_compatible K R))
      (closure_monotone (FamilyEquivalenceClosure A)
        (closure_inflate (CompatibleClosure K) R)).

(** The chosen congruence closure reuses the general composite operator;
    no separate monotonicity, inflation or flattening proof is needed. *)

(** 选定合同闭包复用一般复合算子，不需另证单调性、扩张律或压平律。 *)

Definition CongruenceClosure@{i a o r +}
    {I : Type@{i}} {A : I → Type@{a}}
    (K : ContextSystem@{i a o} A)
  : Closure (λ R S : RelationFamily@{i a r _} A, R ⊆ᵢ S)
  := @CompositeClosure (RelationFamily A) (@RelationFamilyLe I A)
      (RelationFamilyPreorder A) (CompatibleClosure K)
      (FamilyEquivalenceClosure A) (compatible_equivalence_interchange K).

(** Closed relations are exactly the compatible equivalence relations.
    This is the generic simultaneous-closedness theorem, with its two
    component predicates interpreted by the earlier characterizations. *)

(** 闭关系恰好是相容等价关系。这是一般同时闭性定理，再用先前刻画解释两个
    分量谓词。 *)

Definition congruence_closure_closed@{i a o r +}
    {I : Type@{i}} {A : I → Type@{a}}
    (K : ContextSystem@{i a o} A) (R : RelationFamily@{i a r _} A)
  : is_closed (CongruenceClosure K) R ↔
      (is_compatible K R ∧ ∀ j, Equivalence@{a r} (R j)).
Proof.
  pose (hc := @composite_closure_closed _ _ (RelationFamilyPreorder A)
    (CompatibleClosure K) (FamilyEquivalenceClosure A)
    (compatible_equivalence_interchange K) R).
  split.
  - intros h. split.
    + exact (fst (compatible_closure_closed K R) (fst (fst hc h))).
    + exact (fst (family_equivalence_closure_closed R) (snd (fst hc h))).
  - intros [h e]. apply (snd hc). split.
    + exact (snd (compatible_closure_closed K R) h).
    + exact (snd (family_equivalence_closure_closed R) e).
Defined.

(** The generated extension is itself compatible, by generic flattening. *)

(** 由一般压平律，生成的扩张本身相容。 *)

Definition congruence_closure_compatible@{i a o r +}
    {I : Type@{i}} {A : I → Type@{a}}
    (K : ContextSystem@{i a o} A) (R : RelationFamily@{i a r _} A)
  : is_compatible K (CongruenceClosure K R)
  := fst (fst (congruence_closure_closed K (CongruenceClosure K R))
      (closure_flatten (CongruenceClosure K) R)).

(** Each generated fiber has its equivalence laws. Different path or
    context witnesses are not identified by this property. *)

(** 每个生成纤维具有等价律。此性质不识别不同路径或上下文见证。 *)

Global Instance CongruenceClosure_Equivalence@{i a o r +}
    {I : Type@{i}} {A : I → Type@{a}}
    (K : ContextSystem@{i a o} A) (R : RelationFamily@{i a r _} A) (j : I)
  : Equivalence@{a r} (CongruenceClosure K R j)
  := snd (fst (congruence_closure_closed K (CongruenceClosure K R))
      (closure_flatten (CongruenceClosure K) R)) j.

(** Minimality among compatible equivalence extensions follows directly
    from the general closure universal property. *)

(** 在相容等价扩张中的最小性，直接来自一般闭包泛性质。 *)

Definition congruence_closure_universal@{i a o r +}
    {I : Type@{i}} {A : I → Type@{a}}
    (K : ContextSystem@{i a o} A) (R S : RelationFamily@{i a r _} A)
    (hs : is_compatible K S) (es : ∀ j, Equivalence@{a r} (S j))
  : CongruenceClosure K R ⊆ᵢ S ↔ R ⊆ᵢ S
  := @closure_universal _ _ (RelationFamilyPreorder A)
      (CongruenceClosure K) R S
      (snd (congruence_closure_closed K S) (hs, es)).

(** Specified equivalence of generators is respected by the composite. *)

(** 复合保持生成元的指定等价。 *)

Global Instance CongruenceClosure_proper {I : Type} {A : I → Type}
    (K : ContextSystem A)
  : Proper (RelationFamilyEq ==> RelationFamilyEq) (CongruenceClosure K).
Proof.
  intros R S h. apply relation_family_equiv_of_inclusions.
  - exact (closure_monotone (CongruenceClosure K)
      (λ i, relation_equiv_forward (h i))).
  - exact (closure_monotone (CongruenceClosure K)
      (λ i, relation_equiv_backward (h i))).
Defined.

(** ** Joint Equational Derivations

    A second presentation generates equivalence and context rules together,
    as a syntax-directed equational theory would. It is only a witness
    presentation, not another independently packaged closure operator. Its
    fold and the composite's leastness compare it with finite zig-zags. *)

(** ** 共同生成的等式推导

    第二种呈现同时生成等价规则与上下文规则，如同按语法给出的等式理论。它只
    是见证呈现，不是另行封装的闭包算子。其折叠与复合的最小性共同给出它和
    有限之字路径之间的比较。 *)

(** A generator, the three equivalence rules, and one-hole congruence.
    Binary congruence can be obtained by two one-hole replacements and
    transitivity, keeping the fixed argument in each operation's label. *)

(** 一条生成元、三条等价规则，以及单孔合同规则。二元合同可通过两次单孔替换
    与传递性得到，每次操作的标签保存不变的另一参数。 *)

Inductive EquationalClosure {I : Type} {A : I → Type}
    (K : ContextSystem A) (R : RelationFamily A)
  : RelationFamily A
  :=| equation_step {i} {x y : A i}
        : R i x y → EquationalClosure K R i x y
    | equation_refl {i} (x : A i) : EquationalClosure K R i x x
    | equation_sym {i} {x y : A i}
        : EquationalClosure K R i x y → EquationalClosure K R i y x
    | equation_trans {i} {x y z : A i}
        : EquationalClosure K R i x y → EquationalClosure K R i y z →
          EquationalClosure K R i x z
    | equation_context {i j} (c : context_operation K i j) {x y : A i}
        : EquationalClosure K R i x y →
          EquationalClosure K R j (K i j c x) (K i j c y).

Arguments equation_step {_ _ _ _ _ _ _} _.
Arguments equation_refl {_ _ _ _ _} _.
Arguments equation_sym {_ _ _ _ _ _ _} _.
Arguments equation_trans {_ _ _ _ _ _ _ _} _ _.
Arguments equation_context {_ _ _ _ _ _} _ {_ _} _.

(** The joint presentation supplies equivalence directly from its rules. *)

(** 共同呈现直接从其规则给出等价性。 *)

Global Program Instance EquationalClosure_Equivalence
    {I : Type} {A : I → Type} (K : ContextSystem A)
    (R : RelationFamily A) (i : I)
  : Equivalence (EquationalClosure K R i)
  :=
  {|Equivalence_Reflexive := equation_refl
  ; Equivalence_Symmetric x y := equation_sym
  ; Equivalence_Transitive x y z := equation_trans
  |}.

(** Its context rule supplies compatibility across the specified indices. *)

(** 其上下文规则给出跨指定索引的相容性。 *)

Definition equational_closure_compatible {I : Type} {A : I → Type}
    (K : ContextSystem A) (R : RelationFamily A)
  : is_compatible K (EquationalClosure K R)
  := λ i j c x y p, equation_context c p.

(** Interpret a derivation in any compatible equivalence target receiving
    the generators. Only the stated target operations are used. *)

(** 将推导解释到接收生成元的任意相容等价目标，仅使用所声明的目标操作。 *)

Definition equational_closure_preserves {I : Type} {A : I → Type}
    (K : ContextSystem A) {R S : RelationFamily A}
    (hs : is_compatible K S) (es : ∀ i, Equivalence (S i))
    (h : R ⊆ᵢ S)
  : EquationalClosure K R ⊆ᵢ S.
Proof.
  intros i x y p.
  induction p as [i x y p | i x | i x y p ih |
    i x y z p ih q iq | i j c x y p ih].
  - exact (h i x y p).
  - exact (@Equivalence_Reflexive _ (S i) (es i) x).
  - exact (@Equivalence_Symmetric _ (S i) (es i) x y ih).
  - exact (@Equivalence_Transitive _ (S i) (es i) x y z ih iq).
  - exact (hs i j c x y ih).
Defined.

(** Joint equational generation and context steps followed by finite
    zig-zags generate the same relation. Both transformations are
    transparent, with no inverse equations on derivations. *)

(** 共同等式生成与先上下文步骤、后有限之字路径生成同一关系。两个转换均透明，
    不为推导施加互逆方程。 *)

Definition equational_closure_paths@{i a o r +}
    {I : Type@{i}} {A : I → Type@{a}}
    (K : ContextSystem@{i a o} A) (R : RelationFamily@{i a r _} A)
  : EquationalClosure K R ≈ᵢ (R^C[K])^≈ᵢ.
Proof.
  apply relation_family_equiv_of_inclusions.
  - exact (equational_closure_preserves K
      (congruence_closure_compatible K R)
      (CongruenceClosure_Equivalence K R)
      (closure_inflate (CongruenceClosure K) R)).
  - apply (snd (congruence_closure_universal K R
      (EquationalClosure K R) (equational_closure_compatible K R)
      (EquationalClosure_Equivalence K R))).
    intros i x y p. exact (equation_step p).
Defined.

(** Joint derivations also respect the specified equivalence of generators. *)

(** 共同推导也保持生成元的指定等价。 *)

Global Instance EquationalClosure_proper {I : Type} {A : I → Type}
    (K : ContextSystem A)
  : Proper (RelationFamilyEq ==> RelationFamilyEq) (EquationalClosure K).
Proof.
  intros R S h. apply relation_family_equiv_of_inclusions.
  - exact (equational_closure_preserves K (equational_closure_compatible K S)
      (EquationalClosure_Equivalence K S)
      (λ i x y p, equation_step (fst (h i x y) p))).
  - exact (equational_closure_preserves K (equational_closure_compatible K R)
      (EquationalClosure_Equivalence K R)
      (λ i x y p, equation_step (snd (h i x y) p))).
Defined.
