From Cats.Set Require Export Core.

(** * Closure Operators on Type-Valued Preorders

    A closure enlarges an object monotonically, and a second application
    can be flattened. The order need not be antisymmetric: idempotence
    means comparison in both directions, not native equality of objects,
    functions or witnesses. No category structure is needed here. *)

(** * Type 值预序上的闭包算子

    闭包单调地扩张对象，第二次应用可以压平。预序无须反对称；幂等性表示
    双向比较，不表示对象、函数或见证的原生相等。本层不依赖范畴结构。 *)

(** Candidate closure laws for a specified operation. The final field is
    only the flattening direction; inflation supplies the reverse one. *)

(** 指定操作的候选闭包律。最后一项只要求压平方向，反向由扩张律提供。 *)

Definition is_closure {X : Type} (R : crelation X) (c : X → X)
  : Type
  := (∀ x y, R x y → R (c x) (c y)) ∧
      ((∀ x, R x (c x)) ∧ (∀ x, R (c (c x)) (c x))).

(** A chosen operation with its closure laws. The unique function coercion
    exposes the operation; constructing a closure always supplies its laws. *)

(** 选定的操作及其闭包律。唯一的函数强制转换暴露操作；构造闭包时须提供定律。 *)

Record Closure {X : Type} (R : crelation X)
  :=
  {
  (** The selected extension operation. *)

  (** 选定的扩张操作。 *)

    closure_map :> X → X

  (** Monotonicity, inflation and flattening for that same operation. *)

  (** 同一操作的单调性、扩张律与压平律。 *)

  ; closure_laws : is_closure R closure_map
  }.

Section ClosureLaws.
Context {X : Type} {R : crelation X}.

(** Monotonicity transports an input comparison to the closed objects. *)

(** 单调性将输入比较运输到闭包后的对象。 *)

Definition closure_monotone (c : Closure R) {x y : X} (h : R x y)
  : R (c x) (c y)
  := fst (closure_laws R c) x y h.

(** Inflation embeds each input into its chosen closed extension. *)

(** 扩张将每个输入嵌入其选定闭扩张。 *)

Definition closure_inflate (c : Closure R) (x : X)
  : R x (c x)
  := fst (snd (closure_laws R c)) x.

(** Flattening removes one layer without identifying the two objects. *)

(** 压平消去一层闭包，不把两个对象判为原生相等。 *)

Definition closure_flatten (c : Closure R) (x : X)
  : R (c (c x)) (c x)
  := snd (snd (closure_laws R c)) x.

(** A closed object admits the reverse comparison to inflation. This
    predicate records a witness, rather than an equation of representations. *)

(** 闭对象具有扩张的反向比较。谓词记录见证，不要求表示之间的等式。 *)

Definition is_closed (c : Closure R) (x : X)
  : Type
  := R (c x) x.

(** Every chosen closed extension is itself closed. *)

(** 每个选定闭扩张自身都是闭的。 *)

Definition closure_closed (c : Closure R) (x : X)
  : is_closed c (c x)
  := closure_flatten c x.

(** Compare operations pointwise. All comparison witnesses remain data. *)

(** 逐点比较操作，全部比较见证仍保留为数据。 *)

Definition ClosureLe (c d : Closure R)
  : Type
  := ∀ x, R (c x) (d x).

(** Equivalence of closures means two pointwise comparisons, without
    equality of the functions or their law fields. *)

(** 闭包等价是两个方向的逐点比较，不要求函数或定律字段相等。 *)

Definition ClosureEq (c d : Closure R)
  : Type
  := ClosureLe c d ∧ ClosureLe d c.

End ClosureLaws.

Declare Scope closure_scope.
Delimit Scope closure_scope with closure.
Infix "⊑Cl" := ClosureLe (at level 70) : closure_scope.
Infix "≈Cl" := ClosureEq (at level 70) : closure_scope.
Local Open Scope closure_scope.

Section PreorderClosures.
Context {X : Type} {R : crelation X} `{HR : !PreOrder R}.

(** A comparison from an input to a closed target extends through closure.
    First use monotonicity, then the target's closedness witness. *)

(** 输入到闭目标的比较可延拓经过闭包：先用单调性，再用目标的闭性见证。 *)

Definition closure_extend (c : Closure R) {x y : X}
    (hy : is_closed c y) (h : R x y)
  : R (c x) y
  := transitivity (closure_monotone c h) hy.

(** Restriction precomposes a comparison with inflation. *)

(** 限制将比较与扩张见证预合成。 *)

Definition closure_restrict (c : Closure R) {x y : X} (h : R (c x) y)
  : R x y
  := transitivity (closure_inflate c x) h.

(** The least-closed-extension property. The displayed equivalence provides
    two witness transformations, not inverse equations on those witnesses.
    In a preorder, uniqueness of an object means mutual comparison. *)

(** 最小闭扩张性质。所陈述等价提供两个见证转换，不要求见证上的互逆方程。
    在预序中，对象唯一性表示相互可比较。 *)

Definition closure_universal (c : Closure R) {x y : X}
    (hy : is_closed c y)
  : R (c x) y ↔ R x y
  := (closure_restrict c, closure_extend c hy).

(** Closedness is stable under mutual comparison. This is the appropriate
    invariance when the preorder has multiple equivalent representatives. *)

(** 闭性在双向比较下保持；这适用于预序中具有不同等价表示的情形。 *)

Definition closure_closed_transport (c : Closure R) {x y : X}
    (h : R x y) (k : R y x) (hx : is_closed c x)
  : is_closed c y
  := transitivity (closure_monotone c k) (transitivity hx h).

(** Pointwise comparison is a Type-valued preorder on closure structures. *)

(** 逐点比较在闭包结构上形成 Type 值预序。 *)

Global Instance ClosureLe_PreOrder
  : PreOrder (@ClosureLe X R).
Proof.
  split.
  - intros c x. reflexivity.
  - intros c d e h k x. exact (transitivity (h x) (k x)).
Defined.

(** Mutual pointwise comparison supplies the specified closure equivalence. *)

(** 双向逐点比较给出闭包的指定等价关系。 *)

Global Instance ClosureEq_Equivalence
  : Equivalence (@ClosureEq X R).
Proof.
  split.
  - intros c. split; intros x; reflexivity.
  - intros c d [h k]. exact (k, h).
  - intros c d e [h k] [u v].
    split; intros x; [exact (transitivity (h x) (u x)) |
      exact (transitivity (v x) (k x))].
Defined.

(** A smaller closure has at least the closed objects of a larger closure.
    Conversely, this containment recovers pointwise comparison by testing
    the closed extension [d x]. Thus order of operators reverses order of
    their closed-object predicates. *)

(** 较小闭包至少具有较大闭包的全部闭对象。反过来，在闭扩张 [d x] 处检验
    此包含便能恢复逐点比较。因此算子顺序与闭对象谓词的包含方向相反。 *)

Definition closure_le_iff_closed (c d : Closure R)
  : c ⊑Cl d ↔ (∀ x, is_closed d x → is_closed c x).
Proof.
  split.
  - intros h x hx. exact (transitivity (h x) hx).
  - intros h x. exact (closure_extend c (h (d x) (closure_closed d x))
      (closure_inflate d x)).
Defined.

(** Closures with the same closed objects are pointwise equivalent. Neither
    equality of predicate functions nor equality of chosen witnesses is used. *)

(** 具有相同闭对象的闭包逐点等价，不使用谓词函数或选定见证的相等。 *)

Definition closure_unique (c d : Closure R)
    (h : ∀ x, is_closed c x ↔ is_closed d x)
  : c ≈Cl d.
Proof.
  split; apply (snd (closure_le_iff_closed _ _)); intros x hx.
  - exact (snd (h x) hx).
  - exact (fst (h x) hx).
Defined.

(** The identity operation is a closure on any preorder. *)

(** 任意预序上的恒等操作都是闭包。 *)

Program Definition IdentityClosure
  : Closure R
  :=
  {|closure_map x := x
  |}.
Next Obligation.
  split; [intros x y h; exact h |].
  split; intros x; reflexivity.
Defined.

(** A candidate least extension into a specified predicate. The chosen map
    is supplied explicitly; this predicate does not choose witnesses from
    mere existential propositions. *)

(** 指定谓词中的候选最小扩张。映射显式给出；此谓词不从命题存在性中选择见证。 *)

Definition is_closure_universal (P : X → Type) (c : X → X)
  : Type
  := ∀ x, P (c x) ∧ (R x (c x) ∧
      (∀ y, P y → R x y → R (c x) y)).

(** Every closure supplies these universal extensions for its closed-object
    predicate. This connects the operational laws to the candidate property. *)

(** 每个闭包都为其闭对象谓词提供这种泛扩张，将操作定律接到候选性质。 *)

Definition closure_is_universal (c : Closure R)
  : is_closure_universal (is_closed c) c
  := λ x, (closure_closed c x,
      (closure_inflate c x, λ y hy hxy, closure_extend c hy hxy)).

(** Chosen universal extensions satisfy the closure laws. This construction
    does not identify [P] with the fixed-object predicate: that identification
    additionally needs invariance of [P] under mutual comparison. *)

(** 选定泛扩张满足闭包律。此构造不将 [P] 与不动对象谓词直接识别；要作这种
    识别，还须假设 [P] 在双向比较下保持。 *)

Program Definition ClosureFromUniversal (P : X → Type) (c : X → X)
    (h : is_closure_universal P c)
  : Closure R
  :=
  {|closure_map := c
  |}.
Next Obligation.
  split.
  - intros x y k. apply (snd (snd (h x))).
    + exact (fst (h y)).
    + exact (transitivity k (fst (snd (h y)))).
  - split.
    + intros x. exact (fst (snd (h x))).
    + intros x. apply (snd (snd (h (c x))));
        [exact (fst (h x)) | reflexivity].
Defined.

End PreorderClosures.
