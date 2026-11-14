From Cats.Set.Relation Require Export Closure.
From Stdlib Require Import Arith.PeanoNat.

(** * Strong Normalization of Type-Valued Relations

    Read [R x y] as a directed step from [x] to [y]. A witness of [SN R x]
    is a well-founded tree containing a subtree for every outgoing step,
    not merely a selected terminating path. This is accessibility for the
    converse relation, with witnesses in [Type] rather than [Prop].

    Carrier and edge universes are independent. The tree has an auxiliary
    universe containing both; there is no resizing of its stored branches.
    All witness transformations below are transparent. No equality between
    normalization trees or relation witnesses is required. *)

(** * Type 值关系的强归一化

    将 [R x y] 读作从 [x] 到 [y] 的有向一步。[SN R x] 的见证是一棵良基树，
    为每个向外步骤保存子树，而不只是选定一条终止路径。这是逆关系的可达性，
    但见证位于 [Type]，而非 [Prop]。

    载体与边的宇宙相互独立。树另用容纳两者的辅助宇宙，不缩小所存分支的大小。
    下列见证转换全部透明，不要求归一化树或关系见证之间的相等。 *)

Local Open Scope relation_scope.

(** Every immediate reduct must itself be strongly normalizing. The
    direction is intentionally opposite to the standard incoming-edge
    convention for accessibility. *)

(** 每个直接后继都必须强归一化。这里的方向有意与标准可达性的入边约定相反。 *)

Inductive SN@{a r s} {A : Type@{a}} (R : A → A → Type@{r}) (x : A)
  : Type@{s}
  :=| sn_intro : (∀ y, R x y → SN R y) → SN R x.

Arguments sn_intro {_ _ _} _.

(** A strongly normalizing element supplies a tree for any chosen step. *)

(** 强归一化元素为任意选定的一步提供后继树。 *)

Definition sn_step {A : Type} {R : crelation A} {x y : A}
    (p : SN R x) (h : R x y)
  : SN R y
  := match p with sn_intro next => next y h end.

(** An element with no outgoing steps has a normalization tree with no
    inhabited branches. No decision procedure for steps is needed. *)

(** 没有向外步骤的元素具有无可居留分支的归一化树，不需要步骤判定过程。 *)

Definition sn_terminal {A : Type} {R : crelation A} {x : A}
    (h : ∀ y, R x y → Empty_set)
  : SN R x
  := sn_intro (λ y p, match h y p with end).

(** A natural-number measure strictly decreases along every step. Bounded
    induction constructs the entire normalization tree, with carrier and
    edge universes independent of the small numerical measure. No finite
    enumeration or decision procedure for successors is required. *)

(** 自然数度量沿每一步严格下降。带界归纳构造整棵归一化树，载体与边宇宙
    独立于小的数值度量；不要求后继的有限枚举或判定过程。 *)

Definition sn_measure {A : Type} {R : crelation A} (m : A → nat)
    (decrease : ∀ x y, R x y → m y < m x) (x : A)
  : SN R x.
Proof.
  assert (go : ∀ n x, m x < n → SN R x).
  { induction n as [| n ih]; intros y bound.
    - exact (False_rect _ (Nat.nlt_0_r (m y) bound)).
    - apply sn_intro. intros z h. apply (ih z).
      exact (Nat.lt_le_trans _ _ _ (decrease y z h)
        (proj1 (Nat.lt_succ_r _ _) bound)). }
  exact (go (S (m x)) x (Nat.lt_succ_diag_r (m x))).
Defined.

(** Strong normalization is inherited by every endpoint of a finite path.
    The path and normalization tree bounds remain independent.
    This does not assert strong normalization of the reflexive path
    relation itself, which has a self-loop at every element. *)

(** 强归一化由有限路径的每个终点继承。这并不声称自反路径关系本身强归一化：
    该关系在每个元素处都有自环。路径与归一化树的界保持独立。 *)

Definition sn_rtc@{a r p s} {A : Type@{a}}
    {R : A → A → Type@{r}} {x y : A}
    (h : ReflTransClosure@{a r p} R x y)
  : SN@{a r s} R x → SN@{a r s} R y.
Proof.
  induction h as [x | x y z h p ih]; intros q.
  - exact q.
  - exact (ih (sn_step q h)).
Defined.

(** ** Simulation and Inclusion

    Fix two carriers, relations and a map preserving each directed step.
    A tree at an image pulls back to a tree at its preimage. Preservation
    of steps alone therefore transfers termination in the reverse
    direction; injectivity and surjectivity are unnecessary. *)

(** ** 模拟与包含

    固定两个载体、关系及保持每个有向步骤的映射。像处的归一化树可拉回原像处，
    因而单凭步骤保持性，终止性按反方向传递；无须单射或满射。 *)

Section Simulation.
Context {A B : Type} {R : crelation A} {S : crelation B}.
Context (f : A → B) (h : ∀ x y, R x y → S (f x) (f y)).

(** Induction on the target tree constructs all source branches. The
    native equality used to identify an image is only an induction device;
    no equality of functions or relation evidence is assumed. *)

(** 对目标树归纳构造全部源分支。用于识别像的原生相等只是归纳工具，不假设
    函数相等或关系证据相等。 *)

Definition sn_simulation (x : A) (p : SN S (f x))
  : SN R x.
Proof.
  remember (f x) as z eqn:e. revert x e.
  induction p as [z next ih]. intros x e. subst z.
  apply sn_intro. intros y q.
  exact (ih (f y) (h x y q) y eq_refl).
Defined.

End Simulation.

(** Removing possible steps preserves strong normalization. The two
    relations may have different edge-witness universes. *)

(** 删除可能步骤保持强归一化；两个关系可以使用不同的边见证宇宙。 *)

Definition sn_inclusion {A : Type} {R S : crelation A} (h : R ⊆R S)
    {x : A} (p : SN S x)
  : SN R x
  := sn_simulation (λ x, x) h x p.

(** Mutually included relations have equivalent normalization predicates.
    This compares existence of trees, not the trees themselves. *)

(** 相互包含的关系具有等价的归一化谓词；这里比较树的存在性，不比较树本身。 *)

Global Instance SN_proper {A : Type}
  : Proper (relation_equivalence ==> pointwise_relation A iffT) (@SN A).
Proof.
  intros R S h x. split.
  - exact (sn_inclusion (relation_equiv_backward h)).
  - exact (sn_inclusion (relation_equiv_forward h)).
Defined.

(** ** Independent Reducing Components

    Fix relations on two carriers. Nested induction on their normalization
    trees supports arguments where one step changes exactly one component.
    This is not a termination theorem for the union of arbitrary relations
    on a common carrier, where steps can enable each other indefinitely. *)

(** ** 独立归约分量

    固定两个载体上的关系。对各自归一化树嵌套归纳，可处理每步恰好改变一个
    分量的论证。这并不是同一载体上任意关系之并的终止定理：其步骤可能不断
    相互使能。 *)

Section IndependentComponents.
Context {A B : Type} {R : crelation A} {S : crelation B}.

(** A reusable induction principle for two independently normalizing
    arguments. The result family can retain computational data in [Type]. *)

(** 两个独立强归一化参数的可复用归纳原则；结果族可以在 [Type] 中保留数据。 *)

Definition sn_pair_induction (P : A → B → Type)
    (step : ∀ x y,
      (∀ x', R x x' → P x' y) →
      (∀ y', S y y' → P x y') → P x y)
    {x : A} (p : SN R x) {y : B} (q : SN S y)
  : P x y.
Proof.
  revert y q. induction p as [x next ih]. intros y q.
  induction q as [y next' ih'].
  apply step.
  - intros x' h. exact (ih x' h y (sn_intro next')).
  - exact ih'.
Defined.

(** A product step changes the left component or the right component,
    preserving the other component by native equality. Native equality
    here fixes the representation; it is not an arbitrary setoid step. *)

(** 积上的一步改变左分量或右分量，以原生相等固定另一分量的表示；这里的
    固定并非任意广集相等所给的步骤。 *)

Definition ProductStep (p q : A * B)
  : Type
  := (R (fst p) (fst q) ∧ snd p = snd q) ∨
      (fst p = fst q ∧ S (snd p) (snd q)).

(** Interleaving steps in independent components preserves termination. *)

(** 对独立分量的步骤作交错，保持终止性。 *)

Definition sn_product {x : A} (p : SN R x) {y : B} (q : SN S y)
  : SN ProductStep (x, y).
Proof.
  refine (sn_pair_induction (λ x y, SN ProductStep (x, y)) _ p q).
  intros x' y' ih ih'. apply sn_intro.
  intros [u v] [[h e] | [e h]]; cbn in *.
  - subst v. exact (ih u h).
  - subst u. exact (ih' v h).
Defined.

(** Projecting a product tree recovers normalization of its left
    component, by simulating steps with a fixed right component. *)

(** 以固定右分量模拟步骤，便从积的归一化树恢复左分量的归一化。 *)

Definition sn_product_left {x : A} {y : B} (p : SN ProductStep (x, y))
  : SN R x
  := sn_simulation (λ u, (u, y))
      (λ u v h, inl (h, eq_refl)) x p.

(** The same simulation recovers the right component. *)

(** 同样的模拟恢复右分量。 *)

Definition sn_product_right {x : A} {y : B} (p : SN ProductStep (x, y))
  : SN S y
  := sn_simulation (λ v, (x, v))
      (λ u v h, inr (eq_refl, h)) y p.

(** Product normalization is equivalent to normalization of both
    independent components, without comparing their trees. *)

(** 积归一化等价于两个独立分量各自归一化，不比较相应的树。 *)

Definition sn_product_iff (x : A) (y : B)
  : SN ProductStep (x, y) ↔ (SN R x ∧ SN S y)
  := ((λ p, (sn_product_left p, sn_product_right p)),
      (λ p, sn_product (fst p) (snd p))).

End IndependentComponents.

Arguments ProductStep {_ _} R S _ _.

(** An infinite step sequence contradicts an SN tree at its starting
    point. This is one implication only: absence of an infinite sequence
    is not used as a constructive replacement for the tree definition. *)

(** 无限步骤序列与起点处的强归一化树矛盾。这里只给出一个方向，不以不存在
    无限序列作为树定义的构造性替代。 *)

Definition sn_no_infinite_sequence {A : Type} {R : crelation A}
    (f : nat → A) (h : ∀ n, R (f n) (f (S n)))
    (p : SN R (f 0))
  : Empty_set.
Proof.
  assert (go : ∀ z, SN R z → ∀ n, z = f n → Empty_set).
  { intros z q. induction q as [z next ih]. intros n e. subst z.
    exact (ih (f (S n)) (h n) (S n) eq_refl). }
  exact (go (f 0) p 0 eq_refl).
Defined.

(** ** Self-Loops Obstruct Normalization

    For any carrier and directed relation, induction on a normalization
    tree rules out a self-loop. Consequently reflexive path closure is
    useful for transporting SN to reducts, but cannot be its step relation. *)

(** ** 自环阻碍归一化

    对任意载体与有向关系，归一化树上的归纳排除自环。因此，自反路径闭包可
    用来将强归一化传给后继，却不能本身充当强归一化的步骤关系。 *)

Section SelfLoops.
Context {A : Type} {R : crelation A}.

(** Every self-loop contradicts the tree's well-founded branching. *)

(** 任意自环都与树的良基分支矛盾。 *)

Definition sn_no_self_loop {x : A} (p : SN R x)
  : R x x → Empty_set.
Proof.
  induction p as [x next ih]. intros h. exact (ih x h h).
Defined.

End SelfLoops.

(** The empty path already rules out SN for reflexive transitive closure. *)

(** 空路径已经排除了反身传递闭包的强归一化。 *)

Definition sn_not_rtc {A : Type} (R : crelation A) (x : A)
  : SN (R^*) x → Empty_set
  := λ p, sn_no_self_loop p (rtc_refl x).
