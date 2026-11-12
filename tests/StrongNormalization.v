From Cats.Set.Relation Require Import StrongNormalization.

(** * Strong-Normalization Interface Checks

    These checks separate carrier, edge and tree universes, then compute
    with transparent countdown trees and a noninjective simulation. They
    concern the reusable relation interface, not a particular calculus. *)

(** * 强归一化接口检查

    先分离载体、边及树的宇宙，再检查透明倒计数树与非单射模拟的计算。
    检查针对可复用的关系接口，不依赖某个演算。 *)

Local Open Scope relation_scope.

(** ** Small Edges over a Larger Carrier

    Fix [r < a < s]. The SN tree must contain the carrier and edge data,
    without forcing their two input universes to coincide. *)

(** ** 大载体上的小边

    固定 [r < a < s]。归一化树须容纳载体与边数据，而不迫使两个输入宇宙相等。 *)

Section SmallEdges.
Universes r a s.
Constraint r < a, a < s.
Context (A : Type@{a}) (R : A → A → Type@{r}).

(** Taking a step retains the separated tree universe. *)

(** 取一步后仍保留分离的树宇宙。 *)

Definition small_edge_sn_step {x y : A}
    (p : SN@{a r s} R x) (h : R x y)
  : SN@{a r s} R y
  := sn_step p h.

End SmallEdges.

(** ** Large Edges over a Smaller Carrier

    Fix the reverse order [a < r < s] and check finite-path inheritance. *)

(** ** 小载体上的大边

    固定反向的 [a < r < s] 大小顺序，检查有限路径的后继继承性。 *)

Section LargeEdges.
Universes a r s.
Constraint a < r, r < s.
Context (A : Type@{a}) (R : A → A → Type@{r}).

(** Paths preserve SN without identifying carrier and edge bounds. *)

(** 路径保持强归一化，不识别载体界与边界。 *)

Definition large_edge_sn_path {x y : A}
    (h : (R^*) x y) (p : SN@{a r s} R x)
  : SN@{a r s} R y
  := sn_rtc h p.

End LargeEdges.

(** ** Pullback to Smaller Trees

    Fix a target carrier, edges and tree strictly larger than the source
    tree. A simulation constructs source trees from target trees; it does
    not resize a target tree or impose a bound from target to source. *)

(** ** 拉回较小的树

    固定严格大于源树的目标载体、边及树。模拟由目标树构造源树，不缩小目标树，
    也不施加从目标到源的大小界限。 *)

Section SmallerPullback.
Universes a r s b q t.
Constraint a < r, r < s, s < b, b < q, q < t.
Context (A : Type@{a}) (B : Type@{b}).
Context (R : A → A → Type@{r}) (S : B → B → Type@{q}).
Context (f : A → B) (h : ∀ x y, R x y → S (f x) (f y)).

(** The inferred simulation interface keeps the two tree bounds separate. *)

(** 推导出的模拟接口保持两个树界相互分离。 *)

Definition simulation_smaller_tree (x : A) (p : SN@{b q t} S (f x))
  : SN@{a r s} R x
  := sn_simulation f h x p.

End SmallerPullback.

(** ** Independent Components with Different Witness Sizes

    Fix [a < r < b < q < s < t]. The component trees live at [t], while
    the combined tree can live at [s]. Induction can also return small
    computational data despite the size of the input trees. *)

(** ** 见证大小不同的独立分量

    固定 [a < r < b < q < s < t]。分量树位于 [t]，组合树仍可位于 [s]；
    即使输入树很大，归纳也能返回小的计算数据。 *)

Section IndependentSizes.
Universes a r b q s t.
Constraint a < r, r < b, b < q, q < s, s < t.
Context (A : Type@{a}) (B : Type@{b}).
Context (R : A → A → Type@{r}) (S : B → B → Type@{q}).

(** The product tree stores product steps, with no dependence on the size
    of the input trees used to construct it. *)

(** 积树保存积上的步骤，其大小不依赖于构造时所用输入树的大小。 *)

Definition independent_product_sn {x : A} (p : SN@{a r t} R x)
    {y : B} (q : SN@{b q t} S y)
  : SN@{b q s} (ProductStep R S) (x, y)
  := sn_product p q.

(** Nested induction can return a small value without resizing its inputs. *)

(** 嵌套归纳可以返回小的值，无须缩小输入。 *)

Definition independent_small_result {x : A} (p : SN@{a r t} R x)
    {y : B} (q : SN@{b q t} S y)
  : nat
  := sn_pair_induction (λ _ _, nat) (λ _ _ _ _, 0) p q.

End IndependentSizes.

(** ** Transparent Computations

    Countdown steps carry arbitrary natural-number tags. A simulated
    carrier adds a Boolean label that may change on every step; projecting
    the counter preserves steps without being injective. *)

(** ** 透明计算

    倒计数步骤携带任意自然数标签。模拟的载体增加可在每步改变的布尔标签，
    计数器投影保持步骤，但不是单射。 *)

Section Computations.

(** Step evidence retains its tag as ordinary Type-valued data. *)

(** 步骤证据将标签保留为普通 Type 值数据。 *)

Definition Countdown (n m : nat)
  : Type
  := (n = S m) ∧ nat.

(** Structural induction gives a transparent tree for every counter. *)

(** 结构归纳为每个计数器给出透明的归一化树。 *)

Definition countdown_sn (n : nat)
  : SN Countdown n.
Proof.
  induction n as [| n ih]; apply sn_intro; intros m [e tag].
  - discriminate e.
  - injection e as e. subst m. exact ih.
Defined.

(** Selecting a branch computes to the predecessor's existing tree. *)

(** 选取分支计算为前驱已有的树。 *)

Example countdown_step_computes
  : sn_step (countdown_sn 2) (eq_refl, 37) = countdown_sn 1.
Proof. reflexivity. Qed.

(** Simulation allows arbitrary changes to the unused Boolean label. *)

(** 模拟允许任意改变未使用的布尔标签。 *)

Definition tagged_countdown_sn (p : nat * bool)
  : SN (λ x y, Countdown (fst x) (fst y)) p
  := sn_simulation fst (λ _ _ h, h) p (countdown_sn (fst p)).

(** Pullback and step selection remain computational even across labels. *)

(** 即使跨越不同标签，拉回与选取步骤仍可计算。 *)

Example simulation_step_computes
  : sn_step (tagged_countdown_sn (2, true))
      (y := (1, false)) (eq_refl, 11) =
      tagged_countdown_sn (1, false).
Proof. reflexivity. Qed.

(** Independent components can interleave left and right steps. *)

(** 独立分量可交错执行左、右步骤。 *)

Definition countdown_product_sn
  : SN (ProductStep Countdown Countdown) (2, 3)
  := sn_product (countdown_sn 2) (countdown_sn 3).

(** Projecting after a left step produces a tree for the new left counter. *)

(** 左侧步骤之后投影，得到新左计数器的归一化树。 *)

Definition countdown_product_reduct_sn
  : SN Countdown 1
  := sn_product_left
      (sn_step countdown_product_sn (y := (1, 3))
        (inl ((eq_refl, 19), eq_refl))).

End Computations.
