From Cats.Set.Relation Require Import Newman.
From Stdlib Require Import Arith.PeanoNat.

(** * Constructive Confluence Interface Regressions

    Check independent path and normalization-tree bounds in both orders,
    including edge witnesses below the carrier. A finite concrete fork
    also checks that Newman returns computational paths. *)

(** * 构造性合流接口回归

    检查路径界与归一化树界在两种次序下独立，包括边见证低于载体的情形。
    一个具体有限分叉还检查 Newman 返回的路径可计算。 *)

Local Open Scope relation_scope.

(** ** Paths below Trees

    Fix [a < r < p < s]. Joins stay at [p], below the input tree. *)

(** ** 低于树的路径

    固定 [a < r < p < s]。汇合保留在 [p]，低于输入树。 *)

Section SmallPaths.
Universes a r p s.
Constraint a < r, r < p, p < s.
Context {A : Type@{a}} (R : A → A → Type@{r}).
Context (local : is_locally_confluent@{a r p p} R).

(** Large input trees are not stored in the returned join paths. *)

(** 大输入树不存入返回的汇合路径。 *)

Definition small_path_newman {x : A} (normal : SN@{a r s} R x)
  : is_confluent_at@{a r p p} R x
  := newman_at local normal.

End SmallPaths.

(** ** Paths above Trees

    Fix [r < a < s < p], reversing the edge/carrier and path/tree orders. *)

(** ** 高于树的路径

    固定 [r < a < s < p]，反转边与载体、路径与树的次序。 *)

Section LargePaths.
Universes r a s p.
Constraint r < a, a < s, s < p.
Context {A : Type@{a}} (R : A → A → Type@{r}).
Context (local : is_locally_confluent@{a r p p} R).

(** Large join paths do not enlarge the input normalization tree. *)

(** 大汇合路径不增大输入归一化树。 *)

Definition large_path_newman {x : A} (normal : SN@{a r s} R x)
  : is_confluent_at@{a r p p} R x
  := newman_at local normal.

End LargePaths.

(** ** A Computational Fork

    Four states form a diamond. All edges carry [unit] data, and the
    local joining operation explicitly supplies two paths to the bottom. *)

(** ** 可计算的分叉

    四个状态形成菱形。全部边保存 [unit] 数据；局部汇合操作显式提供两条到
    底部的路径。 *)

Section Fork.

(** The source, two alternatives and their common successor. *)

(** 来源、两个备选及其共同后继。 *)

Inductive Fork
  :=| fork_top
    | fork_left
    | fork_right
    | fork_bottom.

(** Exactly the four directed edges of the diamond. *)

(** 恰好给出菱形的四条有向边。 *)

Definition ForkStep (x y : Fork)
  : Type
  := match x, y with
      | fork_top, fork_left | fork_top, fork_right |
        fork_left, fork_bottom | fork_right, fork_bottom => unit
      | _, _ => Empty_set
      end.

(** A displayed finite path to the bottom from every state. *)

(** 从每个状态到达底部的显式有限路径。 *)

Definition fork_path (x : Fork)
  : (ForkStep^*) x fork_bottom.
Proof.
  destruct x.
  - exact (rtc_cons (x := fork_top) (y := fork_left)
      (z := fork_bottom) tt
      (rtc_step (x := fork_left) (y := fork_bottom) tt)).
  - exact (rtc_step (x := fork_left) (y := fork_bottom) tt).
  - exact (rtc_step (x := fork_right) (y := fork_bottom) tt).
  - exact (rtc_refl _).
Defined.

(** Every local fork is joined at the bottom. *)

(** 每个局部分叉均在底部汇合。 *)

Definition fork_local
  : is_locally_confluent ForkStep
  := λ x y z h k, existT _ fork_bottom (fork_path y, fork_path z).

(** A structural measure constructs the required input trees. *)

(** 结构度量构造所需输入树。 *)

Definition fork_normal (x : Fork)
  : SN ForkStep x.
Proof.
  apply (sn_measure (λ x,
    match x with fork_top => 2 | fork_bottom => 0 | _ => 1 end)).
  intros u v h. destruct u, v; cbn in *; try destruct h;
    apply Nat.lt_succ_diag_r.
Defined.

(** Count the supplied steps, rather than comparing path witnesses. *)

(** 计算已给步骤的数目，不比较路径见证。 *)

Fixpoint fork_path_length {x y : Fork} (p : (ForkStep^*) x y)
  : nat
  := match p with rtc_refl _ => 0 | rtc_cons _ q => S (fork_path_length q) end.

(** Newman computes a common successor and one residual edge on each leg. *)

(** Newman 算出共同后继，以及每腿上的一条剩余边。 *)

Example newman_fork_computes
  : let h := newman fork_local fork_normal fork_top fork_left fork_right
      (rtc_step (x := fork_top) (y := fork_left) tt)
      (rtc_step (x := fork_top) (y := fork_right) tt) in
    (projT1 h, fork_path_length (fst (projT2 h)),
      fork_path_length (snd (projT2 h))) = (fork_bottom, 1, 1).
Proof. reflexivity. Defined.

End Fork.
