From Cats Require Import
  Cat.Monad.Applicative
  Cat.Computational.Arrow.Kleisli
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Monoid.

Local Open Scope monoidal_scope.
Local Open Scope monad_scope.

(** * Stateful Computation on Setoids

    A computation returns a value and a new state. All maps respect the
    specified equalities. The chosen strength and derived Applicative are
    explicit values; importing this module selects no model instance. *)

(** * 广集上的状态计算

    计算返回一个值及新状态。所有映射均保持指定相等。选定强度及诱导的
    Applicative 都是显式值，导入本模块不自动选择模型实例。 *)

(** Map the value returned by a stateful computation, preserving its state. *)

(** 映射状态计算返回的值，保持其状态。 *)

Program Definition state_map {R X Y : SetC} (f : X →r Y)
  : (R →S (X ×S R)) →r (R →S (Y ×S R))
  :=
  {|func k := {|func r := (f (fst (k r)), snd (k r))|}
  |}.
Next Obligation.
  intros r r' H. cbn in *. pose proof (@func_proper _ _ k r r' H) as K.
  destruct (k r) as [x s], (k r') as [x' s']. cbn in K |-.
  destruct K as [Hx Hs].
  split; [apply func_proper; exact Hx | exact Hs].
Defined.
Next Obligation.
  intros k k' H r. cbn in *. specialize (H r).
  destruct (k r) as [x s], (k' r) as [x' s']. cbn in H |-.
  destruct H as [Hx Hs].
  split; [apply func_proper; exact Hx | exact Hs].
Defined.

(** The state carrier and equality levels remain separate. Function-space
    equality requires both to fit in the ambient equality level, which may
    be strictly below the ambient carrier level. The following interfaces
    keep the two ambient levels explicit. *)

(** 状态载体与相等层级保持独立。函数空间相等要求两者均不超过所在广集的相等
    层级，而后者可严格小于载体层级。以下接口显式保留这两个所在层级。 *)

Program Definition StateF@{r e u p +} (R : SetC@{r e})
  : Functor (SetCat@{u p _ _ _ _ _}) (SetCat@{u p _ _ _ _ _})
  :=
  {|F0 X := R →S (X ×S R)
  ; F1 X Y f := state_map f
  |}.
Next Obligation.
  intros f g H k r. split; [exact (H (fst (k r))) | reflexivity].
Defined.
Next Obligation.
  intros k r. cbn. destruct (k r). split; reflexivity.
Defined.
Next Obligation. intros k r. split; reflexivity. Defined.

(** Return a value without changing the state. *)

(** 返回一个值，不改变状态。 *)

Program Definition state_pure (R X : SetC)
  : X →r (R →S (X ×S R))
  :=
  {|func x := {|func r := (x, r)|}
  |}.
Next Obligation. intros r r' H. split; [reflexivity | exact H]. Defined.
Next Obligation. intros x x' H r. split; [exact H | reflexivity]. Defined.

(** Flatten two stateful layers, passing the outer state to the inner one. *)

(** 压平两层状态计算，将外层状态传入内层。 *)

Program Definition state_join (R X : SetC)
  : (R →S ((R →S (X ×S R)) ×S R)) →r (R →S (X ×S R))
  :=
  {|func k := {|func r := fst (k r) (snd (k r))|}
  |}.
Next Obligation.
  intros r r' H. cbn in *. pose proof (@func_proper _ _ k r r' H) as K.
  destruct (k r) as [v s], (k r') as [v' s']. cbn in K |-.
  destruct K as [Hv Hs]. transitivity (v' s).
  - exact (Hv s).
  - apply func_proper. exact Hs.
Defined.
Next Obligation.
  intros k k' H r. cbn in *. specialize (H r).
  destruct (k r) as [v s], (k' r) as [v' s']. cbn in H |-.
  destruct H as [Hv Hs]. transitivity (v' s).
  - exact (Hv s).
  - apply func_proper. exact Hs.
Defined.

(** Stateful return is natural in its ordinary result type. *)

(** 状态返回在通常结果类型上自然。 *)

Program Definition StatePureN@{r e u p +} (R : SetC@{r e})
  : IdF ⇒ StateF@{r e u p _ _ _ _} R
  :=
  {|nt X := state_pure R X
  |}.
Next Obligation. intros x r. split; reflexivity. Defined.

(** Stateful flattening is natural in its ordinary result type. *)

(** 状态压平在通常结果类型上自然。 *)

Program Definition StateJoinN@{r e u p +} (R : SetC@{r e})
  : (StateF@{r e u p _ _ _ _} R ∘F
      StateF R) ⇒ StateF R
  :=
  {|nt X := state_join R X
  |}.
Next Obligation. intros k r. split; reflexivity. Defined.

(** Explicitly choose the ordinary state monad. *)

(** 显式选择普通状态 Monad。 *)

Program Definition StateM@{r e u p +} (R : SetC@{r e})
  : Monad (SetCat@{u p _ _ _ _ _})
  :=
  {|MonadF := StateF R
  ; monad_unit := StatePureN R
  ; monad_mul := StateJoinN R
  |}.
Next Obligation.
  split; [intros X k r | split; intros X k r].
  - cbn. destruct (k r). split; reflexivity.
  - change (R →r (X ×S R)) in k.
    change (@carrier_equiv (X ×S R) (fst (k r), snd (k r)) (k r)).
    destruct (k r). split; reflexivity.
  - reflexivity.
Defined.

(** Carry an ordinary context value through a stateful computation. *)

(** 将通常上下文值穿过状态计算。 *)

Program Definition state_strength (R X Y : SetC)
  : (X ×S (R →S (Y ×S R))) →r (R →S ((X ×S Y) ×S R))
  :=
  {|func p := {|func r := ((fst p, fst (snd p r)), snd (snd p r))|}
  |}.
Next Obligation.
  intros r r' H. cbn in *. pose proof (@func_proper _ _ (snd p) r r' H) as K.
  destruct (snd p r) as [y s], (snd p r') as [y' s']. cbn in K |-.
  destruct K as [Hy Hs].
  split; [split; [reflexivity | exact Hy] | exact Hs].
Defined.
Next Obligation.
  intros [x k] [x' k'] [Hx Hk] r. cbn in *. specialize (Hk r).
  destruct (k r) as [y s], (k' r) as [y' s']. cbn in Hk |-.
  destruct Hk as [Hy Hs].
  split; [split; [exact Hx | exact Hy] | exact Hs].
Defined.

(** Stateful strength is natural in both context and result. *)

(** 状态强度在上下文及结果上均自然。 *)

Program Definition StateStrengthN@{r e u p +} (R : SetC@{r e})
  : (tensorF SetCartesianMonoidal ∘F
      (IdF ×F StateF@{r e u p _ _ _ _} R)) ⇒
      (StateF R ∘F tensorF SetCartesianMonoidal)
  :=
  {|nt p := state_strength R (fst p) (snd p)
  |}.
Next Obligation.
  destruct X as [X1 X2], Y as [Y1 Y2], f as [f g].
  intros [x k] r. cbn.
  split; [split; reflexivity | reflexivity].
Defined.

(** Explicitly choose coherent strength for the state functor. *)

(** 显式选择状态函子的相干强度。 *)

Program Definition StateStrength@{r e u p +} (R : SetC@{r e})
  : @HasStrength (SetCat@{u p _ _ _ _ _}) SetCartesianMonoidal (StateF R)
  :=
  {|strengthN := StateStrengthN R
  |}.
Next Obligation.
  intros [[] k] r. cbn. destruct (k r). split; reflexivity.
Defined.
Next Obligation.
  intros [[x y] k] r. cbn. split; [split; [reflexivity | split; reflexivity] |
    reflexivity].
Defined.

(** Return and flattening preserve this chosen state strength. *)

(** 返回及压平保持此选定状态强度。 *)

Program Definition StateStrongM@{r e u p +} (R : SetC@{r e})
  : StrongMonad (SetCat@{u p _ _ _ _ _}) SetCartesianMonoidal
  :=
  {|StrongMonadM := StateM R
  ; hasStrength := StateStrength R
  |}.
Next Obligation.
  intros [x y] r. cbn. split; [split; reflexivity | reflexivity].
Defined.
Next Obligation.
  intros [x k] r. cbn. split; [split; reflexivity | reflexivity].
Defined.

(** Derive the lawful state Applicative using the general conversion.
    This sequences the left state transition before the right. *)

(** 通过一般转换导出带定律的状态 Applicative；先运行左状态转移，再运行右侧。 *)

Definition StateA@{r e u p +} (R : SetC@{r e})
  : Applicative (SetCat@{u p _ _ _ _ _})
      SetCat_HasTerminal SetCat_HasProduct
  := MonadA (StateStrongM R).

(** Derive the state Arrow from the same chosen strong Monad. Its
    context action is inherited from the general monoidal construction. *)

(** 从同一个选定强 Monad 导出状态 Arrow，上下文作用继承自一般幺半构造。 *)

Definition StateArrow@{r e u p +} (R : SetC@{r e})
  : Arrow (SetCat@{u p _ _ _ _ _}) (KleisliCat (StateM R))
      SetCartesianMonoidal
  := KleisliArrow (StateStrongM R).
