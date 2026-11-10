From Cats.Set.Closure Require Import Composition.
From Cats.Instance.Preorder Require Import Closure.
From Cats Require Import Cat.Core.

(** * Closure Interface Regressions

    Separate carrier and witness levels, then check computations where order
    witnesses carry numbers and equivalent objects are not natively equal.
    These tests exercise the abstract interface, rather than a syntax model. *)

(** * 闭包接口回归检查

    先分离载体与见证层级，再检查顺序见证携带数值、等价对象并非原生相等时的
    计算。检查针对抽象接口，不依赖语法模型。 *)

Section SeparatedLevels.
Universes u r.
Constraint u < r.
Context (X : Type@{u}) (R : X → X → Type@{r}).
Context `{HR : !PreOrder R} (c d : Closure R).
Context (h : is_closure_interchange c d).

(** Closure laws and their composite retain the larger witness universe. *)

(** 闭包律及其复合保留较大的见证宇宙。 *)

Definition separated_composite_closure
  : Closure R
  := CompositeClosure c d h.

(** The category of closed objects retains its proof-bearing object data. *)

(** 闭对象范畴保留对象中携带的证明数据。 *)

Definition separated_closed_category
  : Cat
  := ClosedCat c.

(** Reflection and idempotent multiplication work at the same separated
    levels, without resizing the closed-object witnesses. *)

(** 反射与幂等乘法在相同的分离层级工作，不对闭对象见证作大小重设。 *)

Definition separated_closure_adjunction
  := ClosureAdjunction c.
Definition separated_closure_monad_iso (x : X)
  := closure_monad_mul_iso c x.

End SeparatedLevels.

Section ReverseLevels.
Universes u r.
Constraint r < u.
Context (X : Type@{u}) (R : X → X → Type@{r}).
Context `{HR : !PreOrder R} (c : Closure R).

(** The abstract closure interface also permits smaller order witnesses. *)

(** 抽象闭包接口也允许较小的顺序见证。 *)

Definition low_witness_closure_universal {x y : X} (hy : is_closed c y)
  : R (c x) y ↔ R x y
  := closure_universal c hy.
Definition low_witness_closure_reflection
  := ClosureAdjunction c.

End ReverseLevels.

Section WitnessComputation.

(** Every comparison carries a natural-number witness. No antisymmetry or
    equality of parallel witnesses is assumed by this Type-valued preorder. *)

(** 每个比较携带自然数见证。此 Type 值预序不假设反对称性或平行见证相等。 *)

Definition WitnessOrder (_ _ : bool)
  : Type
  := nat.

Local Program Instance witness_order_PreOrder
  : PreOrder WitnessOrder
  :=
  {|PreOrder_Reflexive x := 0
  ; PreOrder_Transitive x y z h k := (h + k)%nat
  |}.

(** Negation is a closure for this preorder, despite not being idempotent
    under native Boolean equality. The laws return observable witness data. *)

(** 布尔取反在此预序上是闭包，尽管它在原生布尔相等下不幂等；定律返回可观察
    的见证数据。 *)

Program Definition WitnessClosure
  : Closure WitnessOrder
  :=
  {|closure_map := negb
  |}.
Next Obligation.
  split; [intros x y h; exact (S h) |].
  split; intros x; [exact 7 | exact 11].
Defined.

(** Extending and restricting comparisons compute through the chosen laws. *)

(** 延拓与限制比较通过选定定律计算。 *)

Example closure_extension_computes
  : closure_extend WitnessClosure (x := true) (y := false) 5 2 = 8.
Proof. reflexivity. Qed.
Example closure_restriction_computes
  : closure_restrict WitnessClosure (x := true) (y := false) 2 = 9.
Proof. reflexivity. Qed.

(** The categorical hom correspondence retains these computations. *)

(** 范畴 Hom 对应保留这些计算。 *)

Example closure_adjunct_computes
  : closure_adjunct_resp WitnessClosure true (false; 5) 2 = 9.
Proof. reflexivity. Qed.
Example closure_unadjunct_computes
  : closure_unadjunct_resp WitnessClosure true (false; 5) 2 = 8.
Proof. reflexivity. Qed.

(** Native idempotence would reject this valid preorder closure. *)

(** 若要求原生幂等性，就会排除此有效的预序闭包。 *)

Example closure_need_not_be_natively_idempotent
  : WitnessClosure (WitnessClosure true) = WitnessClosure true → Empty_set.
Proof. discriminate. Defined.

End WitnessComputation.
