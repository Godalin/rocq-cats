From Cats Require Export STLC.Normal.
From Cats.Set Require Export Decision.
From Stdlib Require Import Arith.PeanoNat.

(** * Deciding Equality of Indexed Normal Syntax

    Comparing the current syntax by native equality must account for its
    type indices, including the newest-variable marker. We require an
    explicit decision for base-label equality as a sufficient condition.
    It induces a decision on simple types. The general dependent-fiber
    injection lemma then handles index transport without an extra axiom.
    Contexts stay fixed throughout comparison.

    Comparison uses annotated, unindexed codes. Code equality is ordinary
    structural comparison; a mutual injectivity proof recovers equality
    of the original neutral or normal trees at a fixed context and type. *)

(** * 带索引正规语法的相等判定

    按原生相等比较当前语法时，须处理类型索引，包括最新变量标记。这里以显式
    的基标签相等判定作为充分条件，由它得到简单类型相等判定，再用一般的依赖
    纤维单射引理处理索引输运，不增加公理。比较过程中上下文始终固定。

    比较使用带注解的无索引编码。编码相等按普通结构比较；相互归纳的单射证明
    在固定上下文与类型处恢复原中性树或正规树的相等。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.

(** Base-label decisions extend structurally to simple types. *)

(** 基标签判定沿结构扩张为简单类型判定。 *)

Definition ty_eq_decision {B : Type}
    (d : ∀ p q : B, Decision (p = q)) (A U : Ty B)
  : Decision (A = U).
Proof.
  apply decision_of_sumbool. decide equality.
  apply decision_to_sumbool. apply d.
Defined.

(** Variable rank forgets the type index and counts older declarations. *)

(** 变量位置编号忘却类型索引，按旧声明计数。 *)

Fixpoint var_rank {B : Type} {Γ : Ctx B}
  : ∀ A : Ty B, Var Γ A → nat.
Proof.
  destruct Γ as [| Γ U]; intros A x.
  - destruct x.
  - destruct x as [x | x].
    + exact (S (@var_rank B Γ A x)).
    + exact O.
Defined.

(** Equal ranks identify variables together with their type indices.
    Packing the index is essential: this statement needs no decision on
    labels and makes no assertion that arbitrary index paths are equal. *)

(** 相同编号识别变量及其类型索引。打包索引至关重要：此断言不需要标签判定，
    也不声称任意索引路径相等。 *)

Lemma var_rank_injective {B : Type} (Γ : Ctx B)
  : ∀ (A U : Ty B) (x : Var Γ A) (y : Var Γ U),
      var_rank A x = var_rank U y →
      existT (Var Γ) A x = existT (Var Γ) U y.
Proof.
  induction Γ as [| Γ IH V]; intros A U x y h.
  - destruct x.
  - destruct x as [x | x], y as [y | y]; cbn [var_rank] in h.
    + apply Nat.succ_inj in h.
      exact (f_equal (λ z : sigT (Var Γ),
        existT (Var (Γ ▻ V)) (projT1 z) (var_succ (projT2 z)))
        (IH A U x y h)).
    + discriminate h.
    + discriminate h.
    + destruct x, y. reflexivity.
Defined.

(** Annotation preserves the intermediate types hidden by neutral
    eliminations. Codes contain only simple types, ranks and finite trees;
    they store no equality proofs or semantic functions. *)

(** 注解保留中性消去中隐藏的中间类型。编码只包含简单类型、编号和有限树，
    不保存相等证明或语义函数。 *)

Inductive NormalCode (B : Type)
  : Type
  :=| code_var : Ty B → nat → NormalCode B
    | code_app : Ty B → Ty B → NormalCode B → NormalCode B → NormalCode B
    | code_fst : Ty B → Ty B → NormalCode B → NormalCode B
    | code_snd : Ty B → Ty B → NormalCode B → NormalCode B
    | code_base : B → NormalCode B → NormalCode B
    | code_unit : NormalCode B
    | code_pair : Ty B → Ty B → NormalCode B → NormalCode B → NormalCode B
    | code_lam : Ty B → Ty B → NormalCode B → NormalCode B.

Arguments code_var {_} _ _.
Arguments code_app {_} _ _ _ _.
Arguments code_fst {_} _ _ _.
Arguments code_snd {_} _ _ _.
Arguments code_base {_} _ _.
Arguments code_unit {_}.
Arguments code_pair {_} _ _ _ _.
Arguments code_lam {_} _ _ _.

(** Erase only the dependent indexing discipline, retaining all annotations
    needed to recover the original typed tree. *)

(** 只忘却依赖索引约束，保留恢复原带类型树所需的全部注解。 *)

Fixpoint ne_code {B : Type} {Γ : Ctx B} {A : Ty B} (n : Ne Γ A)
  : NormalCode B
  := match n with
  | @ne_var _ _ A x => code_var A (var_rank A x)
  | @ne_app _ _ A U n v => code_app A U (ne_code n) (nf_code v)
  | @ne_fst _ _ A U n => code_fst A U (ne_code n)
  | @ne_snd _ _ A U n => code_snd A U (ne_code n)
  end
with nf_code {B : Type} {Γ : Ctx B} {A : Ty B} (v : Nf Γ A)
  : NormalCode B
  := match v with
  | @nf_base _ _ p n => code_base p (ne_code n)
  | nf_unit => code_unit
  | @nf_pair _ _ A U v w => code_pair A U (nf_code v) (nf_code w)
  | @nf_lam _ _ A U v => code_lam A U (nf_code v)
  end.

(** Unindexed codes have structural decidable equality under the explicit
    label decision. This comparison does not inspect semantic values. *)

(** 在显式标签判定下，无索引编码的结构相等可判定。此比较不检查语义值。 *)

Definition normal_code_decision {B : Type}
    (d : ∀ p q : B, Decision (p = q)) (c k : NormalCode B)
  : Decision (c = k).
Proof.
  apply decision_of_sumbool. decide equality.
  all: first [apply Nat.eq_dec |
    apply decision_to_sumbool;
      first [apply ty_eq_decision; exact d | apply d]].
Defined.

(** ** Typed Comparison under Decidable Label Equality

    Fix a signature [B] and an explicit native equality decision [d] for
    its labels. Prove code injectivity and derive neutral and normal
    equality decisions at a fixed context and type. *)

(** ** 标签相等可判定时的带类型比较

    固定签名 [B] 与其标签的显式原生相等判定 [d]，证明编码单射性，并在固定
    上下文与类型处导出中性项和正规形的相等判定。 *)

Section Comparison.
Context {B : Type} (d : ∀ p q : B, Decision (p = q)).

(** Equal codes identify typed trees together with their result indices.
    Once annotations align a recursive pair of fibers, their decidable
    type indices let us extract homogeneous equality of the children. *)

(** 相同编码识别带类型树及其结果索引。注解对齐递归的两个纤维后，类型索引
    的可判定相等允许提取子树的同类型相等。 *)

Fixpoint ne_code_injective (Γ : Ctx B) (A : Ty B) (n : Ne Γ A)
  : ∀ (U : Ty B) (m : Ne Γ U), ne_code n = ne_code m →
      existT (Ne Γ) A n = existT (Ne Γ) U m
with nf_code_injective (Γ : Ctx B) (A : Ty B) (v : Nf Γ A)
  : ∀ (U : Ty B) (w : Nf Γ U), nf_code v = nf_code w →
      existT (Nf Γ) A v = existT (Nf Γ) U w.
Proof.
  - destruct n as [Γ A x | Γ A U n v | Γ A U n | Γ A U n];
      intros V m; destruct m as
      [Γ A' y | Γ A' U' m w | Γ A' U' m | Γ A' U' m];
      intros h; cbn [ne_code] in h; try discriminate h.
    + injection h as hA hxy.
      exact (f_equal (λ z : sigT (Var Γ),
        existT (Ne Γ) (projT1 z) (ne_var (projT2 z)))
        (var_rank_injective Γ A A' x y hxy)).
    + injection h as hA hU hn hv. destruct hA, hU.
      pose proof (decidable_fiber_injective (ty_eq_decision d)
        (Ne Γ) (A ⇒ U) n m
        (ne_code_injective Γ (A ⇒ U) n (A ⇒ U) m hn)) as en.
      pose proof (decidable_fiber_injective (ty_eq_decision d)
        (Nf Γ) A v w (nf_code_injective Γ A v A w hv)) as ev.
      destruct en, ev. reflexivity.
    + injection h as hA hU hn. destruct hA, hU.
      pose proof (decidable_fiber_injective (ty_eq_decision d)
        (Ne Γ) (A × U) n m
        (ne_code_injective Γ (A × U) n (A × U) m hn)) as en.
      destruct en. reflexivity.
    + injection h as hA hU hn. destruct hA, hU.
      pose proof (decidable_fiber_injective (ty_eq_decision d)
        (Ne Γ) (A × U) n m
        (ne_code_injective Γ (A × U) n (A × U) m hn)) as en.
      destruct en. reflexivity.
  - destruct v as [Γ p n | Γ | Γ A U v v' | Γ A U v];
      intros V w; destruct w as
      [Γ q m | Γ | Γ A' U' w w' | Γ A' U' w];
      intros h; cbn [nf_code] in h; try discriminate h.
    + injection h as hp hn. destruct hp.
      pose proof (decidable_fiber_injective (ty_eq_decision d)
        (Ne Γ) (ty_base p) n m
        (ne_code_injective Γ (ty_base p) n (ty_base p) m hn)) as en.
      destruct en. reflexivity.
    + reflexivity.
    + injection h as hA hU hv hv'. destruct hA, hU.
      pose proof (decidable_fiber_injective (ty_eq_decision d)
        (Nf Γ) A v w (nf_code_injective Γ A v A w hv)) as ev.
      pose proof (decidable_fiber_injective (ty_eq_decision d)
        (Nf Γ) U v' w' (nf_code_injective Γ U v' U w' hv')) as ev'.
      destruct ev, ev'. reflexivity.
    + injection h as hA hU hv. destruct hA, hU.
      pose proof (decidable_fiber_injective (ty_eq_decision d)
        (Nf (Γ ▻ A)) U v w
        (nf_code_injective (Γ ▻ A) U v U w hv)) as ev.
      destruct ev. reflexivity.
Defined.

(** Decide native equality of neutrals at the same context and type.
    A negative code comparison refutes any possible typed-tree equality. *)

(** 判定同一上下文与类型处中性项的原生相等。编码比较的否定分支反驳任何可能
    的带类型树相等。 *)

Definition ne_eq_decision {Γ : Ctx B} {A : Ty B} (n m : Ne Γ A)
  : Decision (n = m).
Proof.
  destruct (normal_code_decision d (ne_code n) (ne_code m)) as [h | k].
  - left. exact (decidable_fiber_injective (ty_eq_decision d) (Ne Γ) A n m
      (ne_code_injective Γ A n A m h)).
  - right. intros h. exact (k (f_equal ne_code h)).
Defined.

(** Decide native equality of long normal forms under the same explicit
    label hypothesis. This is independent of any evaluation model. *)

(** 在同一个显式标签假设下判定长正规形的原生相等，不依赖求值模型。 *)

Definition nf_eq_decision {Γ : Ctx B} {A : Ty B} (v w : Nf Γ A)
  : Decision (v = w).
Proof.
  destruct (normal_code_decision d (nf_code v) (nf_code w)) as [h | k].
  - left. exact (decidable_fiber_injective (ty_eq_decision d) (Nf Γ) A v w
      (nf_code_injective Γ A v A w h)).
  - right. intros h. exact (k (f_equal nf_code h)).
Defined.

End Comparison.
