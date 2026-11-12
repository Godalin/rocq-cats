From Cats Require Export STLC.KripkeSemantics.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.Lift
  Instance.Set.Kripke.

(** * Reflection and Reification

    Reflection interprets a neutral term as a value. Reification observes
    a value as a beta-normal, eta-long tree. Both must respect equality and
    commute with renaming. We construct these operations and laws together
    by recursion on the simple type, so the arrow reflection can use the
    already constructed domain reification and its coherence laws.

    A function value is reified by entering the context extended by its
    domain, reflecting the newest variable, applying the value in that
    future world and reifying the result. No arbitrary term evaluation or
    small-step reduction is used here. *)

(** * 反射与实化

    反射将中性项解释为值，实化将值观察为 β 正规且 η 长的语法树。二者都须
    保持相等并与重命名交换。这里沿简单类型同时构造操作与定律，使箭头反射
    可以使用已经构造的定义域实化及其相容律。

    实化函数值时，进入按其定义域扩张的上下文，反射最新变量，在该未来世界
    应用函数值，再实化结果。此处不使用任意项的求值或小步归约。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_tm_scope.

(** A pair of operations with their equality and context coherence laws.
    The semantic presheaf is a parameter, not a second presheaf interface.
    The two competing function views remain explicit. *)

(** 一对操作及其相等与上下文相容律。语义预层是参数，不另建预层接口；两种
    函数观察方式均保持显式。 *)

Record Reification {B : Type} (A : Ty B)
    (S : Functor ((RenamingCat B)^op) SetCat)
  :=
  { reflect_ne : ∀ Γ : Ctx B, Ne Γ A → S Γ
  ; reify_sem : ∀ Γ : Ctx B, S Γ → Nf Γ A
  ; reflect_ne_proper Γ :: Proper (eq ==> [≈S]) (reflect_ne Γ)
  ; reify_sem_proper Γ :: Proper ([≈S] ==> eq) (reify_sem Γ)
  ; reflect_ne_rename
      : ∀ (Γ Δ : Ctx B) (ρ : Ren Δ Γ) (n : Ne Γ A),
        fmap S ρ (reflect_ne Γ n) ≈S reflect_ne Δ (n⟨ρ⟩ne)
  ; reify_sem_rename
      : ∀ (Γ Δ : Ctx B) (ρ : Ren Δ Γ) (v : S Γ),
        reify_sem Δ (fmap S ρ v) = (reify_sem Γ v)⟨ρ⟩nf
  }.

Arguments reflect_ne {_ _ _} _ _ _.
Arguments reify_sem {_ _ _} _ _ _.
Arguments reflect_ne_proper {_ _ _} _ _ _ _ _.
Arguments reify_sem_proper {_ _ _} _ _ _ _ _.
Arguments reflect_ne_rename {_ _ _} _ _ _ _ _.
Arguments reify_sem_rename {_ _ _} _ _ _ _ _.

(** Lift any reflection/reification pair to independently larger carrier
    and equality universes. Reification removes the outer wrapper, and all
    coherence laws are inherited without comparing their witnesses. *)

(** 将任意反射/实化对提升到各自更大的载体与相等宇宙。实化去除外层包装，
    全部相容律直接继承，不比较其见证。 *)

Definition lift_reification@{u p +} {B : Type} {A : Ty B}
    {S : Functor ((RenamingCat B)^op) SetCat} (R : Reification A S)
  : Reification A
      (LiftF ∘F S : Functor ((RenamingCat B)^op)
        SetCat@{u p _ _ _ _ _}).
Proof.
  unshelve notypeclasses refine
    {|reflect_ne := _
    ; reify_sem := _
    ; reflect_ne_proper := _
    ; reify_sem_proper := _
    ; reflect_ne_rename := _
    ; reify_sem_rename := _
    |}.
  - intros Γ n. exact {|lower := reflect_ne R Γ n
                       |}.
  - intros Γ v. exact (reify_sem R Γ (lower v)).
  - intros Γ n m h. exact {|lower := reflect_ne_proper R Γ n m h
                           |}.
  - intros Γ [v] [w] [h]. exact (reify_sem_proper R Γ v w h).
  - intros Γ Δ ρ n. exact {|lower := reflect_ne_rename R Γ Δ ρ n
                           |}.
  - intros Γ Δ ρ [v]. exact (reify_sem_rename R Γ Δ ρ v).
Defined.

(** Reflection as a natural transformation from lifted neutral syntax.
    The ambient value carrier must contain the syntax carrier. The pair's
    existing respectfulness and renaming law supply all obligations. *)

(** 从提升后中性语法出发的反射自然变换。值载体的环境界限须容纳语法载体；
    全部证明义务由操作对已有的保相等性质与重命名律提供。 *)

Program Definition ReflectN@{b r u p l +} {B : Type@{b}} {A : Ty B}
    {S : Functor ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{u p _ _ _ _ _}} (R : Reification A S)
  : LiftF ∘F NePsh A ⇒ S
  :=
  {|nt Γ :=
     {|func n := reflect_ne R Γ (lower n)
     |}
  |}.
Next Obligation.
  intros [n] [m] [h]. apply reflect_ne_proper. exact h.
Defined.
Next Obligation.
  intros [n]. symmetry. apply reflect_ne_rename.
Defined.

(** Reification as a natural transformation to lifted normal syntax.
    The returned wrapper retains a normal tree at the original signature
    universe; it is removed by [lower]. *)

(** 到提升后正规语法的实化自然变换。返回的包装保留原签名宇宙中的正规树，
    可通过 [lower] 取出。 *)

Program Definition ReifyN@{b r u p l +} {B : Type@{b}} {A : Ty B}
    {S : Functor ((RenamingCat B : Cat@{b b r l l})^op)
      SetCat@{u p _ _ _ _ _}} (R : Reification A S)
  : S ⇒ LiftF ∘F NfPsh A
  :=
  {|nt Γ :=
     {|func v := {|lower := reify_sem R Γ v
                 |}
     |}
  |}.
Next Obligation.
  intros v w h. refine {|lower := _
                        |}. apply reify_sem_proper. exact h.
Defined.
Next Obligation.
  intros v. refine {|lower := _
                    |}. apply reify_sem_rename.
Defined.

(** Reflect a neutral function using the domain and codomain operations.
    The argument is reified before forming a blocked application. Its
    reindexing coherence follows from the two smaller-type coherence laws. *)

(** 使用定义域与余域操作反射中性函数。形成被阻塞应用前先实化实参，其重索引
    相容性来自两个较小类型处的相容律。 *)

Definition reflect_function_value {B : Type} (A U : Ty B)
    (RA : Reification A (SemF A)) (RU : Reification U (SemF U))
    (Γ : Ctx B) (n : Ne Γ (A ⇒ U))
  : SemF (A ⇒ U) Γ.
Proof.
  unshelve notypeclasses refine
    {|kripke_apply := _
    ; kripke_apply_proper := _
    ; kripke_naturality := _
    |}.
  - intros Δ ρ x.
    exact (reflect_ne RU Δ (ne_app (n⟨ρ⟩ne) (reify_sem RA Δ x))).
  - intros Δ ρ τ h x y k. apply reflect_ne_proper.
    rewrite (rename_ne_ext n ρ τ h).
    rewrite (reify_sem_proper RA Δ x y k). reflexivity.
  - intros Δ Θ ρ τ x.
    etransitivity; [apply reflect_ne_rename |].
    apply reflect_ne_proper. cbn.
    rewrite rename_ne_comp, <- reify_sem_rename. reflexivity.
Defined.

(** Fix the signature, world equality, semantic and world-law bounds
    once for this construction and its laws. Section-local references
    inherit those bindings, so they need no repeated universe instances.
    The semantic bound [s] and world-law bound [l] remain independent. *)

(** 为本构造及其定律一次固定签名、世界相等、语义与世界定律界限。节内引用
    继承这些绑定，无须反复写宇宙实例；语义界限 [s] 与世界定律界限 [l] 仍
    相互独立。 *)

Section TypeDirected.
Universes b r s l.
Context {B : Type@{b}}.

(** Type-directed construction. At base types lift wrappers carry neutral
    syntax; at products the operations act componentwise; the arrow case
    builds the existing coherent Kripke function record. *)

(** 类型导向构造。基类型处的提升包装保存中性语法，积类型逐分量作用，箭头
    情形构造既有的相容 Kripke 函数记录。 *)

Fixpoint TypeReification (A : Ty B)
  : Reification A
      (SemF A : Functor ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{s s _ _ _ _ _}).
Proof.
  destruct A as [b | | A U | A U].
  - unshelve notypeclasses refine
      {|reflect_ne := _
      ; reify_sem := _
      ; reflect_ne_proper := _
      ; reify_sem_proper := _
      ; reflect_ne_rename := _
      ; reify_sem_rename := _
      |}.
    + intros Γ n. exact {|lower := n
                         |}.
    + intros Γ v. exact (nf_base (lower v)).
    + intros Γ n m h. exact {|lower := h
                             |}.
    + intros Γ [n] [m] [h]. cbn in h |- *. now rewrite h.
    + intros Γ Δ ρ n. exact {|lower := reflexivity _
                             |}.
    + intros Γ Δ ρ [n]. reflexivity.
  - unshelve notypeclasses refine
      {|reflect_ne := _
      ; reify_sem := _
      ; reflect_ne_proper := _
      ; reify_sem_proper := _
      ; reflect_ne_rename := _
      ; reify_sem_rename := _
      |}.
    + intros Γ n. exact tt.
    + intros Γ v. exact nf_unit.
    + intros Γ n m h. exact tt.
    + intros Γ v w h. reflexivity.
    + intros Γ Δ ρ n. exact tt.
    + intros Γ Δ ρ v. reflexivity.
  - pose (RA := TypeReification A).
    pose (RU := TypeReification U).
    unshelve notypeclasses refine
      {|reflect_ne := _
      ; reify_sem := _
      ; reflect_ne_proper := _
      ; reify_sem_proper := _
      ; reflect_ne_rename := _
      ; reify_sem_rename := _
      |}.
    + intros Γ n.
      exact (reflect_ne RA Γ (ne_fst n), reflect_ne RU Γ (ne_snd n)).
    + intros Γ v.
      exact (nf_pair (reify_sem RA Γ (fst v)) (reify_sem RU Γ (snd v))).
    + intros Γ n m h. destruct h. split; reflexivity.
    + intros Γ [v w] [v' w'] [h k]. cbn. f_equal.
      * apply reify_sem_proper. exact h.
      * apply reify_sem_proper. exact k.
    + intros Γ Δ ρ n. split.
      * exact (reflect_ne_rename RA Γ Δ ρ (ne_fst n)).
      * exact (reflect_ne_rename RU Γ Δ ρ (ne_snd n)).
    + intros Γ Δ ρ [v w]. cbn. f_equal.
      * exact (reify_sem_rename RA Γ Δ ρ v).
      * exact (reify_sem_rename RU Γ Δ ρ w).
  - pose (RA := TypeReification A).
    pose (RU := TypeReification U).
    pose (rf := reflect_function_value A U RA RU).
    unshelve notypeclasses refine
      {|reflect_ne := _
      ; reify_sem := _
      ; reflect_ne_proper := _
      ; reify_sem_proper := _
      ; reflect_ne_rename := _
      ; reify_sem_rename := _
      |}.
    + exact rf.
    + intros Γ v.
      exact (nf_lam (reify_sem RU (Γ ▻ A)
        (v (Γ ▻ A) wkRen (reflect_ne RA (Γ ▻ A) (ne_var var_zero))))).
    + intros Γ n m h. destruct h. reflexivity.
    + intros Γ v w h. f_equal. apply reify_sem_proper. apply h.
    + intros Γ Δ ρ n Θ τ x. cbn. apply reflect_ne_proper.
      rewrite rename_ne_comp. reflexivity.
    + intros Γ Δ ρ v. cbn. f_equal.
      rewrite <- reify_sem_rename. apply reify_sem_proper.
      symmetry. etransitivity; [apply kripke_naturality |].
      apply kripke_apply_proper.
      * intros T x. reflexivity.
      * exact (reflect_ne_rename RA (Γ ▻ A) (Δ ▻ A)
          (ρ^↑Ren) (ne_var var_zero)).
Defined.

(** Reifying a reflected neutral computes the syntactic type-directed eta
    expansion. This compares normal trees, not semantic function records. *)

(** 实化反射后的中性项，得到语法上的类型导向 η 展开。这里比较正规语法树，
    不比较语义函数记录。 *)

Lemma reify_reflect_eta (A : Ty B)
  : ∀ (Γ : Ctx B) (n : Ne Γ A),
      reify_sem (TypeReification A) Γ
        (reflect_ne (TypeReification A) Γ n) = eta_expand_ne n.
Proof.
  induction A; intros Γ n;
    cbn [TypeReification reflect_ne reify_sem reflect_function_value
      kripke_apply eta_expand_ne].
  - reflexivity.
  - reflexivity.
  - f_equal.
    + exact (IHA1 Γ (ne_fst n)).
    + exact (IHA2 Γ (ne_snd n)).
  - f_equal. rewrite IHA2, IHA1. reflexivity.
Defined.

(** The normal tree obtained from a neutral by reflection and reification
    is beta/eta equal to its input, by the existing syntactic eta theorem.
    Derivation evidence is independently bounded from semantic values.
    This is not yet soundness of normalization for arbitrary raw terms. *)

(** 中性项经过反射与实化所得的正规树，与输入 βη 相等，证明复用既有语法 η
    定理。推导见证的界限独立于语义值；这尚非任意原始项正规化的可靠性。 *)

Definition reify_reflect_sound@{e +} (A : Ty B)
    (Γ : Ctx B) (n : Ne Γ A)
  : TmEq@{b e _} (embed_ne n)
      (embed_nf (reify_sem (TypeReification A) Γ
        (reflect_ne (TypeReification A) Γ n))).
Proof. rewrite reify_reflect_eta. apply eta_expand_ne_sound. Defined.

(** The semantic round trip and syntactic eta expansion also agree as
    natural transformations after the explicit value-universe lift. *)

(** 显式提升值宇宙后，语义往返与语法 η 展开也按自然变换相等。 *)

Definition reification_eta_triangle (A : Ty B)
  : (ReifyN (TypeReification A) ∘Nv
      ReflectN (TypeReification A)) ≈N (LiftF ∘Nl NeutralEtaN A).
Proof.
  intros Γ [n]. refine {|lower := _
                        |}. apply reify_reflect_eta.
Defined.

End TypeDirected.
