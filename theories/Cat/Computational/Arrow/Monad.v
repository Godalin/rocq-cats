From Cats Require Export
  Cat.Computational.Arrow.Dynamic
  Cat.Monad.Extension.
From Cats Require Import
  Cat.Adjunction
  Cat.Monad.Adjunction
  Instance.Set.Arrow
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Hom
  Cat.Induced.
From Cats.Set Require Import
  Constant.
Import Cats.Cat.Core Cats.Cat.Product.Core.

Local Open Scope computation_scope.
Local Open Scope monad_scope.
Local Existing Instance SetCat_HasTerminal.
Local Existing Instance SetCat_HasProduct.

(** * The Monad of a Dynamic Arrow

    Fix an ArrowApply on native setoids, with independent carrier and
    equality levels. Its pure inclusion into the indexed computation
    category is left adjoint to taking computations from the terminal
    input. Reuse the general adjunction-to-Monad construction; no closed
    structure or new proof of the three Monad laws is needed. *)

(** * 动态 Arrow 的 Monad

    固定原生广集上的 ArrowApply，载体与相等层级保持独立。纯计算到索引计算
    范畴的包含左伴随于取终端输入的计算。复用一般伴随到 Monad 的构造，
    不需要闭结构，也不重新证明三条 Monad 定律。 *)

Section Theory.
Universes o u p.
Context {K : Cat@{o u p _ _}} (AA : ArrowApply K).

(** The dynamic Hom correspondence supplies the adjunction. The existing
    constructor handles size bounds without identifying native Hom levels. *)

(** 动态 Hom 对应给出伴随；已有构造处理大小界，不将原生 Hom 层级等同。 *)

Program Definition ArrowApplyAdj
  : InducedF AA ⊣ (@ℎ1F (ComputationCat AA) UnitS)
  := AdjFromHom (InducedF AA) (@ℎ1F (ComputationCat AA) UnitS)
      (arrow_dynamic_name_resp AA) (arrow_dynamic_eval_resp AA) _ _ _ _.
Next Obligation. exact (arrow_dynamic_eval_name AA f). Defined.
Next Obligation. exact (arrow_dynamic_name_eval AA g). Defined.
Next Obligation. exact (arrow_dynamic_name_pre AA f h). Defined.
Next Obligation. exact (arrow_dynamic_name_post AA f k). Defined.

(** Forward transposition names the supplied computation. *)

(** 正向转置命名所给计算。 *)

Lemma arrow_apply_adjunct {X Y : SetC@{u p}} (f : Hom (AA X) (AA Y))
  : f^♯[ArrowApplyAdj] ≈f arrow_dynamic_name AA f.
Proof. reflexivity. Qed.

(** Inverse transposition dynamically evaluates a value-indexed computation. *)

(** 逆转置动态求值由值索引的计算。 *)

Lemma arrow_apply_unadjunct {X Y : SetC@{u p}}
    (f : X →r ArrowGlobalF AA Y)
  : f^♭[ArrowApplyAdj] ≈ arrow_dynamic_eval AA f.
Proof. reflexivity. Qed.

(** The induced Monad stores exactly the global computations of the Arrow. *)

(** 诱导的 Monad 存储恰好该 Arrow 的全局计算。 *)

Definition ArrowMonad
  : Monad (SetCat@{u p _ _ _ _ _})
  := AdjMonad ArrowApplyAdj.

(** Identity components compare the underlying functor with [ArrowGlobalF],
    without requiring equality of functor structures or their law fields. *)

(** 恒等分量将底层函子与 [ArrowGlobalF] 比较，不要求函子结构或定律字段相等。 *)

Program Definition ArrowMonadUnderlyingIso
  : (ArrowMonad : Fct SetCat SetCat) ≅N ArrowGlobalF AA
  := ({|nt X := id_resp
      |}; _).
Next Obligation. intros m. reflexivity. Defined.
Next Obligation.
  intros X. exists id_resp. split; intros m; reflexivity.
Defined.

(** The induced unit agrees with the existing pure global computation. *)

(** 诱导的单位与已有纯全局计算一致。 *)

Lemma arrow_monad_unit (X : SetC@{u p}) (x : X)
  : η[ArrowMonad] X x ≈ arrow_value_pure K AA X x.
Proof. exact (@comp_id_l K _ _ (arr[AA; const_resp UnitS x])). Qed.

(** Multiplication runs the dynamically returned global computation. *)

(** 乘法运行动态返回的全局计算。 *)

Lemma arrow_monad_mul (X : SetC@{u p})
  : μ[ArrowMonad] X ≈f
      comp_l_resp (C := K) (f := arrow_dynamic_eval AA
        (id_resp (X := ArrowGlobalF AA X))).
Proof. reflexivity. Qed.

(** Extension first runs the input computation, then dynamically evaluates
    the continuation selected by its result. *)

(** 扩张先运行输入计算，再动态求值由其结果选定的续延。 *)

Lemma arrow_monad_extend {X Y : SetC@{u p}}
    (f : X →r ArrowGlobalF AA Y)
  : kleisli_extend ArrowMonad f ≈f
      comp_l_resp (C := K) (f := arrow_dynamic_eval AA f).
Proof.
  intros m.
  change (arrow_dynamic_eval AA (id_resp (X := ArrowGlobalF AA Y)) ∘
    (arr[AA; f] ∘ m) ≈ arrow_dynamic_eval AA f ∘ m).
  rewrite <- comp_assoc. apply comp_proper; [|reflexivity].
  symmetry. exact (unadjunct_counit ArrowApplyAdj f).
Qed.

End Theory.
