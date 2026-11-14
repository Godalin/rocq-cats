From Cats Require Export
  Cat.Monad.Context
  Cat.Applicative.Core.
From Cats Require Import
  Cat.Product.Transport.

Local Open Scope monoidal_scope.
Local Open Scope monad_scope.
Local Open Scope applicative_scope.

(** * Left-to-Right Applicative Sequencing

    A strong monad over the chosen finite products supplies binary
    combination. The left computation runs before the right; no
    commutativity or exponential objects are required. *)

(** * 从左到右的 Applicative 顺序组合

    选定有限积上的强 Monad 提供二元组合。先运行左侧计算，再运行右侧计算；
    不要求交换性或指数对象。 *)

Section Applicative.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (M : StrongMonad C (@CartesianMonoidal C HT HP)).

(** Bind the left input, then the right, and return their ordinary pair. *)

(** 绑定左输入，再绑定右输入，最后返回它们的通常配对。 *)

Definition monad_pair {X Y : @Ob C}
  : Hom (M X × M Y) (M (X × Y)%ob)
  := bind[M; π1;
      bind[M; π2 ∘ π1; return[M; ⟨π2 ∘ π1, π2⟩]]].

(** Use the proved equations while keeping computational bodies abstract.
    Transparency is restored before leaving this module. *)

(** 使用已证方程时暂将计算体视为抽象操作，在离开本模块前恢复透明性。 *)

Local Opaque context_bind monad_return.

(** Ordered pairing is natural in both ordinary result types. *)

(** 有序配对在两个通常结果类型上自然。 *)

Lemma monad_pair_natural {X X' Y Y' : @Ob C}
    (f : Hom X X') (g : Hom Y Y')
  : monad_pair ∘ (fmap M f × fmap M g) ≈
      fmap M (f × g) ∘ monad_pair.
Proof.
  unfold monad_pair.
  monad_context_simpl M. reflexivity.
Qed.

(** Pairing in a shared context runs the first projection before the second.
    Keeping this equation explicit avoids unfolding computations stored in
    an ordinary context while proving associativity. *)

(** 共同上下文中的配对先运行第一投影，再运行第二投影。显式保留此方程，
    可在证明结合律时避免展开存于通常上下文中的计算。 *)

Lemma monad_pair_pre {W X Y : @Ob C} (p : Hom W (M X × M Y))
  : monad_pair ∘ p ≈ bind[M; π1 ∘ p;
      bind[M; π2 ∘ p ∘ π1; return[M; ⟨π2 ∘ π1, π2⟩]]].
Proof. unfold monad_pair. monad_context_simpl M. reflexivity. Qed.

Local Ltac normalize_pairing :=
  repeat first
    [ progress monad_context_simpl M
    | match goal with
      | |- context [context_bind M ((@monad_pair ?A ?B) ∘ ?p) ?k] =>
          rewrite (monad_pair_pre (X := A) (Y := B) p)
      end ].

(** The tensorator packages natural ordered pairing. *)

(** tensorator 打包自然的有序配对。 *)

Program Definition MonadTensorN
  : (tensorF (@CartesianMonoidal C HT HP) ∘F (M ×F M)) ⇒
      (M ∘F tensorF (@CartesianMonoidal C HT HP))
  :=
  {|nt p := @monad_pair (fst p) (snd p)
  |}.
Next Obligation.
  destruct X as [X1 X2], Y as [Y1 Y2], f as [f g].
  rewrite (@cartesian_tensor_map C HT HP _ _ _ _ (fmap M f) (fmap M g)),
    (@cartesian_tensor_map C HT HP _ _ _ _ f g).
  exact (monad_pair_natural f g).
Defined.

(** Monad return at the terminal object and ordered pairing form a lax
    monoidal endofunctor. The proof retains the sequencing order. *)

(** 终对象处的 Monad 返回及有序配对组成 lax 幺半自函子，证明保留求值次序。 *)

Program Definition MonadLax
  : LaxMonoidalFct (@CartesianMonoidal C HT HP)
      (@CartesianMonoidal C HT HP)
  :=
  {|LaxMonoidalF := M
  ; lax_unit := monad_return M (@id 1)
  ; lax_tensorN := MonadTensorN
  |}.
Next Obligation.
  change (fmap M (π2 : Hom (1 × X) X) ∘ monad_pair ∘
    (@tensor_map C (@CartesianMonoidal C HT HP) _ _ _ _
      (monad_return M (@id 1)) (@id (M X))) ≈ π2).
  rewrite cartesian_tensor_map.
  change (fmap M (π2 : Hom (1 × X) X) ∘ monad_pair ∘
    (monad_return M (@id 1) × id) ≈ π2).
  unfold monad_pair. monad_context_simpl M. reflexivity.
Defined.
Next Obligation.
  change (fmap M (π1 : Hom (X × 1) X) ∘ monad_pair ∘
    (@tensor_map C (@CartesianMonoidal C HT HP) _ _ _ _
      (@id (M X)) (monad_return M (@id 1))) ≈ π1).
  rewrite cartesian_tensor_map.
  change (fmap M (π1 : Hom (X × 1) X) ∘ monad_pair ∘
    (id × monad_return M (@id 1)) ≈ π1).
  unfold monad_pair. monad_context_simpl M. reflexivity.
Defined.
Local Opaque monad_pair.
Next Obligation.
  change (fmap M (@product_assoc C HP X Y Z).1 ∘ monad_pair ∘
    (@tensor_map C (@CartesianMonoidal C HT HP) _ _ _ _
      (@monad_pair X Y) (@id (M Z))) ≈ monad_pair ∘
    (@tensor_map C (@CartesianMonoidal C HT HP) _ _ _ _
      (@id (M X)) (@monad_pair Y Z)) ∘
    (@product_assoc C HP (M X) (M Y) (M Z)).1).
  rewrite !cartesian_tensor_map.
  change (fmap M (@product_assoc C HP X Y Z).1 ∘ monad_pair ∘
    (monad_pair × id) ≈ monad_pair ∘ (id × monad_pair) ∘
      (@product_assoc C HP (M X) (M Y) (M Z)).1).
  rewrite !comp_assoc,
    (monad_pair_pre (X := (X × Y)%ob) (Y := Z)
      ((@monad_pair X Y) × @id (M Z))),
    (monad_pair_pre (X := X) (Y := (Y × Z)%ob)
      ((@id (M X) × @monad_pair Y Z) ∘
        (@product_assoc C HP (M X) (M Y) (M Z)).1)).
  unfold product_assoc. cbn. normalize_pairing.
  unfold product_assoc. cbn. monad_context_simpl M. reflexivity.
Defined.

Local Transparent monad_pair.

(** The induced Applicative retains the original functor and return. *)

(** 诱导的 Applicative 保留原函子及返回运算。 *)

Program Definition MonadA
  : Applicative C HT HP
  :=
  {|ApplicativeLax := MonadLax
  ; applicative_pure := η[M]
  |}.
Next Obligation. symmetry. apply monad_return_id. Defined.
Next Obligation.
  change (η[M] (X × Y)%ob ≈ monad_pair ∘ (η[M] X × η[M] Y)).
  rewrite <- (monad_return_id M (X × Y)%ob),
    <- (monad_return_id M X), <- (monad_return_id M Y).
  unfold monad_pair. monad_context_simpl M. reflexivity.
Defined.

(** The induced pure operation is precisely the monad unit. *)

(** 诱导的纯值运算恰为 Monad 单位。 *)

Lemma monad_applicative_pure (X : @Ob C)
  : pure[MonadA] X ≈ η[M] X.
Proof. reflexivity. Qed.

(** The induced tensorator is the specified left-to-right pairing. *)

(** 诱导的 tensorator 为指定的从左到右配对。 *)

Lemma monad_applicative_pair (X Y : @Ob C)
  : φ₂[MonadA; X; Y] ≈ @monad_pair X Y.
Proof. reflexivity. Qed.

Local Transparent context_bind monad_return.

End Applicative.
