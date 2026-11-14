From Cats Require Export
  Cat.Applicative.Core.
From Cats Require Import
  Cat.Product.Transport.

Local Open Scope monoidal_scope.
Local Open Scope applicative_scope.

(** * Coherent Binary-Lifting Operations

    This presentation supplies operations independently of a lax monoidal
    structure. Its equations are equations of arrows, so they hold after
    every context substitution. No exponential or well-pointedness is used. *)

(** * 相干二元提升运算

    此呈现独立给出运算，不预先给定 lax 幺半结构。定律为态射方程，因此在每个
    上下文替换后成立；不使用指数或良点性。 *)

(** Laws on a specified functor, pure map and binary lifting. The
    associativity law permits different intermediate result types and
    retains the source equation as Type-valued input. *)

(** 指定函子、纯值映射及二元提升上的定律。结合律允许不同的中间结果类型，
    并将来源方程作为 Type 值输入保留。 *)

Class IsApplicativeOps {C : Cat} (HT : HasTerminal C) (HP : HasProduct C)
    (F : Fct C C) (pure : IdF ⇒ F)
    (lift : ∀ {X Y Z : @Ob C}, Hom (@Prod C HP X Y) Z →
      Hom (@Prod C HP (F X) (F Y)) (F Z))
  :=
  (** Lifting preserves the specified equality of operations. *)

  (** 提升保持运算的指定相等。 *)

  { ops_proper {X Y Z : @Ob C}
      :: Proper (HomEq ==> HomEq) (@lift X Y Z)

  (** Ordinary maps on results commute with lifting. *)

  (** 结果上的通常映射与提升交换。 *)

  ; ops_post {X Y Z W : @Ob C}
      (f : Hom (@Prod C HP X Y) Z) (g : Hom Z W)
    : fmap F g ∘ lift f ≈ lift (g ∘ f)

  (** Ordinary maps on both inputs can be substituted before lifting. *)

  (** 两个输入上的通常映射可在提升之前代入。 *)

  ; ops_pre {X Y X' Y' Z : @Ob C}
      (f : Hom (@Prod C HP X' Y') Z) (g : Hom X X') (h : Hom Y Y')
    : lift f ∘ (@cross C HP _ _ _ _ (fmap F g) (fmap F h)) ≈
        lift (f ∘ (@cross C HP _ _ _ _ g h))

  (** Lifting two pure inputs agrees with pure ordinary evaluation. *)

  (** 两个纯输入的提升，等于通常求值的纯值。 *)

  ; ops_pure {X Y Z : @Ob C} (f : Hom (@Prod C HP X Y) Z)
    : lift f ∘ (@cross C HP _ _ _ _ (pure X) (pure Y)) ≈ pure Z ∘ f

  (** A pure terminal input on the left is neutral. *)

  (** 左侧纯终输入为中性输入。 *)

  ; ops_unit_l (X : @Ob C)
    : lift (@Cats.Cat.Product.Core.π2 C HP (@Term C HT) X) ∘
        (@cross C HP _ _ _ _ (pure (@Term C HT)) id) ≈ π2

  (** A pure terminal input on the right is neutral. *)

  (** 右侧纯终输入为中性输入。 *)

  ; ops_unit_r (X : @Ob C)
    : lift (@Cats.Cat.Product.Core.π1 C HP X (@Term C HT)) ∘
        (@cross C HP _ _ _ _ id (pure (@Term C HT))) ≈ π1

  (** Every associativity diagram of ordinary operations is preserved. *)

  (** 通常运算的每个结合图都被保持。 *)

  ; ops_assoc {X Y Z U V T : @Ob C}
      (f : Hom (@Prod C HP X Y) U)
      (g : Hom (@Prod C HP U Z) T)
      (h : Hom (@Prod C HP Y Z) V)
      (k : Hom (@Prod C HP X V) T)
      (H : g ∘ (@cross C HP _ _ _ _ f id) ≈
        k ∘ (@cross C HP _ _ _ _ id h) ∘
          (@product_assoc C HP X Y Z).1)
    : lift g ∘ (@cross C HP _ _ _ _ (lift f) id) ≈
        lift k ∘ (@cross C HP _ _ _ _ id (lift h)) ∘
          (@product_assoc C HP (F X) (F Y) (F Z)).1
  }.

(** Pointwise equality of liftings transports the laws on fixed data.
    No equality of functions or proof fields is needed. *)

(** 提升的逐点相等可运输固定数据上的定律，不要求函数或证明字段相等。 *)

Program Definition applicative_ops_transport {C : Cat}
    {HT : HasTerminal C} {HP : HasProduct C}
    {F : Fct C C} {pure : IdF ⇒ F}
    {b c : ∀ {X Y Z : @Ob C}, Hom (@Prod C HP X Y) Z →
      Hom (@Prod C HP (F X) (F Y)) (F Z)}
    (B : IsApplicativeOps HT HP F pure (@b))
    (E : ∀ {X Y Z : @Ob C} (f : Hom (@Prod C HP X Y) Z), b f ≈ c f)
  : IsApplicativeOps HT HP F pure (@c)
  :=
  {|ops_proper := _
  ; ops_post := _
  ; ops_pre := _
  ; ops_pure := _
  ; ops_unit_l := _
  ; ops_unit_r := _
  ; ops_assoc := _
  |}.
Next Obligation.
  intros f g H. rewrite <- (E _ _ _ f), <- (E _ _ _ g).
  exact (ops_proper (IsApplicativeOps := B) _ _ H).
Defined.
Next Obligation.
  rewrite <- (E _ _ _ f), <- (E _ _ _ (g ∘ f)).
  exact (ops_post (IsApplicativeOps := B) f g).
Defined.
Next Obligation.
  rewrite <- (E _ _ _ f), <- (E _ _ _ (f ∘ (@cross C HP _ _ _ _ g h))).
  exact (ops_pre (IsApplicativeOps := B) f g h).
Defined.
Next Obligation.
  rewrite <- (E _ _ _ f). exact (ops_pure (IsApplicativeOps := B) f).
Defined.
Next Obligation.
  rewrite <- E. exact (ops_unit_l (IsApplicativeOps := B) X).
Defined.
Next Obligation.
  rewrite <- E. exact (ops_unit_r (IsApplicativeOps := B) X).
Defined.
Next Obligation.
  rewrite <- (E _ _ _ f), <- (E _ _ _ g), <- (E _ _ _ h), <- (E _ _ _ k).
  exact (ops_assoc (IsApplicativeOps := B) f g h k H).
Defined.

(** An endofunctor and its coherent pure/binary operations. The single
    underlying view is the functor; no tensorator is stored here. *)

(** 自函子及其相干纯值／二元运算。唯一底层视图为函子，此处不存储 tensorator。 *)

Class ApplicativeOps (C : Cat) (HT : HasTerminal C) (HP : HasProduct C)
  :=
  (** The only coercion exposes the specified endofunctor. *)

  (** 唯一强制转换暴露指定自函子。 *)

  { OpsF :> Fct C C

  (** Pure embedding is natural, including for non-global contextual values. *)

  (** 纯值嵌入自然，也适用于非全局的上下文值。 *)

  ; operations_pure : IdF ⇒ OpsF

  (** Lift each binary arrow without assuming a structural tensorator. *)

  (** 提升每个二元箭头，不预设结构式 tensorator。 *)

  ; operations_lift {X Y Z : @Ob C}
      : Hom (@Prod C HP X Y) Z → Hom (@Prod C HP (OpsF X) (OpsF Y)) (OpsF Z)

  (** The fixed operations satisfy the stated coherence diagrams. *)

  (** 固定运算满足给出的相干图。 *)

  ; operations_laws
      :: IsApplicativeOps HT HP OpsF operations_pure (@operations_lift)
  }.

Arguments OpsF {_ _ _} _.
Arguments operations_pure {_ _ _} _.
Arguments operations_lift {_ _ _} _ {_ _ _} _.
Arguments operations_laws {_ _ _} _.

Notation "'pureᵒ[' O ']'" := (operations_pure O) : applicative_scope.
Notation "'lift₂ᵒ[' O ';' f ']'" := (operations_lift O f)
  : applicative_scope.

(** Respectfulness for the bundled operation has an explicit owner,
    avoiding inference of an unrelated pure map during setoid rewriting. *)

(** 打包运算的保相等性显式指定归属，避免广集重写时推断无关的纯值映射。 *)

Global Instance operations_lift_proper {C : Cat}
    {HT : HasTerminal C} {HP : HasProduct C}
    (O : ApplicativeOps C HT HP) {X Y Z : @Ob C}
  : Proper (HomEq ==> HomEq) (@operations_lift C HT HP O X Y Z).
Proof. exact (ops_proper (IsApplicativeOps := operations_laws O)). Qed.

(** The existing generic lax-lifting proofs supply all operation laws. *)

(** 已有的一般 lax 提升证明提供全部运算定律。 *)

Program Definition applicative_operations_laws {C : Cat}
    {HT : HasTerminal C} {HP : HasProduct C} (A : Applicative C HT HP)
  : IsApplicativeOps HT HP A (pure[A]) (@lax_lift2 _ _ _ _ A)
  :=
  {|ops_proper X Y Z := lax_lift2_proper A
  ; ops_post X Y Z W f g := lax_lift2_post A f g
  ; ops_pre X Y X' Y' Z f g h := cartesian_lift2_pre A f g h
  ; ops_pure X Y Z f := applicative_lift2_pure A f
  ; ops_unit_l X := applicative_unit_l A X
  ; ops_unit_r X := applicative_unit_r A X
  ; ops_assoc X Y Z U V T f g h k H := cartesian_lift2_assoc A f g h k H
  |}.

(** Forget the structural packaging while keeping its functor and operations. *)

(** 忘却结构包装，保持其函子及运算。 *)

Program Definition ApplicativeOperations {C : Cat}
    {HT : HasTerminal C} {HP : HasProduct C} (A : Applicative C HT HP)
  : ApplicativeOps C HT HP
  :=
  {|OpsF := A
  ; operations_pure := pure[A]
  ; operations_lift := @lax_lift2 _ _ _ _ A
  ; operations_laws := applicative_operations_laws A
  |}.

(** ** Reconstructing the Structural Applicative

    Fix coherent pure and binary operations over selected finite products.
    Reconstruct their tensorator, lax structure and Applicative bundle. *)

(** ** 重建结构式 Applicative

    固定选定有限积上的相干纯值与二元运算，重建 tensorator、lax 结构及 Applicative 包。 *)

Section Reconstruction.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (O : ApplicativeOps C HT HP).
Local Existing Instance O.

(** Result naturality determines every lifting from the lifted pairing
    operation, the identity on the chosen product. *)

(** 结果自然性使每个提升都由配对运算的提升确定；配对运算即选定积上的恒等。 *)

Lemma operations_lift_pair {X Y Z : @Ob C} (f : Hom (X × Y) Z)
  : lift₂ᵒ[O; f] ≈ fmap O f ∘ lift₂ᵒ[O; (@id (X × Y))].
Proof.
  pose proof (ops_post (IsApplicativeOps := operations_laws O) id f) as H.
  rewrite comp_id_r in H. symmetry. exact H.
Qed.

(** Lifted pairing is natural in both product factors. *)

(** 提升后的配对在两个积因子上自然。 *)

Program Definition OperationsTensorN
  : (tensorF (@CartesianMonoidal C HT HP) ∘F (O ×F O)) ⇒
      (O ∘F tensorF (@CartesianMonoidal C HT HP))
  :=
  {|nt p := lift₂ᵒ[O; (@id (fst p × snd p))]
  |}.
Next Obligation.
  destruct X as [X1 X2], Y as [Y1 Y2], f as [f g].
  rewrite (@cartesian_tensor_map C HT HP _ _ _ _ (fmap O f) (fmap O g)),
    (@cartesian_tensor_map C HT HP _ _ _ _ f g).
  pose proof (ops_pre (IsApplicativeOps := operations_laws O)
    (@id (Y1 × Y2)) f g) as H.
  cbn in H. rewrite comp_id_l in H.
  rewrite H, <- operations_lift_pair. reflexivity.
Defined.

(** Reconstruct the lax structure from pure terminal value and lifted pairing. *)

(** 从纯终值及提升后的配对恢复 lax 结构。 *)

Program Definition OperationsLax
  : LaxMonoidalFct (@CartesianMonoidal C HT HP)
      (@CartesianMonoidal C HT HP)
  :=
  {|LaxMonoidalF := O
  ; lax_unit := pureᵒ[O] 1
  ; lax_tensorN := OperationsTensorN
  |}.
Next Obligation.
  change (fmap O (π2 : Hom (1 × X) X) ∘ lift₂ᵒ[O; (@id (1 × X))] ∘
    (@tensor_map C (@CartesianMonoidal C HT HP) _ _ _ _
      (pureᵒ[O] 1) (@id (O X))) ≈ π2).
  rewrite cartesian_tensor_map.
  rewrite <- operations_lift_pair.
  exact (ops_unit_l (IsApplicativeOps := operations_laws O) X).
Defined.
Next Obligation.
  change (fmap O (π1 : Hom (X × 1) X) ∘ lift₂ᵒ[O; (@id (X × 1))] ∘
    (@tensor_map C (@CartesianMonoidal C HT HP) _ _ _ _
      (@id (O X)) (pureᵒ[O] 1)) ≈ π1).
  rewrite cartesian_tensor_map.
  rewrite <- operations_lift_pair.
  exact (ops_unit_r (IsApplicativeOps := operations_laws O) X).
Defined.
Next Obligation.
  change (fmap O (@product_assoc C HP X Y Z).1 ∘
    lift₂ᵒ[O; (@id ((X × Y) × Z))] ∘
      (@tensor_map C (@CartesianMonoidal C HT HP) _ _ _ _
        lift₂ᵒ[O; (@id (X × Y))] (@id (O Z))) ≈
    lift₂ᵒ[O; (@id (X × (Y × Z)))] ∘
      (@tensor_map C (@CartesianMonoidal C HT HP) _ _ _ _
        (@id (O X)) lift₂ᵒ[O; (@id (Y × Z))]) ∘
      (@product_assoc C HP (O X) (O Y) (O Z)).1).
  rewrite !cartesian_tensor_map.
  rewrite <- operations_lift_pair.
  apply (ops_assoc (IsApplicativeOps := operations_laws O) id
    (@product_assoc C HP X Y Z).1 id id).
  rewrite !cross_id, !comp_id_l, !comp_id_r. reflexivity.
Defined.

(** Restore the structural Applicative without changing its pure operation. *)

(** 恢复结构式 Applicative，不改变其纯值运算。 *)

Program Definition OperationsA
  : Applicative C HT HP
  :=
  {|ApplicativeLax := OperationsLax
  ; applicative_pure := pureᵒ[O]
  |}.
Next Obligation. reflexivity. Defined.
Next Obligation.
  symmetry. pose proof (ops_pure (IsApplicativeOps := operations_laws O)
    (@id (X × Y))) as H.
  rewrite comp_id_r in H. exact H.
Defined.

(** The operation round trip preserves every lifted binary arrow. *)

(** 运算往返保持每条提升后的二元箭头。 *)

Lemma operations_roundtrip_lift {X Y Z : @Ob C} (f : Hom (X × Y) Z)
  : lift₂ᵒ[ApplicativeOperations OperationsA; f] ≈ lift₂ᵒ[O; f].
Proof. symmetry. apply operations_lift_pair. Qed.

(** The operation round trip preserves every pure component. *)

(** 运算往返保持每个纯值分量。 *)

Lemma operations_roundtrip_pure (X : @Ob C)
  : pureᵒ[ApplicativeOperations OperationsA] X ≈ pureᵒ[O] X.
Proof. reflexivity. Qed.

End Reconstruction.

(** ** The Structural Round Trip

    Fix a structural Applicative with the same terminal and product choices.
    Compare the recovered tensorator, unit and pure components. *)

(** ** 结构式往返

    固定使用同一终对象与积选择的结构式 Applicative，比较恢复的 tensorator、单位及纯值分量。 *)

Section StructuralRoundtrip.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (A : Applicative C HT HP).

(** The structural round trip preserves the tensorator componentwise. *)

(** 结构往返逐分量保持 tensorator。 *)

Lemma applicative_roundtrip_tensor (X Y : @Ob C)
  : φ₂[OperationsA (ApplicativeOperations A); X; Y] ≈ φ₂[A; X; Y].
Proof. cbn. unfold lax_lift2. rewrite functor_id, comp_id_l. reflexivity. Qed.

(** The structural round trip recovers the selected unit by its pure law. *)

(** 结构往返通过纯值单位律恢复选定单位。 *)

Lemma applicative_roundtrip_unit
  : φ₀[OperationsA (ApplicativeOperations A)] ≈ φ₀[A].
Proof. exact (applicative_pure_unit A). Qed.

(** Pure components are retained by computation. *)

(** 纯值分量由计算保持。 *)

Lemma applicative_roundtrip_pure (X : @Ob C)
  : pure[OperationsA (ApplicativeOperations A)] X ≈ pure[A] X.
Proof. reflexivity. Qed.

End StructuralRoundtrip.
