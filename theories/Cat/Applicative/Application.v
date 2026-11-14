From Cats Require Export
  Cat.Applicative.Operations
  Cat.Applicative.Closed.

Local Open Scope monoidal_scope.
Local Open Scope applicative_scope.

(** * A Coherent Pure and Application Presentation

    Application alone determines binary lifting by currying. The laws below
    require that reconstructed lifting is coherent as an arrow operation.
    The four classical global-value equations alone are not used as a
    replacement for these conditions in an arbitrary closed category. *)

(** * 相干的纯值与应用呈现

    应用通过柯里化唯一确定二元提升。以下定律要求恢复的提升作为态射运算相干。
    在任意闭范畴中，不将四条经典全局值方程单独作为这些条件的替代。 *)

(** First fix binary products, exponentials, an endofunctor and an application
    operation. Recover binary lifting without assuming a pure map or terminal. *)

(** 首先固定二元积、指数、自函子及应用运算，恢复二元提升；此处不假设纯值映射或终对象。 *)

Section RawApplication.
Context {C : Cat} `{HP : !HasProduct C} `{HE : !HasExponential HP}
    (F : Fct C C)
    (a : ∀ {X Y : @Ob C}, Hom (F (Y ^ X) × F X) (F Y)).

(** Lift a binary arrow by mapping its transpose and then applying. *)

(** 映射二元箭头的转置，再应用，从而提升该箭头。 *)

Definition application_lift {X Y Z : @Ob C} (f : Hom (X × Y) Z)
  : Hom (F X × F Y) (F Z)
  := @a Y Z ∘ (fmap F (ƛ f) × id).

(** The reconstruction respects the designated equality of binary arrows. *)

(** 恢复保持二元箭头的指定相等。 *)

Global Instance application_lift_proper {X Y Z : @Ob C}
  : Proper (HomEq ==> HomEq) (@application_lift X Y Z).
Proof. intros f g H. unfold application_lift. rewrite H. reflexivity. Qed.

(** Reconstructing evaluation recovers application, without any law on [a]. *)

(** 恢复求值的提升即恢复应用，无须对 [a] 作任何定律假设。 *)

Lemma application_lift_eval (X Y : @Ob C)
  : application_lift (eval (X := X) (Y := Y)) ≈ @a X Y.
Proof.
  unfold application_lift.
  rewrite exponential_curry_eval, functor_id, cross_id, comp_id_r.
  reflexivity.
Qed.

End RawApplication.

(** ** Application from Coherent Operations

    Fix chosen finite products and exponentials and a coherent binary-operation
    presentation. Construct application and recover its original lifting. *)

(** ** 从相干运算得到应用

    固定选定有限积、指数及相干二元运算呈现，构造应用并恢复原提升。 *)

Section OperationApplication.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    `{HE : !HasExponential HP} (O : ApplicativeOps C HT HP).

(** An operational presentation applies by lifting evaluation. *)

(** 运算式呈现通过提升求值来应用。 *)

Definition operations_ap {X Y : @Ob C}
  : Hom (O (Y ^ X) × O X) (O Y)
  := lift₂ᵒ[O; (eval (X := X) (Y := Y))].

(** Input substitution and the exponential beta law recover every binary
    lifting from application. No well-pointedness or strength is required. *)

(** 输入代入及指数 β 律从应用恢复每个二元提升，不要求良点性或强度。 *)

Lemma operations_lift_from_ap {X Y Z : @Ob C} (f : Hom (X × Y) Z)
  : lift₂ᵒ[O; f] ≈ application_lift O (@operations_ap) f.
Proof.
  unfold application_lift, operations_ap.
  pose proof (ops_pre (IsApplicativeOps := operations_laws O)
    (eval (X := Y) (Y := Z)) (ƛ f) id) as H.
  change (lift₂ᵒ[O; (eval (X := Y) (Y := Z))] ∘
    (fmap O (ƛ f) × fmap O (@id Y)) ≈ lift₂ᵒ[O; uncurry (ƛ f)]) in H.
  rewrite functor_id, exponential_β in H. symmetry. exact H.
Qed.

End OperationApplication.

(** Pure and application data with coherent reconstructed lifting. There is
    one underlying functor, and neither a tensorator nor a binary lifting
    is stored. The conditions are exactly those named in [IsApplicativeOps]. *)

(** 纯值与应用数据，附带恢复后提升的相干性。唯一底层视图为函子，不存储
    tensorator 或二元提升；条件恰为 [IsApplicativeOps] 中列出的定律。 *)

Class ApplicativeAp (C : Cat) (HT : HasTerminal C) (HP : HasProduct C)
    (HE : HasExponential HP)
  :=
  (** The only coercion exposes the underlying endofunctor. *)

  (** 唯一强制转换暴露底层自函子。 *)

  { ApF :> Fct C C

  (** Pure embedding commutes with every ordinary arrow. *)

  (** 纯值嵌入与每条通常箭头交换。 *)

  ; application_pure : IdF ⇒ ApF

  (** Application combines an effectful internal function and argument. *)

  (** 应用组合带效应的内部函数及参数。 *)

  ; application_ap {X Y : @Ob C}
      : Hom (@Prod C HP (ApF (@exp C HP HE Y X)) (ApF X)) (ApF Y)

  (** Currying and application reconstruct a coherent binary lifting. *)

  (** 柯里化及应用恢复相干的二元提升。 *)

  ; application_laws
      :: IsApplicativeOps HT HP ApF application_pure
        (@application_lift C HP HE ApF (@application_ap))
  }.

Arguments ApF {_ _ _ _} _.
Arguments application_pure {_ _ _ _} _.
Arguments application_ap {_ _ _ _} _ {_ _}.
Arguments application_laws {_ _ _ _} _.

Notation "'pureᵃ[' P ']'" := (application_pure P) : applicative_scope.
Notation "'apᵃ[' P ']'" := (application_ap P) : applicative_scope.

(** Read binary operations from a coherent application presentation. *)

(** 从相干应用呈现读取二元运算。 *)

Program Definition ApplicationOperations {C : Cat}
    {HT : HasTerminal C} {HP : HasProduct C} {HE : HasExponential HP}
    (P : ApplicativeAp C HT HP HE)
  : ApplicativeOps C HT HP
  :=
  {|OpsF := P
  ; operations_pure := pureᵃ[P]
  ; operations_lift := @application_lift C HP HE P (@application_ap _ _ _ _ P)
  ; operations_laws := application_laws P
  |}.

(** Read application from binary operations, transporting their laws along
    the proved arrow equality rather than requiring record equality. *)

(** 从二元运算读取应用；沿已证态射相等运输定律，不要求记录相等。 *)

Program Definition OperationsApplication {C : Cat}
    {HT : HasTerminal C} {HP : HasProduct C} {HE : HasExponential HP}
    (O : ApplicativeOps C HT HP)
  : ApplicativeAp C HT HP HE
  :=
  {|ApF := O
  ; application_pure := pureᵒ[O]
  ; application_ap := @operations_ap C HT HP HE O
  ; application_laws := applicative_ops_transport (operations_laws O)
      (@operations_lift_from_ap C HT HP HE O)
  |}.

(** Construct a structural Applicative from coherent pure/application data. *)

(** 从相干纯值／应用数据构造结构式 Applicative。 *)

Definition ApplicationA {C : Cat}
    {HT : HasTerminal C} {HP : HasProduct C} {HE : HasExponential HP}
    (P : ApplicativeAp C HT HP HE)
  : Applicative C HT HP
  := OperationsA (ApplicationOperations P).

(** Expose a structural Applicative as coherent pure/application operations. *)

(** 将结构式 Applicative 暴露为相干纯值／应用运算。 *)

Definition ApplicativeApplication {C : Cat}
    {HT : HasTerminal C} {HP : HasProduct C} {HE : HasExponential HP}
    (A : Applicative C HT HP)
  : ApplicativeAp C HT HP HE
  := OperationsApplication (ApplicativeOperations A).

(** ** Application Round Trips

    Fix the same finite-product and exponential choices. Compare application
    and structural Applicative presentations in their specified hom equality. *)

(** ** 应用的往返

    固定同一有限积与指数选择，在指定 Hom 相等下比较应用与结构式呈现。 *)

Section Roundtrips.
Context {C : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    `{HE : !HasExponential HP}.

(** Application to binary operations and back preserves application. *)

(** 应用转为二元运算再返回，保持应用。 *)

Lemma application_roundtrip_ap (P : ApplicativeAp C HT HP HE) (X Y : @Ob C)
  : apᵃ[OperationsApplication (ApplicationOperations P)] ≈
      (apᵃ[P] : Hom (P (Y ^ X) × P X) (P Y)).
Proof. apply application_lift_eval. Qed.

(** The application-operation round trip retains pure by computation. *)

(** 应用运算往返通过计算保留纯值。 *)

Lemma application_roundtrip_pure (P : ApplicativeAp C HT HP HE)
    (X : @Ob C)
  : pureᵃ[OperationsApplication (ApplicationOperations P)] X ≈ pureᵃ[P] X.
Proof. reflexivity. Qed.

(** Binary operations to application and back preserves every binary arrow. *)

(** 二元运算转为应用再返回，保持每个二元箭头。 *)

Lemma application_roundtrip_lift (O : ApplicativeOps C HT HP)
    {X Y Z : @Ob C} (f : Hom (X × Y) Z)
  : lift₂ᵒ[ApplicationOperations (OperationsApplication O); f] ≈
      lift₂ᵒ[O; f].
Proof. symmetry. exact (operations_lift_from_ap O f). Qed.

(** The structural reconstruction preserves the supplied application. *)

(** 结构重建保持给定应用。 *)

Lemma application_reconstruction_ap (P : ApplicativeAp C HT HP HE)
    (X Y : @Ob C)
  : (ap[ApplicationA P] : Hom (P (Y ^ X) × P X) (P Y)) ≈ apᵃ[P].
Proof.
  transitivity (lift₂ᵒ[ApplicationOperations P; (eval (X := X) (Y := Y))]).
  - exact (operations_roundtrip_lift (ApplicationOperations P)
      (eval (X := X) (Y := Y))).
  - apply application_lift_eval.
Qed.

(** The comparison also preserves application in every shared context.
    Rewriting this equality and pure preservation transfers the four
    classical laws already proved for [ApplicationA P]. *)

(** 比较也在每个共同上下文中保持应用。重写此相等及纯值保持，即可运输
    已对 [ApplicationA P] 证明的四条经典定律。 *)

Lemma application_reconstruction_apply (P : ApplicativeAp C HT HP HE)
    {W X Y : @Ob C} (u : Hom W (P (Y ^ X))) (v : Hom W (P X))
  : u ⋆[ApplicationA P] v ≈ apᵃ[P] ∘ ⟨u, v⟩.
Proof.
  unfold applicative_apply.
  rewrite (application_reconstruction_ap P X Y). reflexivity.
Qed.

(** The structural reconstruction retains the supplied pure components. *)

(** 结构重建保留给定纯值分量。 *)

Lemma application_reconstruction_pure (P : ApplicativeAp C HT HP HE)
    (X : @Ob C)
  : pure[ApplicationA P] X ≈ pureᵃ[P] X.
Proof. reflexivity. Qed.

(** Every reconstructed structural binary operation agrees with the original. *)

(** 每个重建后的结构式二元运算均与原运算一致。 *)

Lemma applicative_application_roundtrip_lift (A : Applicative C HT HP)
    {X Y Z : @Ob C} (f : Hom (X × Y) Z)
  : lift₂[ApplicationA (ApplicativeApplication A); f] ≈ lift₂[A; f].
Proof.
  transitivity (lift₂ᵒ[ApplicationOperations (ApplicativeApplication A); f]).
  - exact (operations_roundtrip_lift
      (ApplicationOperations (ApplicativeApplication A)) f).
  - exact (application_roundtrip_lift (ApplicativeOperations A) f).
Qed.

(** The structural/application round trip preserves closed application. *)

(** 结构／应用往返保持闭应用。 *)

Lemma applicative_application_roundtrip_ap (A : Applicative C HT HP)
    (X Y : @Ob C)
  : ap[ApplicationA (ApplicativeApplication A)] ≈
      (ap[A] : Hom (A (Y ^ X) × A X) (A Y)).
Proof.
  exact (applicative_application_roundtrip_lift A
    (eval (X := X) (Y := Y))).
Qed.

(** Pure components are retained by the structural/application round trip. *)

(** 结构／应用往返保留纯值分量。 *)

Lemma applicative_application_roundtrip_pure (A : Applicative C HT HP)
    (X : @Ob C)
  : pure[ApplicationA (ApplicativeApplication A)] X ≈ pure[A] X.
Proof. reflexivity. Qed.

(** The tensorator is recovered using equality of arrows, not of functors. *)

(** tensorator 通过态射相等恢复，不要求函子原生相等。 *)

Lemma applicative_application_roundtrip_tensor (A : Applicative C HT HP)
    (X Y : @Ob C)
  : φ₂[ApplicationA (ApplicativeApplication A); X; Y] ≈ φ₂[A; X; Y].
Proof.
  change (lift₂ᵒ[ApplicationOperations (ApplicativeApplication A);
    (@id (X × Y))] ≈ φ₂[A; X; Y]).
  rewrite (application_roundtrip_lift (ApplicativeOperations A)
    (@id (X × Y))).
  unfold operations_lift, ApplicativeOperations, lax_lift2.
  rewrite functor_id, comp_id_l. reflexivity.
Qed.

(** The unit comparison is recovered by the original pure-unit law. *)

(** 单位比较由原纯值单位律恢复。 *)

Lemma applicative_application_roundtrip_unit (A : Applicative C HT HP)
  : φ₀[ApplicationA (ApplicativeApplication A)] ≈ φ₀[A].
Proof. exact (applicative_pure_unit A). Qed.

End Roundtrips.
