From Cats Require Export
  Cat.Computational.Arrow.Core.

Local Open Scope monoidal_scope.
Local Open Scope computation_scope.
Local Open Scope ob_scope.

(** * Pure Computation with Monoidal Contexts *)

(** * 带幺半上下文的纯计算 *)

(** Fix a category and its selected monoidal structure. Use identity pure
    inclusion and tensoring to construct an explicit effect-free Arrow. *)

(** 固定范畴及其选定幺半结构，用恒等纯嵌入及张量构造显式无效应 Arrow。 *)

Section Pure.
Context {C : Cat} `{MC : !HasMonoidal C}.

(** The identity functor with left tensoring is an explicit pure model.
    Neither binary products nor symmetry are needed. *)

(** 恒等函子及左张量给出显式纯模型，不要求二元积或对称性。 *)

Program Definition PureArrow
  : @Arrow C C MC
  := MakeArrow IdF
    {|arrow_context X Y Z f := (id ⊗ f)%hom
    |}.
Next Obligation. intros f g H. rewrite H. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation.
  rewrite <- tensor_map_comp, comp_id_l. reflexivity.
Qed.
Next Obligation.
  rewrite <- !tensor_map_comp, !comp_id_l, !comp_id_r. reflexivity.
Qed.
Next Obligation.
  unfold tensor_map. rewrite tensor_sequence_left.
  apply tensor_unitor_l_natural.
Qed.
Next Obligation.
  pose proof (tensor_assoc_sequence_natural id[Z] id[W] f) as H.
  rewrite tensor_sequence_id in H. exact H.
Qed.

End Pure.
