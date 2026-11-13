From Cats.Set Require Export
  Morphism.

(** * Constant Respectful Maps

    Fix source and target setoids. A constant function preserves their
    specified equalities, with no category structure or native function
    equality. The source is an explicit parameter for partial application. *)

(** * 常值保相等映射

    固定来源与目标广集。常值函数保持指定相等，不要求范畴结构或函数原生
    相等；来源是显式参数，便于部分应用。 *)

(** Return the selected target value on every source representative. *)

(** 在每个来源代表处返回选定目标值。 *)

Program Definition const_resp (X : SetC) {Y : SetC} (y : Y)
  : X →r Y
  :=
  {|func _ := y
  |}.
Next Obligation. intros x x' H. reflexivity. Defined.

(** Changing the constant respects target equality pointwise. *)

(** 改变常值时，逐点保持目标相等。 *)

Global Instance const_resp_proper {X Y : SetC}
  : Proper (carrier_equiv Y ==> FunEq) (@const_resp X Y).
Proof. intros y z H x. exact H. Qed.
