From Cats Require Export
  Algebra.Monoid.Commutative
  Instance.Bool.Group.

(** * Boolean Commutative Coefficients

    Xor is commutative in the specified Boolean equality. This witness is
    about the multiplication already chosen by
    %\coqref{Cats.Instance.Bool.Group.BoolS Monoid}{%[BoolS_Monoid]%}%,
    which is also the monoid underlying [BoolS_Group]. It does not introduce
    a second multiplication, and importing the module selects neither a
    coefficient group nor its commutativity witness globally. *)

(** * 布尔交换系数

    异或按指定布尔相等满足交换律。此见证针对
    %\coqref{Cats.Instance.Bool.Group.BoolS Monoid}{%[BoolS_Monoid]%}%
    已选定的乘法，它也是 [BoolS_Group] 的底层幺半群。这里不引入第二种乘法；
    导入模块不会全局选定系数群或交换性见证。 *)

Program Definition BoolS_IsCommutativeMonoid
  : @IsCommutativeMonoid BoolS BoolS_Monoid
  :=
  {|monoid_mul_comm x y := _
  |}.
Next Obligation. destruct x, y; reflexivity. Defined.
