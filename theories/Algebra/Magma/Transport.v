From Cats Require Export
  Algebra.Magma.Core.

Local Open Scope magma_scope.

(** * Transporting a Multiplication

    Given respectful maps [f : B →r A] and [g : A →r B], multiply in [B]
    by moving both inputs to [A], multiplying there, and returning with [g].
    This raw operation needs no inverse equation. Stronger structures reuse
    this exact magma in their respective transport modules. *)

(** * 运输乘法

    给定保相等映射 [f : B →r A] 和 [g : A →r B]，先将两个输入送到 [A]，
    在那里相乘，再用 [g] 返回，得到 [B] 上的乘法。原始运算无须逆方程；
    更强结构在各自的运输模块中原样复用此原群。 *)

(** ** Two Maps between Independent Setoids

    Fix independently sized carriers and equalities. The supplied source
    magma determines every multiplication below; no target structure is
    registered by importing this module. *)

(** ** 独立广集之间的两个映射

    固定大小独立的载体与相等。以下所有乘法由显式来源原群决定；导入本模块
    不会注册目标结构。 *)

Section Transport.
Context (A : Magma) {B : SetC}.
Context (f : B →r A) (g : A →r B).

(** The transported operation is [g (f x ⋅ f y)]. Its respectfulness uses
    only the two supplied maps and the original operation. *)

(** 运输后的运算为 [g (f x ⋅ f y)]，其保相等性只使用给定两映射及原运算。 *)

Program Definition MagmaTransport : Magma
  :=
  {|MagmaToSetC := B
  ; hasMagma :=
      {|mul x y := g (@mul _ (hasMagma A) (f x) (f y))
      ; mul_proper := _
      |}
  |}.
Next Obligation.
  intros x x' Hx y y' Hy. apply (@func_proper _ _ g).
  apply (@mul_proper _ (hasMagma A)); apply (@func_proper _ _ f); assumption.
Defined.

(** If [f] recovers elements returned by [g], it preserves the transported
    product. Only this pointwise equation is needed; there is no equality
    of functions or their preservation fields.

    The square below uses specified equality in [A]. *)

(** 若 [f] 恢复经 [g] 返回的元素，它就保持运输后的乘积。这里只需逐点方程，
    不比较函数或保相等字段；下图的交换指 [A] 中指定的广集相等。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
B\times B \arrow[r, "\mu_B"] \arrow[d, "f\times f"'] &
B \arrow[d, "f"] \\
A\times A \arrow[r, "\mu_A"'] & A
\end{tikzcd}
\end{center}%
*)

Lemma magma_transport_map_mul (Hfg : (f ∘r g) ≈f id_resp) (x y : B)
  : f (@mul _ (hasMagma (MagmaTransport)) x y) ≈S
      @mul _ (hasMagma A) (f x) (f y).
Proof. exact (Hfg (@mul _ (hasMagma A) (f x) (f y))). Defined.

End Transport.
