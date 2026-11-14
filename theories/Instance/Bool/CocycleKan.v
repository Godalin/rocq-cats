From Cats Require Export
  Instance.Set.Simplicial.Cocycle.Kan
  Instance.Bool.CocycleModel
  Instance.Bool.Commutative.

(** * An Explicit Boolean Cocycle Kan Model

    The previous Boolean model has distinct triangles with the same edges.
    The general cocycle filling theorem now supplies every positive-
    dimensional horn filler, using the existing xor group and its
    commutativity witness. This specializes
    %\coqref{Cats.Instance.Set.Simplicial.Cocycle.Kan.two cocycle HasKanFillers}
    {%[two_cocycle_HasKanFillers]%}%. Enable the resulting Kan structure
    explicitly.

    This is an actual Kan structure; computation of its homotopy groups and
    the intended higher homotopy distinction remain separate work. *)

(** * 显式布尔 Cocycle Kan 模型

    前面的布尔模型有边相同而仍不同的三角形。一般 cocycle 填充定理现在复用
    已有异或群及其交换性见证，提供全部正维 horn 填充。这是
    %\coqref{Cats.Instance.Set.Simplicial.Cocycle.Kan.two cocycle HasKanFillers}
    {%[two_cocycle_HasKanFillers]%}% 的特化。所得 Kan 结构仍须显式启用。

    这里得到实际 Kan 结构；其同伦群计算及预期的高阶同伦区别仍为独立工作。 *)

Local Existing Instance BoolS_Group.
Local Existing Instance BoolS_IsCommutativeMonoid.

(** Select the full Kan structure without globally registering it. *)

(** 选取完整 Kan 结构，但不全局注册。 *)

Definition BoolCocycleModel_HasKanFillers
  : HasKanFillers BoolCocycleModel
  := two_cocycle_HasKanFillers.
