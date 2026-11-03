From Cats Require Export STLC.Exponential.
From Cats Require Import Cat.CCC.

(** * The Syntactic Cartesian Closed Category *)

(** * 语法笛卡尔闭范畴 *)

(** Assemble the chosen empty context, concatenation products and packed
    function contexts. This model structure must be enabled explicitly. *)

(** 组合选定的空上下文、连接积及打包函数上下文；该模型结构须显式启用。 *)

Program Definition CtxCat_CCC@{b e l +} (B : Type@{b})
  : CCC (CtxCat@{b e l} B)
  :=
  {|hasTerminal := CtxCat_HasTerminal B
  ; hasProduct := CtxCat_HasProduct B
  ; hasExponential := CtxCat_HasExponential B
  |}.
