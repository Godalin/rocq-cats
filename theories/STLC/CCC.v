From Cats Require Export STLC.Exponential.
From Cats Require Import Cat.CCC.

(** * The Syntactic Cartesian Closed Category *)

(** * 语法笛卡尔闭范畴 *)

(** ** Assembling the chosen syntactic model

    The terminal, product and exponential constructions have already
    established their universal properties. [CtxCat_CCC] bundles those
    choices so a client can interpret the STLC operations in the syntax
    itself. There are no new beta/eta axioms in this assembly.

    In this presentation objects are contexts. The terminal object is the
    empty context, products are concatenations and exponentials are the
    packed function contexts of [CtxExp]. These choices make a model;
    they do not assert that other product or exponential representations
    have literally equal objects. Enable this model structure explicitly
    when using it, just as for a concrete setoid model. *)

(** ** 组装选定的语法模型

    终对象、积与指数构造已经分别证明泛性质。[CtxCat_CCC] 把这些选择打包，
    使客户端能够在语法自身中解释 STLC 操作。这一步没有加入新的 βη 公理。

    此呈现以上下文为对象：终对象是空上下文，积是连接，指数是 [CtxExp]
    给出的打包函数上下文。这些选择形成一个模型，并不断言其他积或指数的
    表示具有原生相等的对象。使用时须显式启用模型结构，与使用具体广集模型
    时的要求一致。 *)

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
