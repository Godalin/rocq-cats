From Cats Require Export STLC.Set.
From Cats Require Export Cat.Core.
From Cats Require Import Cat.Terminal.

(** * The Syntactic Category of Contexts

    Arrows are simultaneous substitutions in the direction of context maps.
    Their specified equality is pointwise beta/eta equality. *)

(** * 上下文的语法范畴

    箭头为与上下文映射同向的同时替换，指定相等为逐点 βη 相等。 *)

(** Composition and its laws reuse the substitution algebra. The levels obey
    [b <= e <= l]; pointwise application of properness keeps its auxiliary
    law level from identifying with the equality witness level. *)

(** 复合及其定律复用替换代数，层级满足 [b <= e <= l]；逐点应用保相等证明，
    避免将其辅助定律层级与相等见证层级合并。 *)

Program Definition CtxCat@{b e l +} (B : Type@{b})
  : Cat@{b b e l l}
  :=
  {|Ob := Ctx B
  ; HomSet := SubS@{b e}
  ; id _ := sub_id
  ; comp _ _ _ := sub_comp
  ; comp_proper _ _ _ σ σ' H τ τ' K A x
      := sub_comp_tm_proper@{b e l} σ σ' H τ τ' K A x
  |}.
Next Obligation.
  apply sub_tm_eq_of_eq@{b e b b}. apply sub_comp_id_r.
Defined.
Next Obligation.
  apply sub_tm_eq_of_eq@{b e b b}. apply sub_comp_id_l.
Defined.
Next Obligation.
  apply sub_tm_eq_of_eq@{b e b b}. apply sub_comp_assoc.
Defined.

(** The empty context is terminal: it has no variables to assign. This chosen
    structure must be enabled explicitly. *)

(** 空上下文没有待赋值变量，因此是终对象；该选定结构须显式启用。 *)

Program Definition CtxCat_HasTerminal@{b e l +} (B : Type@{b})
  : HasTerminal (CtxCat@{b e l} B)
  :=
  {|Term := ctx_empty
  |}.
Next Obligation.
  intros Γ. exists sub_empty.
  refine {|this := I
         ; that := _
         |}.
  intros σ _. apply sub_tm_eq_of_eq@{b e b b}. apply sub_empty_unique.
Defined.
