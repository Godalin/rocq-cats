From Cats Require Export
  Cat.Core
  Cat.Functor.Core.

(** * Categories Induced by an Object Map *)

(** * 由对象映射诱导的范畴 *)

(** Keep the hom-sets and all operations of an ambient category, while
    selecting a possibly redundant family of objects. No object equality
    or injectivity of the selection is required. *)

(** 保留环境范畴的 Hom 广集及全部运算，选取可重复的对象族；不要求对象相等
    或选取映射具有单射性。 *)

Program Definition InducedCat {C : Cat} (O : Type) (j : O → @Ob C)
  : Cat
  :=
  {|Ob := O
  ; HomSet X Y := HomSet (j X) (j Y)
  ; id X := id
  ; comp X Y Z := comp
  ; comp_proper X Y Z := comp_proper
  |}.
Next Obligation. apply comp_id_r. Qed.
Next Obligation. apply comp_id_l. Qed.
Next Obligation. apply comp_assoc. Qed.

(** The inclusion acts identically on every hom-set. *)

(** 嵌入在每个 Hom 广集上恒等作用。 *)

Program Definition InducedInclusionF {C : Cat} (O : Type) (j : O → @Ob C)
  : Functor (InducedCat O j) C
  :=
  {|F0 := j
  ; F1 X Y f := f
  |}.
Next Obligation. intros f g H. exact H. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.
