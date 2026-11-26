From Cats Require Export
  Topos.Core.
From Cats Require Import
  Cat.Core
  Cat.CCC.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Morphism
  Cat.Pullback
  Topos.Nat.

(** Well-Pointed Category: equality on all global points detects equality. *)

(** 良点范畴：在所有全局点上的相等能够检测态射相等。 *)

Minks.Mixin IsWellPointed {C : Cat}
  extends HasTerminal C
  :=
  { well_pointed_ext {X Y : C} {f g : Hom X Y}
    : (∀ x : Hom 1 X, f ∘ x ≈ g ∘ x) → f ≈ g
  }.

Arguments IsWellPointed {_} _.

(** Choice for ETCS models: every epimorphism has a right inverse. *)

(** ETCS 模型的选择原理：每个满态射都有右逆。 *)

Minks.Mixin HasAxiomChoice (C : Cat)
  :=
  { choice_split_epi {X Y : C} {f : Hom X Y}
    : is_epi f → ∃ g, is_rinv_of f g
  }.

(** Extend one elementary topos with a chosen initial object,
    well-pointedness, split epimorphisms and a natural-numbers object.
    Every terminal-dependent field uses the parent's same selected terminal
    object. *)

(** 为一个初等拓扑斯增加选定始对象、良点性、满态射分裂及自然数对象。
    所有依赖终对象的字段均使用父结构的同一终对象选择。 *)

(** Store only the additional choices and laws. The generated parent views
    reuse all Topos components; well-pointedness and recursion depend on the
    inherited terminal, not an independently supplied terminal object. *)

(** 仅保存额外选择和定律。生成的父视图复用全部 Topos 成分；良点性与递归依赖
    继承的终对象，而非独立提供的终对象。 *)

Minks.Struct ETCS
  extends Topos
  with  hasInitial as hasInitial : HasInitial,
        isWellPointed as isWellPointed : IsWellPointed,
        hasAxiomChoice as hasAxiomChoice : HasAxiomChoice,
        hasNaturalNumbersObj as hasNaturalNumbersObj : HasNaturalNumbersObj.

Declare Scope etcs_scope.
Delimit Scope etcs_scope with etcs.
Open Scope etcs_scope.

Notation "'∅'" := Init
  (at level 0)
  : etcs_scope.

Notation "'∈' X" := (Hom 1 X)
  (at level 35) : etcs_scope.

(** ** The ETCS Environment

    Fix an [ETCS] model [C]. This opens the categorical
    set-theory environment for the elementary set constructions discussed
    below. *)

(** ** ETCS 环境

    固定 [ETCS] 模型 [C]，为下文讨论基本集合构造设定范畴集合论环境。 *)

Section ETCS.
Context {C : ETCS}.

(** Let's do _Set Theory_ (in [ETCS]) ! *)

(** 在 [ETCS] 中开展集合论。 *)

(** ** Empty Set *)

(** ** 空集 *)

(* Proposition init_no_elem
  : ∈ 0 → Empty_set.
Proof. intros x. *)

End ETCS.
