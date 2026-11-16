From Cats Require Export
  Topos.Core.
From Cats Require Import
  Cat.Core
  Cat.CCC
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Morphism
  Cat.Pullback
  Topos.Nat.

(** Well-Pointed Category: equality on all global points detects equality. *)

(** 良点范畴：在所有全局点上的相等能够检测态射相等。 *)

Class IsWellPointed (C : Cat) (HT : HasTerminal C)
  :=
  { well_pointed_ext {X Y : C} {f g : Hom X Y}
    : (∀ x : Hom 1 X, f ∘ x ≈ g ∘ x) → f ≈ g
  }.

(** Choice for ETCS models: every epimorphism has a right inverse. *)

(** ETCS 模型的选择原理：每个满态射都有右逆。 *)

Class HasAxiomChoice (C : Cat)
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

Class ETCS (C : Cat)
  :=
  (** The unique parent shares the classifier and pullbacks as well as
      the existing [CCC] and [CartCat] choices. *)

  (** 唯一父结构共享分类子、拉回及已有 [CCC] 与 [CartCat] 的各项选择。 *)

  { ETCSC :> Topos C

  (** Retain the additional chosen initial object. *)

  (** 保留额外选定的始对象。 *)

  ; hasInitial :: HasInitial C

  (** Global points from that same terminal detect equality of arrows. *)

  (** 来自同一终对象的全局点能够检测态射相等。 *)

  ; isWellPointed :: IsWellPointed C (@hasTerminal C ETCSC)

  (** Retain the Type-valued choice of a right inverse for each epi. *)

  (** 保留为每个满态射选取右逆的 Type 值见证。 *)

  ; hasAxiomChoice :: HasAxiomChoice C

  (** Zero and recursion use exactly the inherited terminal choice. *)

  (** 零与递归恰好使用继承的终对象选择。 *)

  ; hasNaturalNumbersObj
    :: HasNaturalNumbersObj C (@hasTerminal C ETCSC)
  }.

Arguments ETCSC {_} _.

(** Register the same parent for instance search, without selecting any
    concrete ETCS model or adding a second path to the category. *)

(** 将同一父结构注册到实例搜索，不选定具体 ETCS 模型，也不增加第二条
    到底层范畴的路径。 *)

#[export] Existing Instance ETCSC.

Declare Scope etcs_scope.
Open Scope etcs_scope.

Notation "'∅'" := Init.

Notation "'∈' X" := (Hom 1 X)
  (at level 35) : etcs_scope.

(** ** The ETCS Environment

    Fix a category [C] equipped with [ETCS C]. This opens the categorical
    set-theory environment for the elementary set constructions discussed
    below. *)

(** ** ETCS 环境

    固定带有 [ETCS C] 结构的范畴 [C]，为下文讨论基本集合构造设定范畴集合论环境。 *)

Section ETCS.
Context {C : Cat} `{Axioms : !ETCS C}.

(** Let's do _Set Theory_ (in [ETCS]) ! *)

(** 在 [ETCS] 中开展集合论。 *)

(** ** Empty Set *)

(** ** 空集 *)

(* Proposition init_no_elem
  : ∈ 0 → Empty_set.
Proof. intros x. *)

End ETCS.
