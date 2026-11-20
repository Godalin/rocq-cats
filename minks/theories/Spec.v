From elpi Require Import elpi.

(** * Structure specifications

    Store inheritance by Rocq identity. Each component key names one
    selected mixin and its dependencies within a structure. *)

(** * 结构规格

    用 Rocq 标识保存继承关系。在一个结构内，每个组件键指定一份 Mixin
    及其依赖。 *)

Elpi Db minks.flat.db lp:{{
  kind component type.
  type slot id -> gref -> list id -> component.

  pred spec i:inductive, o:list inductive, o:list component.
}}.

Elpi File minks.spec lp:{{
  pred merge i:list component, i:list component, o:list component.
  merge [] Cs Cs.
  merge [slot Key Ref Deps | Rest] Cs Out :-
    if (std.mem Cs (slot Key _ _))
       (if (std.mem Cs (slot Key Ref Deps)) true
         (coq.error "Incompatible definitions of component" Key),
        merge Rest Cs Out)
       (merge Rest {std.append Cs [slot Key Ref Deps]} Out).

  pred close i:inductive, o:list component.
  close I Cs :-
    if (spec I Parents Local) true (coq.error "Not a Minks structure:" I),
    close-parents Parents [] Inherited,
    merge Local Inherited Cs.

  pred close-parents i:list inductive, i:list component, o:list component.
  close-parents [] Cs Cs.
  close-parents [P | Ps] Acc Cs :-
    close P Inherited,
    merge Inherited Acc Acc1,
    close-parents Ps Acc1 Cs.

  % Only one slot for a class head may supply an automatic instance.
  % Different dependencies do not prove that two instance types are disjoint.
  pred auto-instance i:list component, i:component.
  auto-instance Cs (slot Key Ref _) :-
    coq.TC.class? Ref,
    not (std.exists Cs (c\ c = slot Other Ref _, not (Other = Key))).

  pred component-key i:component, o:id.
  component-key (slot Key _ _) Key.
}}.
