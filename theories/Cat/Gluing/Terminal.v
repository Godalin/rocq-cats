From Cats Require Export
  Cat.Gluing.Core
  Cat.Terminal.

(** * Terminal Objects in Gluing

    A terminal base object [T] yields [(F T, T, id)]. Its left side need
    not be terminal in [D]. No terminal object in [D] and no terminal
    preservation by [F] are required. Candidate terminality is proved
    before packaging the explicitly enabled chosen structure. *)

(** * 粘合中的终对象

    基范畴中的终对象 [T] 给出 [(F T, T, id)]。其左侧无须在 [D] 中为终。
    不要求 [D] 有终对象，也不要求 [F] 保持终对象。先证明候选终性，再打包
    为显式启用的选定结构。 *)

(** ** A Terminal Base Object

    Fix a functor and a supplied base object. The right component of a
    map to its identity gluing determines the left component uniquely. *)

(** ** 基范畴的终对象

    固定函子及给定的基对象。指向其恒等粘合的映射之右分量唯一确定左分量。 *)

Section GluingTerminal.
Context {C D : Cat} (F : Fct C D) (T : @Ob C).

(** The candidate uses the identity comparison at [F T]. *)

(** 候选取 [F T] 处的恒等比较。 *)

Program Definition GluingTerminal
  : @Ob (Gluing F)
  :=
  {|comma_left_ob := F T
  ; comma_right_ob := T
  ; comma_arrow := id
  |}.

(** Terminality uses only the supplied base universal property. *)

(** 终性只使用给定的基范畴泛性质。 *)

Definition gluing_terminal (HT : is_terminal T)
  : @is_terminal (Gluing F) GluingTerminal.
Proof.
  intros X. destruct (HT (comma_right_ob X)) as [g Hg].
  assert (square : fmap F g ∘ comma_arrow X ≈
      id ∘ (fmap F g ∘ comma_arrow X)) by (symmetry; apply comp_id_l).
  unshelve refine (existT _
    {|comma_left := _
    ; comma_right := _
    ; comma_comm := _
    |} _).
  - exact (fmap F g ∘ comma_arrow X).
  - exact g.
  - exact square.
  - split; [exact I |]. intros f _. split; cbn.
    + pose proof (comma_comm f) as comm. cbn in comm.
      rewrite comp_id_l in comm. rewrite <- comm.
      apply comp_proper; [apply functor_fmap_proper; apply Hg; exact I |
        reflexivity].
    + apply Hg. exact I.
Defined.

End GluingTerminal.

(** Select the constructed terminal object only when explicitly enabled. *)

(** 只在显式启用时选择已构造的终对象。 *)

Program Definition Gluing_HasTerminal {C D : Cat} (F : Fct C D)
    `{TC : !HasTerminal C}
  : HasTerminal (Gluing F)
  :=
  {|Term := GluingTerminal F (@Term C TC)
  ; terminal_universal := gluing_terminal F _ terminal_universal
  |}.
