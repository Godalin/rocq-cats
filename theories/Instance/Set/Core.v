From Cats Require Import Cat.Core.



(** * Category of all Sets (Setoids in Rocq) *)

(** * 所有集合的范畴，集合按广集表示 *)

(** ** Category of [SetC]: [SetCat]

    [SetCat] plays the role of the category of sets in ordinary mathematics.
    [SetC] supplies the values of the set-valued functors in the Yoneda lemma. *)

(** ** [SetC] 的范畴 [SetCat]

    [SetCat] 承担普通数学中集合范畴的作用；[SetC] 也用于 Yoneda 引理。 *)

Program Instance SetCat@{u p +}
  : Cat
  :=
  {|Ob := SetC@{u p}
  ; HomSet := FunS
  ; id _ := id_resp
  ; comp _ _ _ := comp_resp
  ; comp_proper _ _ _ := comp_resp_proper
  ; comp_id_r _ _ := comp_resp_id_r
  ; comp_id_l _ _ := comp_resp_id_l
  ; comp_assoc _ _ _ _ := comp_resp_assoc
  |}.
