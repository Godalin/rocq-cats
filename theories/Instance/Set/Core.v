From Cats Require Import Cat.Core.



(** * Category of all Sets (Setoids in Rocq) *)

(** ** Category of [SetC]: [SetCat]

    [SetCat] can be used as a suitable category with similar
    role as _Set_ in ordinary mathematics. In the proof of
    _Yoneda lemma,_ [SetC] plays an important role. *)

Program Instance SetCat@{u p +} : Cat :=
  {|Ob := SetC@{u p}
  ; HomSet := FunS
  ; id _ := id_resp
  ; comp _ _ _ := comp_resp
  ; comp_proper _ _ _ := comp_resp_proper
  ; comp_id_r _ _ := comp_resp_id_r
  ; comp_id_l _ _ := comp_resp_id_l
  ; comp_assoc _ _ _ _ := comp_resp_assoc
  |}.
