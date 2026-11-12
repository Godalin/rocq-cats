From Cats Require Export
  Cat.Computational.Arrow.Symmetric
  Cat.Computational.Freyd.Core.

Local Open Scope computation_scope.

(** * The Freyd Category of a Computational Arrow

    Finite products are selected once on values. The existing symmetric
    premonoidal computation structure, pure centrality and context laws
    give strict preservation. All object boundaries are reflexive, so
    their transports compute to identities. This is the forward
    construction; no round-trip or categorical equivalence is claimed. *)

(** * 计算 Arrow 的 Freyd 范畴

    在值上仅选定一次有限积。已有对称预幺半计算结构、纯中心性及上下文定律
    给出严格保持性。全部对象边界均为自反相等，故其运输计算为恒等。这是
    正向构造，不主张往返定律或范畴等价。 *)

Section Cartesian.
Context {C K : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (A : Arrow C K (@CartesianMonoidal C HT HP)).

(** Retain the original pure functor and all existing structure choices.
    Pure, Reader-like and stateful models share this one construction. *)

(** 保留原纯函子及全部已有结构选择。纯计算、Reader 型及状态模型共享此构造。 *)

Program Definition ArrowFreyd
  : FreydCat C K
  :=
  {|FreydF := A
  ; hasCartesian := {|hasTerminal := HT; hasProduct := HP|}
  ; hasSymmetricPremonoidal := ArrowSymmetricPremonoidal A
  ; freyd_tensor_objects X Y := eq_refl
  ; freyd_unit_object := eq_refl
  ; freyd_pure_central X Y f := arrow_pure_central A f
  |}.
Next Obligation.
  change (id ∘ arr[A; @id Z × f] ≈ second[A; arr[A; f]; Z] ∘ id).
  rewrite comp_id_l, comp_id_r. symmetry. apply arrow_second_arr.
Defined.
Next Obligation.
  change (id ∘ arr[A; f × @id Z] ≈ first[A; arr[A; f]; Z] ∘ id).
  rewrite comp_id_l, comp_id_r. symmetry. apply arrow_first_arr.
Defined.
Next Obligation. symmetry. apply comp_id_r. Defined.
Next Obligation. symmetry. apply comp_id_r. Defined.
Next Obligation. rewrite comp_id_l, comp_id_r. reflexivity. Defined.
Next Obligation. rewrite comp_id_l, comp_id_r. reflexivity. Defined.

End Cartesian.
