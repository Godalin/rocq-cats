From Cats.Set Require Export Core.

(** * Respectful Maps

    Function equality is pointwise equality in the codomain. It compares
    values, without comparing functions or respectfulness proofs by [eq]. *)

(** * 保相等映射

    函数相等是目标中的逐点相等，比较值而不使用函数或保相等证明的原生相等。 *)

Definition FunEq {X Y : SetC} (f g : X → Y)
  := ∀ x : X, f x ≈S g x.

Infix "≈f" := FunEq (at level 50).

(** [FunEq] is an equivalence relation. *)

(** [FunEq] 是等价关系。 *)

Program Instance FunEq_Equivalence {X Y}
  : Equivalence (@FunEq X Y).
Next Obligation. intros f x. reflexivity. Defined.
Next Obligation. intros f g H x. symmetry. apply H. Defined.
Next Obligation. intros f g h H1 H2 x. transitivity (g x); auto. Defined.

(** A function together with preservation of specified equality. *)

(** 函数及其保持指定相等的见证。 *)

Record FunS_resp (X Y : SetC)
  :=
  { func :> carrier X → carrier Y
  ; func_proper :: Proper (carrier_equiv X ==> carrier_equiv Y) func
  }.

Infix "→r" := FunS_resp (at level 99).

(** The input map's Proper carrier bound [s] is independent of the target
    carrier level [v]; lifting a native hom-map must not identify them. *)

(** 输入映射的 Proper 载体上界 [s] 独立于目标载体层级 [v]；提升原生 Hom 映射时
    不能把两者等同。 *)

Program Definition lift_resp@{v q s +} {X Y : SetC}
    (f : FunS_resp@{s _ _ _ _ _} X Y)
  : LiftS@{_ _ v q} X →r LiftS@{_ _ v q} Y
  :=
  {|func x :=
     {|lower := f (lower x)
     |}
  |}.
Next Obligation.
  intros [x] [y] [H]. exact {|lower := @func_proper _ _ f x y H
                            |}.
Defined.

Notation "f '^↑S'" := (lift_resp f) (at level 35) : set_scope.

(** The setoid of respectful functions, with pointwise equality. *)

(** 以逐点相等比较保相等函数的广集。 *)

Program Canonical FunS (X Y : SetC)
  : SetC
  :=
  {|carrier := X →r Y
  ; carrier_equiv := FunEq
  |}.
Next Obligation. split.
  - intros f x. reflexivity.
  - intros f g H x. symmetry. apply H.
  - intros f g h H1 H2 x. transitivity (g x); auto.
Defined.

Infix "→S" := FunS (at level 99).

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance lift_resp_proper@{v q +} {X Y : SetC}
  : Proper (carrier_equiv (X →S Y) ==>
      carrier_equiv (LiftS@{_ _ v q} X →S LiftS@{_ _ v q} Y))
      (λ f, (f^↑S : LiftS@{_ _ v q} X →r LiftS@{_ _ v q} Y)).
Proof. intros f g H [x]. exact {|lower := H x
                               |}. Defined.

(** The identity respectful map. *)

(** 恒等保相等映射。 *)

Program Definition id_resp {X}
  : X →r X
  :=
  {|func (x : X) := x
  |}.
Next Obligation. intros x x' Hx. exact Hx. Defined.

(** Composition of respectful maps. *)

(** 保相等映射的复合。 *)

Program Definition comp_resp {X Y Z} (f : Y →r Z) (g : X →r Y)
  : X →r Z
  :=
  {|func (x : X) := f (g x)
  |}.
Next Obligation. intros x x' Hx. rewrite Hx. reflexivity. Defined.

Infix "∘r" := comp_resp (at level 50).

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance comp_resp_proper {X Y Z}
  : Proper (carrier_equiv (Y →S Z) ==> carrier_equiv (X →S Y)
      ==> carrier_equiv (X →S Z)) (@comp_resp X Y Z).
Proof.
  intros f f' Hf g g' Hg x. cbn.
  rewrite (Hg x), (Hf (g' x)). reflexivity.
Qed.

(** Right identity law for [comp_resp]. *)

(** [comp_resp] 右单位律。 *)

Theorem comp_resp_id_r {X Y} (f : X →r Y)
  : f ∘r id_resp ≈f f.
Proof. intros x. reflexivity. Qed.

(** Left identity law for [comp_resp]. *)

(** [comp_resp] 左单位律。 *)

Theorem comp_resp_id_l {X Y} (f : X →r Y)
  : id_resp ∘r f ≈f f.
Proof. intros x. reflexivity. Qed.

(** Associativity law for [comp_resp]. *)

(** [comp_resp] 结合律。 *)

Theorem comp_resp_assoc {W X Y Z} (f : Y →r Z) (g : X →r Y) (h : W →r X)
  : ((f ∘r g) ∘r h) ≈f (f ∘r (g ∘r h)).
Proof. intros x. reflexivity. Qed.
