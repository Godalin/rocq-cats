From Cats Require Import
  Cat.Core
  Cat.Shape.Simplex.Operators
  DTT.CwF.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Fam.Core.
From Cats Require Import
  Instance.Set.Fam.Section
  Instance.Set.CwF
  Instance.Bool.Action.

Module CodeConversion.

Program Definition Codes
  : SetC
  :=
  {|carrier := unit
  ; carrier_equiv _ _ := unit
  |}.
Next Obligation. split; red; intros; exact tt. Defined.
Program Definition Values
  : SetC
  :=
  {|carrier := bool
  ; carrier_equiv := eq
  |}.

(** Conversion examines its equality witness, so opacity in the family or
    function equivalence operations would prevent this computation. *)

(** 转换检查相等见证；族或函数相等运算不透明时，此计算将无法归约。 *)

Program Definition Decode
  : FamS Codes
  :=
  {|fam _ := Values
  ; transpS x y p := match p with tt => id_resp end
  |}.
Next Obligation. destruct p. reflexivity. Defined.
Next Obligation. destruct p, q, r. reflexivity. Defined.

Program Definition A
  : UnitS →r Codes
  :=
  {|func _ := tt
  |}.
Next Obligation. intros x y p. exact tt. Defined.
Program Definition t
  : SectionS Decode[A]S
  :=
  {|section _ := false
  |}.
Next Obligation. reflexivity. Defined.

Definition T
  := CodeTyTmF Decode.
Example composition_conversion_computes
  : (ty_sub_comp T id_resp id_resp A ▸[T]
      t[id_resp]Tm[T][id_resp]Tm[T]) tt = false.
Proof. reflexivity. Qed.

End CodeConversion.

(** Extracting an action inverse through the generic groupoid and functor
    constructions must retain the concrete boolean computation. *)

(** 通过通用群胚与函子构造提取作用的逆时，须保留具体布尔计算行为。 *)

Example boolean_action_inverse_computes
  : bool_action_loop_iso.1 false = true.
Proof. reflexivity. Qed.

(** Simplex generators and inverse comparison components retain their finite
    computations through the induced-category and natural-isomorphism layers. *)

(** 单纯生成映射及比较的逆分量通过诱导范畴与自然同构层后仍保留有限计算行为。 *)

Example coface_position_computes
  : fin_rank (δ[0%nat; fin_first] fin_first) = 1%nat.
Proof. reflexivity. Qed.

Example codegeneracy_position_computes
  : σ[0%nat; fin_first] (fin_next fin_first) = fin_first.
Proof. reflexivity. Qed.

Example simplex_inverse_comparison_computes
  : ((codegeneracy_coface_id (n := 0%nat) fin_first).2 fin_first).1 = tt.
Proof. reflexivity. Qed.
