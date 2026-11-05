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
  Instance.Bool.Action
  Instance.Bool.Group
  Instance.Bool.Nerve
  Instance.Set.Simplicial.Nerve.

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

(** Yoneda reconstruction through a standard simplex and a coface retains
    the concrete finite-position computation, including the size wrappers. *)

(** 经由标准单形和余面的 Yoneda 重构保留具体有限位置计算，包括大小包装。 *)

Example simplex_yoneda_reconstruction_computes
  : fin_rank (lower
      (⟦simplex_generic 1%nat⟧Δ[Δ[1%nat]; 1%nat] 0%nat
        {|lower := δ[0%nat; fin_first]
        |}) fin_first) = 1%nat.
Proof. reflexivity. Qed.

(** A face followed by the inverse standard-nerve comparison keeps its
    finite-position computation through both general constructions. *)

(** 面后接标准单形与 nerve 比较的逆映射，经过两个一般构造后仍保持有限位置计算。 *)

Example standard_nerve_inverse_face_computes
  : fin_rank (lower (((standard_nerve_iso 1%nat).2 0%nat).1
      (d[N≅([Ord 1%nat]); 0%nat; fin_first]
        ⟨@IdF [Ord 1%nat]⟩N)) fin_first) = 1%nat.
Proof. reflexivity. Qed.

(** The identity-law comparison retains its inverse through the general
    induced inclusion and probe-presheaf construction. *)

(** 恒等律的比较经过一般诱导嵌入和探测预层构造后，仍保留其逆的计算。 *)

Example nerve_identity_inverse_computes
  : ((lower (functor_id _ _ (N≅([Ord 1%nat]))
      ⟨@IdF [Ord 1%nat]⟩N)).2 fin_first).1 = tt.
Proof. reflexivity. Qed.

(** The equality of comparison images retains the nontrivial boolean
    inverse component through chain products and the groupoid boundary. *)

(** 比较像的相等经过箭头链段积与群胚边界后，仍保留非平凡布尔逆分量的计算。 *)

Example monoid_nerve_comparison_inverse_computes
  : ((lower bool_nerve_comparison_identifies_loops).2
      (fin_next fin_first)).1 = true.
Proof. reflexivity. Qed.

(** The inverse singleton comparison extracts the original loop after the
    general vertex-nerve construction, including its explicit size wrappers. *)

(** 单对象比较的逆经过一般顶点 nerve 及显式大小包装，仍提取出原来的环路。 *)

Example vertex_nerve_monoid_inverse_computes
  : lower (((monoid_vertex_iso (M := BoolS)).2 1%nat).1
      (BoolVertexComparison 1%nat {|lower := bool_nerve_loop
                                  |})) fin_first = true.
Proof. reflexivity. Qed.
