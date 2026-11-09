From Cats Require Export
  Cat.Monoidal.Functor
  Cat.Monoidal.Monoid.
From Cats Require Import
  Cat.Diagram.Core.

Local Open Scope monoidal_scope.

(** * Constant Lax Monoidal Functors

    A monoid object supplies a lax structure on its constant functor,
    from any monoidal source. This construction needs no invertibility
    of the monoid operations and no tensorial strength. *)

(** * 常值 Lax Monoidal 函子

    幺半群对象为从任意幺半来源出发的常函子提供 lax 结构，不要求幺半群运算
    可逆，也不要求张量强度。 *)

Section ConstantLax.
Context {C D : Cat} (MC : MonoidalCategory C)
    {MD : MonoidalCategory D} (A : MonoidObject MD).

(** The multiplication of [A] is the constant tensorator. Naturality
    follows because every source arrow maps to an identity. *)

(** [A] 的乘法就是常值 tensorator；每条来源箭头映为恒等，因而满足自然性。 *)

Program Definition ConstLaxTensorN
  : (tensorF MD ∘F (ConstF C (MonoidCarrier A) ×F
        ConstF C (MonoidCarrier A))) ⇒
      (ConstF C (MonoidCarrier A) ∘F tensorF MC)
  :=
  {|nt p := m[A]
  |}.
Next Obligation.
  rewrite (@functor_id _ _ (tensorF MD)
    (MonoidCarrier A, MonoidCarrier A)), comp_id_r, comp_id_l.
  reflexivity.
Defined.

(** The three lax coherence diagrams are exactly the monoid laws of [A].
    The structure is selected explicitly, rather than registered on import. *)

(** 三条 lax 相干图恰好是 [A] 的幺半群定律；结构须显式选择，不在导入时注册。 *)

Program Definition ConstF_LaxMonoidalFunctor
  : LaxMonoidalFunctor MC MD
  :=
  {|LaxMonoidalF := ConstF C (MonoidCarrier A)
  ; lax_unit := e[A]
  ; lax_tensorN := ConstLaxTensorN
  |}.
Next Obligation. rewrite comp_id_l. apply monoid_object_unit_l. Defined.
Next Obligation. rewrite comp_id_l. apply monoid_object_unit_r. Defined.
Next Obligation. rewrite comp_id_l. apply monoid_object_assoc. Defined.

End ConstantLax.
