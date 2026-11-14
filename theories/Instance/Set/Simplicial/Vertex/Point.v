From Cats Require Export
  Instance.Set.Simplicial.Vertex.Core.
From Cats Require Import
  Cat.Diagram.Core.

Local Open Scope nat_scope.

(** * Vertices as Zero-Simplices

    A zero-simplex retains one object label. Taking that label and building
    the constant ordinal diagram are mutually inverse in specified equality,
    without equality of functor records or their law fields. *)

(** * 顶点作为零单形

    零单形保留一个对象标签。取出标签与构造常值序数图式在指定相等下互逆，
    无需函子记录或其定律字段的相等。 *)

(** Include an object label as a zero-simplex, preserving its equality. *)

(** 将对象标签作为零单形，并保持其相等。 *)

Program Definition point_simplex_resp@{u p +} {X : SetC} {C : Cat}
    (T : Fct (EqGpd X) C)
  : X →r (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 0
  :=
  {|func x := ⟨ConstF [Ord 0] (C := VertexCat T) x⟩ᵥ
  |}.
Next Obligation.
  intros x y H. apply (snd (vertex_nerve_zero_eq_iff _ _)). exact H.
Defined.

Notation "'△₀[' T ']'" := (point_simplex_resp T) : hom_scope.

(** Extract the sole vertex, at its native object-setoid size. *)

(** 在对象广集的原生大小中提取唯一顶点。 *)

Program Definition vertex_zero_resp@{u p +} {X : SetC} {C : Cat}
    (T : Fct (EqGpd X) C)
  : (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 0 →r X
  :=
  {|func x := lower x fin_first
  |}.
Next Obligation.
  intros x y H. exact (fst (vertex_nerve_zero_eq_iff x y) H).
Defined.

(** Extracting an included vertex returns its original label. *)

(** 提取包含的顶点返回原标签。 *)

Lemma vertex_zero_β@{u p +} {X : SetC} {C : Cat}
    {T : Fct (EqGpd X) C} (x : X)
  : vertex_zero_resp T ((△₀[T] : _ →r
      (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 0) x) ≈S x.
Proof. reflexivity. Defined.

(** Rebuilding a zero-simplex from its vertex loses no specified data. *)

(** 从顶点重建零单形不丢失指定数据。 *)

Lemma vertex_zero_η@{u p +} {X : SetC} {C : Cat}
    {T : Fct (EqGpd X) C}
    (x : (Nᵥ(T) : Fct (Δ^op) SetCat@{u p _ _ _ _ _}) 0)
  : △₀[T] (vertex_zero_resp T x) ≈S x.
Proof. apply (snd (vertex_nerve_zero_eq_iff _ _)). reflexivity. Defined.
