From Cats Require Import
  Instance.Set.Simplicial.Vertex.Homotopy
  Instance.Set.Vertex.Terminal
  Instance.Set.Simplicial.Vertex.Point
  Instance.Set.Simplicial.Vertex.Monoid
  Instance.Bool.Group
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

Local Open Scope nat_scope.

(** * A Noninvertible Transformation Gives a Computable Homotopy

    The walking arrow has two unequal objects. Its generating arrow gives
    a transformation between constant functors from the terminal
    presentation. The bridge retains this actual directed edge. *)

(** * 不可逆自然变换给出可计算同伦

    步行箭头有两个不相等的对象，其生成箭头给出从终呈现出发的常值函子之间的
    自然变换。此桥梁保留这条实际有向边。 *)

Program Definition ArrowObjectsF
  : Functor (EqGpd BoolS) ArrowShape
  :=
  {|F0 b := b
  ; F1 x y p := _
  |}.
Next Obligation. destruct p. destruct x; exact tt. Defined.
Next Obligation. intros p q H. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

Definition TerminalObjectsF
  : Functor (EqGpd UnitS@{Set Set}) (CodiscreteCat@{Set Set Set Set} unit)
  := VertexTerminalObjectsF@{Set Set Set Set Set Set Set Set}.

Program Definition EndpointVertexF (b : bool)
  : TerminalObjectsF →ᵥ ArrowObjectsF
  :=
  {|vertex_functor := ConstF (VertexCat TerminalObjectsF)
      (C := VertexCat ArrowObjectsF) b
  |}.
Next Obligation. intros x y p. reflexivity. Defined.
Next Obligation. exact tt. Defined.

Program Definition ArrowTransformation
  : EndpointVertexF false ⇒ EndpointVertexF true
  :=
  {|nt x := tt
  |}.
Next Obligation. exact tt. Defined.

Definition ArrowNerve
  : Functor (Δ^op) SetCat@{Set Set _ _ _ _ _}
  := Nᵥ(ArrowObjectsF).

Definition TerminalNerve
  : Functor (Δ^op) SetCat@{Set Set _ _ _ _ _}
  := Nᵥ(TerminalObjectsF).

Definition ArrowHomotopy
  : SimplicialHomotopy
      (VertexNerveN (EndpointVertexF false) : TerminalNerve ⇒ ArrowNerve)
      (VertexNerveN (EndpointVertexF true))
  := VertexNerveHomotopy ArrowTransformation.

(** A constant input edge and the generic time edge evaluate the stored
    witness, including its two distinct endpoint labels. *)

(** 常值输入边与泛时间边对所存见证求值，并保留两个不同的端点标签。 *)

Definition terminal_edge
  : TerminalNerve 1
  := ⟨ConstF [Ord 1] (C := VertexCat TerminalObjectsF) tt⟩ᵥ.

Definition prism_edge
  : ArrowNerve 1
  := homotopy_map ArrowHomotopy 1 (terminal_edge, simplex_generic 1).

Example prism_initial_vertex_computes
  : lower prism_edge fin_first = false.
Proof. reflexivity. Qed.

Example prism_final_vertex_computes
  : lower prism_edge (fin_next fin_first) = true.
Proof. reflexivity. Qed.

Example prism_time_arrow_computes
  : fmap (lower prism_edge) (ordinal_step fin_first) = tt.
Proof. reflexivity. Qed.

Example transformation_has_no_inverse
  : ¬ is_iso (ArrowTransformation tt).
Proof. intros [g H]. destruct g. Qed.

(** Evaluate both endpoint restrictions of the actual stored map. *)

(** 对实际所存映射的两个端点限制作求值。 *)

Example initial_restriction_computes
  : lower (homotopy_map ArrowHomotopy 1
      (SimplicialEndpointN TerminalNerve false 1 terminal_edge))
      fin_first = false.
Proof. reflexivity. Qed.

Example final_restriction_computes
  : lower (homotopy_map ArrowHomotopy 1
      (SimplicialEndpointN TerminalNerve true 1 terminal_edge))
      fin_first = true.
Proof. reflexivity. Qed.

(** These two maps are homotopic while retaining unequal vertex images. *)

(** 这两个映射具有同伦，同时仍保留不相等的顶点像。 *)

Example nerve_endpoints_remain_distinct
  : ¬ ((VertexNerveN (EndpointVertexF false) : TerminalNerve ⇒ ArrowNerve)
      ≈N VertexNerveN (EndpointVertexF true)).
Proof.
  intros H.
  pose proof (fst (vertex_nerve_zero_eq_iff _ _)
    (H 0 (△₀[TerminalObjectsF] tt))) as E.
  discriminate E.
Qed.

(** A non-thin target detects the actual component arrow as well. In the
    xor monoid the nonidentity central loop defines a self-transformation. *)

(** 非薄目标还可检验实际分量箭头。异或幺半群的非恒等中心环路定义一个自变换。 *)

Local Existing Instance BoolS_Monoid.

Definition BooleanObjectsF
  : Functor (EqGpd UnitS@{Set Set})
      B(BoolS)
  := MonoidObjectsF BoolS (HM := BoolS_Monoid).

Definition BooleanIdentityF
  : BooleanObjectsF →ᵥ BooleanObjectsF
  := VertexIdF BooleanObjectsF.

Program Definition BooleanLoopTransformation
  : BooleanIdentityF ⇒ BooleanIdentityF
  :=
  {|nt x := true
  |}.
Next Obligation. destruct f; reflexivity. Defined.

Definition BooleanVertexNerve
  : Functor (Δ^op) SetCat@{Set Set _ _ _ _ _}
  := Nᵥ(BooleanObjectsF).

Definition BooleanLoopHomotopy
  : SimplicialHomotopy
      (VertexNerveN BooleanIdentityF : BooleanVertexNerve ⇒ BooleanVertexNerve)
      (VertexNerveN BooleanIdentityF)
  := VertexNerveHomotopy BooleanLoopTransformation.

Definition boolean_constant_edge
  : BooleanVertexNerve 1
  := ⟨ConstF [Ord 1] (C := VertexCat BooleanObjectsF) tt⟩ᵥ.

Example nonidentity_component_is_retained
  : fmap (lower (homotopy_map BooleanLoopHomotopy 1
      (boolean_constant_edge, simplex_generic 1)))
      (ordinal_step fin_first) = true.
Proof. reflexivity. Qed.

Example identity_component_is_constant
  : fmap (lower (homotopy_map
      (VertexNerveHomotopy (F := BooleanIdentityF)
        (idN : BooleanIdentityF ⇒ BooleanIdentityF) :
          SimplicialHomotopy
            (VertexNerveN BooleanIdentityF :
              BooleanVertexNerve ⇒ BooleanVertexNerve)
            (VertexNerveN BooleanIdentityF)) 1
      (boolean_constant_edge, simplex_generic 1)))
      (ordinal_step fin_first) = false.
Proof. reflexivity. Qed.
