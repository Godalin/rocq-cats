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

Program Definition ArrowObjectsF
  : Fct (EqGpd BoolS) ArrowShape
  :=
  {|fobj b := b
  ; fmap x y p := _
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation. destruct p. destruct x; exact tt. Defined.
Next Obligation. intros p q H. exact tt. Defined.
Next Obligation. exact tt. Defined.
Next Obligation. exact tt. Defined.

Definition TerminalObjectsF
  : Fct (EqGpd UnitS@{Set Set}) (CodiscreteCat@{Set Set Set Set} unit)
  := VtxTerminalObjF@{Set Set Set Set Set Set Set Set}.

Program Definition EndpointVertexF (b : bool)
  : TerminalObjectsF →ᵥ ArrowObjectsF
  := MakeVtxFct (ConstF (VtxCat TerminalObjectsF)
      (C := VtxCat ArrowObjectsF) b)
    {|vertex_fct_ob_proper := _
    ; vertex_fct_transport := _
    |}.
Next Obligation. intros x y p. reflexivity. Defined.
Next Obligation. exact tt. Defined.

Program Definition ArrowTransformation
  : EndpointVertexF false ⇒ EndpointVertexF true
  :=
  {|nt x := tt
  |}.
Next Obligation. exact tt. Qed.

Definition ArrowNerve
  : Fct (Δ^op) SetCat@{Set Set _ _ _ _ _}
  := Nᵥ(ArrowObjectsF).

Definition TerminalNerve
  : Fct (Δ^op) SetCat@{Set Set _ _ _ _ _}
  := Nᵥ(TerminalObjectsF).

Definition ArrowHomotopy
  : SimplicialHomotopy
      (VtxNerveN (EndpointVertexF false) : TerminalNerve ⇒ ArrowNerve)
      (VtxNerveN (EndpointVertexF true))
  := VtxNerveHomotopy ArrowTransformation.

(** A constant input edge and the generic time edge evaluate the stored
    witness, including its two distinct endpoint labels. *)

Definition terminal_edge
  : TerminalNerve 1
  := ⟨ConstF [Ord 1] (C := VtxCat TerminalObjectsF) tt⟩ᵥ.

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

Example nerve_endpoints_remain_distinct
  : ¬ ((VtxNerveN (EndpointVertexF false) : TerminalNerve ⇒ ArrowNerve)
      ≈N VtxNerveN (EndpointVertexF true)).
Proof.
  intros H.
  pose proof (fst (vertex_nerve_zero_eq_iff _ _)
    (H 0 (△₀[TerminalObjectsF] tt))) as E.
  discriminate E.
Qed.

(** A non-thin target detects the actual component arrow as well. In the
    xor monoid the nonidentity central loop defines a self-transformation. *)


Definition BooleanObjectsF
  : Fct (EqGpd UnitS@{Set Set})
      B(BoolS_Monoid)
  := MonoidObjF BoolS_Monoid.

Definition BooleanIdentityF
  : BooleanObjectsF →ᵥ BooleanObjectsF
  := VtxIdF BooleanObjectsF.

Program Definition BooleanLoopTransformation
  : BooleanIdentityF ⇒ BooleanIdentityF
  :=
  {|nt x := true
  |}.
Next Obligation. destruct f; reflexivity. Qed.

Definition BooleanVertexNerve
  : Fct (Δ^op) SetCat@{Set Set _ _ _ _ _}
  := Nᵥ(BooleanObjectsF).

Definition BooleanLoopHomotopy
  : SimplicialHomotopy
      (VtxNerveN BooleanIdentityF : BooleanVertexNerve ⇒ BooleanVertexNerve)
      (VtxNerveN BooleanIdentityF)
  := VtxNerveHomotopy BooleanLoopTransformation.

Definition boolean_constant_edge
  : BooleanVertexNerve 1
  := ⟨ConstF [Ord 1] (C := VtxCat BooleanObjectsF) tt⟩ᵥ.

Example nonidentity_component_is_retained
  : fmap (lower (homotopy_map BooleanLoopHomotopy 1
      (boolean_constant_edge, simplex_generic 1)))
      (ordinal_step fin_first) = true.
Proof. reflexivity. Qed.

Example identity_component_is_constant
  : fmap (lower (homotopy_map
      (VtxNerveHomotopy (F := BooleanIdentityF)
        (IdN : BooleanIdentityF ⇒ BooleanIdentityF) :
          SimplicialHomotopy
            (VtxNerveN BooleanIdentityF :
              BooleanVertexNerve ⇒ BooleanVertexNerve)
            (VtxNerveN BooleanIdentityF)) 1
      (boolean_constant_edge, simplex_generic 1)))
      (ordinal_step fin_first) = false.
Proof. reflexivity. Qed.
