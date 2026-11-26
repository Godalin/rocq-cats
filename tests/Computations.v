From Cats Require Import
  Instance.Set.Simplicial.Vertex.Reconstruction
  Instance.Set.Simplicial.Vertex.Coskeletal
  Instance.Set.Simplicial.Vertex.Outer.
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
  Instance.Set.Simplicial.Vertex.Spine
  Instance.Set.Simplicial.Nerve.
From Cats Require Import
  Cat.Adjunction
  Cat.Monad.Adjunction
  Cat.Monad.Monoid
  Instance.Set.Monoid.

(** Concrete monoid multiplication and adjunction-induced monad operations
    must compute through the general monoidal interfaces. *)

Module MonoidalComputations.
Local Open Scope monoidal_scope.

Definition BoolObject
  := SetMonoidObj BoolS_Monoid.

Example monoid_obj_mul_computes
  : m[BoolObject] (true, false) = true.
Proof. reflexivity. Qed.

Definition IdentityOfAdj
  := AdjMonad (IdAdj SetCat).

Example adjunction_monad_unit_computes
  : monad_unit IdentityOfAdj BoolS true = true.
Proof. reflexivity. Qed.

Example adjunction_monad_mul_computes
  : monad_mul IdentityOfAdj BoolS false = false.
Proof. reflexivity. Qed.

(** Converting through the categorical characterization preserves both
    computations, independently of the reconstructed law witnesses. *)

Example monad_monoid_roundtrip_computes
  : (monad_unit (MonoidMonad (MonadMonoid IdentityOfAdj)) BoolS true,
      monad_mul (MonoidMonad (MonadMonoid IdentityOfAdj)) BoolS false)
      = (true, false).
Proof. reflexivity. Qed.

End MonoidalComputations.

From Cats Require Import
  Cat.Monoidal.Constant
  Cat.Monoidal.Transport
  Instance.Set.Product.

(** A constant Boolean-xor lax functor exercises genuinely noninvertible
    comparisons. Transported operations must still compute through the
    general monoid construction, including its stored law witnesses. *)

Module LaxMonoidalComputations.
Local Open Scope monoidal_scope.

Definition BoolObject
  := SetMonoidObj BoolS_Monoid.

Definition BoolConstantLax
  : LaxMonoidalFct SetCat SetCat
  := ConstLaxMonoidalF BoolObject.

Definition BoolConstantImage
  := LaxMonoidObj BoolConstantLax BoolObject.

(** The bundled structure acts directly as a functor, through its unique
    underlying-functor coercion and without changing computation. *)

Example constant_lax_fmap_computes
  : fmap BoolConstantLax (@Cats.Cat.Core.id SetCat BoolS) true = true.
Proof. reflexivity. Qed.

Example constant_lax_unit_not_iso
  : ¬ is_iso φ₀[BoolConstantLax].
Proof.
  intros [g [_ H]]. specialize (H true). discriminate H.
Qed.

Example constant_lax_tensor_not_iso
  : ¬ is_iso φ₂[BoolConstantLax; BoolS; BoolS].
Proof.
  intros [g [H _]].
  change (BoolS →r (BoolS ×S BoolS)) in g.
  change (∀ p : bool * bool,
    ProdEq eq eq (g (xorb (fst p) (snd p))) p) in H.
  pose proof (H (false, false)) as Hf.
  pose proof (H (true, true)) as Ht.
  cbn in Hf, Ht. destruct (g false) as [b c].
  cbn in Hf, Ht.
  destruct Hf as [Hf _], Ht as [Ht _].
  rewrite Hf in Ht. discriminate Ht.
Qed.

Example transported_constant_unit_computes
  : e[BoolConstantImage] tt = false.
Proof. reflexivity. Qed.

Example transported_constant_mul_computes
  : m[BoolConstantImage] (true, true) = false.
Proof. reflexivity. Qed.

End LaxMonoidalComputations.

(** A monoidal functor inherits lax computations, while its inverse
    tensorator must also reduce through the derived natural transformation. *)

Module MonoidalFctComputations.

Definition SetIdentity
  := IdMonoidalF (MC := SetCartMonoidal).

Example monoidal_identity_fmap_computes
  : fmap SetIdentity (@Cats.Cat.Core.id SetCat BoolS) true = true.
Proof. reflexivity. Qed.

Example monoidal_identity_unit_inverse_computes
  : (MonoidalUnitIso SetIdentity).2.1 tt = tt.
Proof. reflexivity. Qed.

Example monoidal_identity_tensor_computes
  : (MonoidalTensorIso SetIdentity).1 (BoolS, BoolS) (true, false)
      = (true, false).
Proof. reflexivity. Qed.

Example monoidal_identity_tensor_inverse_computes
  : MonoidalTensorInvN SetIdentity (BoolS, BoolS) (false, true)
      = (false, true).
Proof. reflexivity. Qed.

End MonoidalFctComputations.

From Cats Require Import
  Algebra.Magma.Core
  Cat.Product.Core
  Cat.Monoidal.Bifct
  Cat.Monoidal.Cartesian.

(** Grouping the context laws must preserve which tensor factor is mapped. *)

Module BinoidalComputations.

Definition ProductBinoidal
  := BifctBinoidal (@ProductF SetCat SetCat_HasProduct).

Definition Flip
  := mul_l_resp (M := BoolS_Magma) true.

Example left_context_computes
  : fmap (@TensorAtLF SetCat (hasBinoidal ProductBinoidal) BoolS)
      Flip (true, false) = (true, true).
Proof. reflexivity. Qed.

Example right_context_computes
  : fmap (@TensorAtRF SetCat (hasBinoidal ProductBinoidal) BoolS)
      Flip (true, false) = (false, false).
Proof. reflexivity. Qed.

End BinoidalComputations.

(** Shared natural-isomorphism views and the complete bundle retain the
    original structural inverses through the new intermediate packages. *)

Module PremonoidalComputations.

Definition ProductPremonoidal
  : PremonoidalCat
  := MonoidalCatToPremonoidalCat
      (@CartMonoidal SetCat SetCat_HasTerminal SetCat_HasProduct).

Example middle_associator_inverse_computes
  : ((@TensorAssocMIso SetCat _
      (PremonoidalCat_associator ProductPremonoidal) BoolS BoolS).2
      BoolS).1 (true, (false, true)) = ((true, false), true).
Proof. reflexivity. Qed.

Example bundled_unitor_inverse_computes
  : ((@TensorUnitorLIso SetCat _
      (PremonoidalCat_unitors ProductPremonoidal)).2
      BoolS).1 false = (tt, false).
Proof. reflexivity. Qed.

End PremonoidalComputations.

From Cats Require Import
  Cat.CCC.Functor
  Cat.CCC.Core
  Instance.Set.CCC.

(** The inherited CCC evidence must keep product mediators and exponential
    inverses computational, including after bundled composition. *)

Module BundledCCCComputations.

Definition IdentityCCC
  := IdCCCF SetCat_CCC.
Definition CompositeCCC
  := CompCCCF IdentityCCC IdentityCCC.

Example bundled_ccc_fmap_computes
  : fmap CompositeCCC (@Cats.Cat.Core.id SetCat BoolS) true = true.
Proof. reflexivity. Qed.

Example bundled_ccc_product_inverse_computes
  : fct_product_inv CompositeCCC BoolS BoolS (true, false)
      = (true, false).
Proof. reflexivity. Qed.

Example bundled_ccc_exp_inverse_computes
  : (fct_exp (PreservesExp := CCCFct_preservesExp CompositeCCC) BoolS BoolS).1 id_resp true = true.
Proof. reflexivity. Qed.
End BundledCCCComputations.

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

Example boolean_action_inverse_computes
  : bool_action_loop_iso.1 false = true.
Proof. reflexivity. Qed.

(** Simplex generators and inverse comparison components retain their finite
    computations through the induced-category and natural-isomorphism layers. *)

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

Example simplex_yoneda_reconstruction_computes
  : fin_rank (lower
      (⟦simplex_generic 1%nat⟧Δ[Δ[1%nat]; 1%nat] 0%nat
        {|lower := δ[0%nat; fin_first]
        |}) fin_first) = 1%nat.
Proof. reflexivity. Qed.

(** A face followed by the inverse standard-nerve comparison keeps its
    finite-position computation through both general constructions. *)

Example standard_nerve_inverse_face_computes
  : fin_rank (lower (((standard_nerve_iso 1%nat).2 0%nat).1
      (d[N≅([Ord 1%nat]); 0%nat; fin_first]
        ⟨@IdF [Ord 1%nat]⟩N)) fin_first) = 1%nat.
Proof. reflexivity. Qed.

(** The identity-law comparison retains its inverse through the general
    induced inclusion and probe-presheaf construction. *)

Example nerve_identity_inverse_computes
  : ((lower (fmap_id (IsFct := isFct (N≅([Ord 1%nat])))
      ⟨@IdF [Ord 1%nat]⟩N)).2 fin_first).1 = tt.
Proof. reflexivity. Qed.

(** The equality of comparison images retains the nontrivial boolean
    inverse component through chain products and the groupoid boundary. *)

Example monoid_nerve_comparison_inverse_computes
  : ((lower bool_nerve_comparison_identifies_loops).2
      (fin_next fin_first)).1 = true.
Proof. reflexivity. Qed.

(** The inverse singleton comparison extracts the original loop after the
    general vertex-nerve construction, including its explicit size wrappers. *)

Example vertex_nerve_monoid_inverse_computes
  : lower (((monoid_vertex_iso (M := BoolS_Monoid)).2 1%nat).1
      (BoolVtxComparison 1%nat {|lower := bool_nerve_loop
                               |})) fin_first = true.
Proof. reflexivity. Qed.

(** Reconstruction computes on a nonidentity boolean loop, through the
    naturality witnesses and endpoint transports of the general inverse. *)

Example vertex_fct_reconstruction_computes
  : fmap (VtxNerveInvF
      (IdN : BoolVtxNerve ⇒ BoolVtxNerve))
      (true : (@Hom (VtxCat (MonoidObjF BoolS_Monoid))) tt tt) = true.
Proof. reflexivity. Qed.

(** The chosen spine inverse reconstructs the original arrow by interval
    evaluation, without an opaque extension witness. *)

Example vertex_spine_inverse_computes
  : let e := vertex_spine_iso
      (MonoidObjF BoolS_Monoid) 1%nat in
    fmap (lower (e.2.1 (e.1
      (BoolVtxComparison 1%nat {|lower := bool_nerve_loop
                               |})))) (ordinal_step fin_first) = true.
Proof. reflexivity. Qed.

Module LocalHornComputation.

(** The dual outer filler retains its missing earlier arrow through
    reversal, inverse restriction, and spine realization. *)

Definition T
  := MonoidObjF BoolS_Monoid.

Local Instance chosen_groupoid
  : (VtxCat T) ⦂ Gpd
  := VtxCat_IsGpd T (HC := BoolGpd_IsGpd).

Example local_horn2_dual_computes
  : fmap (lower ((fill₂[T; tt; tt; tt; fin_next (fin_next fin_first)] :
      _ →r (Nᵥ(T) : Fct (Δ^op) SetCat@{Set Set _ _ _ _ _}) 2%nat)
        (false, true))) (ordinal_step fin_first) = true.
Proof. reflexivity. Qed.

(** Recovering a groupoid from the second outer filling structure keeps
    its inverse computational, independently of the division equations. *)

Example outer_horn2_recovered_inverse_computes
  : @gpd_inv BoolGpd
      (@horn2_2_IsGpd BoolGpd
        (@horn2_HasFillers BoolGpd BoolGpd_IsGpd
          (fin_next (fin_next fin_first)))) tt tt true = true.
Proof. reflexivity. Qed.

End LocalHornComputation.

Module HornFaceComputation.

(** A retained coface followed by actual horn inclusion still computes
    its finite vertex, independently of the stored membership witness. *)

Definition retained_first_face
  : ¬ (fin_first : Ordinal 2%nat) = fin_next fin_first.
Proof. discriminate. Defined.

Example horn_face_inclusion_computes
  : fin_rank (lower (ιΛ[2%nat; fin_next fin_first] 0%nat
      (HornFaceN (fin_next fin_first) fin_first retained_first_face
        0%nat {|lower := δ[0%nat; fin_next fin_first]
               |})) fin_first) = 1%nat.
Proof. reflexivity. Qed.

End HornFaceComputation.

(** An actual outer horn is reconstructed, filled locally, and realized
    again without blocking the computation of its missing edge. *)

Example actual_outer_horn2_filler_computes
  : let T := MonoidObjF BoolS_Monoid in
    let x := (△₂[T; tt; tt; tt] : _ →r
      (Nᵥ(T) : Fct (Δ^op) SetCat@{Set Set _ _ _ _ _}) 2%nat) (true, true) in
    let HF := vertex_gpd_horn2_HasFillers T
      (HC := VtxCat_IsGpd T (HC := BoolGpd_IsGpd)) fin_first in
    fmap (lower (@horn_fill _ _ _ HF (x↾Λ[Nᵥ(T); 2%nat; fin_first])).1)
      (ordinal_step (fin_next fin_first)) = true.
Proof. reflexivity. Qed.

(** Matching descent computes the prescribed long edge before any filler
    or inverse is supplied. *)

Example actual_outer_horn2_descent_computes
  : let T := MonoidObjF BoolS_Monoid in
    let h := (OuterHorn2N T (A := tt) (B := tt) (D := tt) true false :
      HornS (Nᵥ(T) : Fct (Δ^op) SetCat@{Set Set _ _ _ _ _}) 2%nat fin_first) in
    fmap (lower (h 1%nat
      {|lower := (δ[1%nat; fin_next fin_first];
          horn_face_member fin_first (fin_next fin_first)
            (λ E, HornFaceComputation.retained_first_face (eq_sym E)))
      |})) (ordinal_step fin_first) = false.
Proof. reflexivity. Qed.

(** General boundary descent preserves a nontrivial arrow through sieve
    membership, chosen labels and endpoint transport. *)

Example vertex_boundary_filler_computes
  : let x := BoolVtxComparison 3%nat
      {|lower := (true ∷S false ∷S true ∷S []S : BoolS ^S 3%nat)
      |} in
    fmap (lower (@coskeletal_fill_resp BoolVtxNerve 2%nat
      BoolVtxNerve_IsCoskeletal 0%nat
      (x↾∂[BoolVtxNerve; 3%nat]))) (ordinal_step fin_first) = true.
Proof. reflexivity. Qed.

From Cats Require Import
  Cat.FreeObject.Adjunction.

(** Passing through comma initiality, free extension, and the induced monad
    must preserve the computation of actual arrows. *)

Module FreeObjectComputations.

Definition FreeIdentity
  : HasFreeObj (@IdF SetCat)
  := AdjFreeObj (IdAdj SetCat).

Example free_extension_computes
  : @free_object_extend SetCat SetCat IdF FreeIdentity BoolS BoolS
      id_resp true = true.
Proof. reflexivity. Qed.

Example free_monad_multiplication_computes
  : monad_mul (@FreeMonad SetCat SetCat IdF FreeIdentity) BoolS true = true.
Proof. reflexivity. Qed.

End FreeObjectComputations.

From Cats Require Import
  Cat.Diagram.Generator
  Cat.Diagram.Core.

(** A concrete free-diagram counit computes through the general chosen
    comma-initial construction, rather than only through a direct path map. *)

Example generator_counit_computes
  : adj_counit
      (GenFreeAdj (DiscreteGraph unit) SetCat)
      (@ConstF (FreeCat (DiscreteGraph unit)) SetCat BoolS) tt true = true.
Proof. reflexivity. Qed.
