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

(** 具体幺半群乘法及伴随诱导的 Monad 运算须能穿过一般幺半接口计算。 *)

Module MonoidalComputations.

Definition BoolObject
  := SetMonoidObj BoolS_Monoid.

Example monoid_object_mul_computes
  : monoid_object_mul BoolObject (true, false) = true.
Proof. reflexivity. Qed.

Definition IdentityFromAdjunction
  := AdjMonad (IdAdj SetCat).

Example adjunction_monad_unit_computes
  : monad_unit IdentityFromAdjunction BoolS true = true.
Proof. reflexivity. Qed.

Example adjunction_monad_mul_computes
  : monad_mul IdentityFromAdjunction BoolS false = false.
Proof. reflexivity. Qed.

(** Converting through the categorical characterization preserves both
    computations, independently of the reconstructed law witnesses. *)

(** 经过范畴刻画的转换保持两个运算的计算，不依赖重新构造的定律见证。 *)

Example monad_monoid_roundtrip_computes
  : (monad_unit (MonoidMonad (MonadMonoid IdentityFromAdjunction)) BoolS true,
      monad_mul (MonoidMonad (MonadMonoid IdentityFromAdjunction)) BoolS false)
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

(** 布尔异或常值 lax 函子检验真正不可逆的比较；传输后的运算仍须穿过一般
    幺半群构造及其保存的定律见证直接计算。 *)

Module LaxMonoidalComputations.
Local Open Scope monoidal_scope.

Definition BoolObject
  := SetMonoidObj BoolS_Monoid.

Definition BoolConstantLax
  := ConstF_LaxMonoidalFct SetCartesianMonoidal BoolObject.

Definition BoolConstantImage
  := LaxMonoidObj BoolConstantLax BoolObject.

(** The bundled structure acts directly as a functor, through its unique
    underlying-functor coercion and without changing computation. *)

(** 打包结构通过唯一的底层函子强制转换直接作为函子使用，计算行为保持不变。 *)

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
  : monoid_object_unit BoolConstantImage tt = false.
Proof. reflexivity. Qed.

Example transported_constant_mul_computes
  : monoid_object_mul BoolConstantImage (true, true) = false.
Proof. reflexivity. Qed.

End LaxMonoidalComputations.

From Cats Require Import
  Cat.Functor.Closed
  Cat.CCC
  Instance.Set.CCC.

(** The inherited CCC evidence must keep product mediators and exponential
    inverses computational, including after bundled composition. *)

(** 继承的 CCC 证据须保持积中介及指数逆的可计算性，包括打包复合之后。 *)

Module BundledCCCComputations.
Local Existing Instance SetCat_CCC.

Definition IdentityCCC
  := IdCCCF SetCat SetCat_CCC.
Definition CompositeCCC
  := CompCCCF IdentityCCC IdentityCCC.

Example bundled_ccc_fmap_computes
  : fmap CompositeCCC (@Cats.Cat.Core.id SetCat BoolS) true = true.
Proof. reflexivity. Qed.

Example bundled_ccc_product_inverse_computes
  : functor_product_inv CompositeCCC BoolS BoolS (true, false)
      = (true, false).
Proof. reflexivity. Qed.

Example bundled_ccc_exponential_inverse_computes
  : (@functor_exponential _ _ CompositeCCC SetCat_CCC SetCat_CCC
      (CCCFct_IsCCCF CompositeCCC) BoolS BoolS).1 id_resp true = true.
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

(** Reconstruction computes on a nonidentity boolean loop, through the
    naturality witnesses and endpoint transports of the general inverse. *)

(** 重构在非恒等布尔环路上穿过一般逆的自然性见证及端点运输进行计算。 *)

Example vertex_functor_reconstruction_computes
  : fmap (VertexNerveInvF
      (idN : BoolVertexNerve ⇒ BoolVertexNerve))
      (true : (@Hom (VertexCat (MonoidObjF BoolS))) tt tt) = true.
Proof. reflexivity. Qed.

(** The chosen spine inverse reconstructs the original arrow by interval
    evaluation, without an opaque extension witness. *)

(** 选定的脊逆映射通过区间求值重构原箭头，不经过不透明的延拓见证。 *)

Example vertex_spine_inverse_computes
  : let e := vertex_spine_iso
      (MonoidObjF BoolS (HM := BoolS_Monoid)) 1%nat in
    fmap (lower (e.2.1 (e.1
      (BoolVertexComparison 1%nat {|lower := bool_nerve_loop
                                  |})))) (ordinal_step fin_first) = true.
Proof. reflexivity. Qed.

Module LocalHornComputation.

(** The dual outer filler retains its missing earlier arrow through
    reversal, inverse restriction, and spine realization. *)

(** 对偶外填充经过反转、限制取逆及脊实现，仍保留缺失先行箭头的计算。 *)

Definition T
  := MonoidObjF BoolS (HM := BoolS_Monoid).

Local Instance chosen_groupoid
  : VertexCat T ⦂ Gpd
  := VertexCat_IsGroupoid T (HC := BoolGroupoid_IsGroupoid).

Example local_horn2_dual_computes
  : fmap (lower ((fill₂[T; tt; tt; tt; fin_next (fin_next fin_first)] :
      _ →r (Nᵥ(T) : Fct (Δ^op) SetCat@{Set Set _ _ _ _ _}) 2%nat)
        (false, true))) (ordinal_step fin_first) = true.
Proof. reflexivity. Qed.

(** Recovering a groupoid from the second outer filling structure keeps
    its inverse computational, independently of the division equations. *)

(** 从第二类外填充恢复群胚后，其逆仍可计算，不受除法方程证明的阻碍。 *)

Example outer_horn2_recovered_inverse_computes
  : @groupoid_inv BoolGroupoid
      (@horn2_2_IsGroupoid BoolGroupoid
        (@horn2_HasFillers BoolGroupoid BoolGroupoid_IsGroupoid
          (fin_next (fin_next fin_first)))) tt tt true = true.
Proof. reflexivity. Qed.

End LocalHornComputation.

Module HornFaceComputation.

(** A retained coface followed by actual horn inclusion still computes
    its finite vertex, independently of the stored membership witness. *)

(** 保留的余面后接实际 horn 包含，仍计算出有限顶点，不受存储的隶属见证影响。 *)

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

(** 实际外 horn 经重构、局部填充及再次实现后，缺失边的计算仍不受阻碍。 *)

Example actual_outer_horn2_filler_computes
  : let T := MonoidObjF BoolS (HM := BoolS_Monoid) in
    let x := (△₂[T; tt; tt; tt] : _ →r
      (Nᵥ(T) : Fct (Δ^op) SetCat@{Set Set _ _ _ _ _}) 2%nat) (true, true) in
    let HF := vertex_groupoid_horn2_HasFillers T
      (HC := VertexCat_IsGroupoid T (HC := BoolGroupoid_IsGroupoid)) fin_first in
    fmap (lower (@horn_fill _ _ _ HF (x↾Λ[Nᵥ(T); 2%nat; fin_first])).1)
      (ordinal_step (fin_next fin_first)) = true.
Proof. reflexivity. Qed.

(** Matching descent computes the prescribed long edge before any filler
    or inverse is supplied. *)

(** 在给出任何填充或逆之前，匹配下降即可计算指定长边。 *)

Example actual_outer_horn2_descent_computes
  : let T := MonoidObjF BoolS (HM := BoolS_Monoid) in
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

(** 一般边界下降穿过筛隶属、选定标签及端点运输后，仍保留非平凡箭头的计算。 *)

Example vertex_boundary_filler_computes
  : let x := BoolVertexComparison 3%nat
      {|lower := (true ∷S false ∷S true ∷S []S : BoolS ^S 3%nat)
      |} in
    fmap (lower (@coskeletal_fill_resp BoolVertexNerve 2%nat
      BoolVertexNerve_IsCoskeletal 0%nat
      (x↾∂[BoolVertexNerve; 3%nat]))) (ordinal_step fin_first) = true.
Proof. reflexivity. Qed.

From Cats Require Import
  Cat.FreeObject.Adjunction.

(** Passing through comma initiality, free extension, and the induced monad
    must preserve the computation of actual arrows. *)

(** 穿过逗号始性、自由延拓及诱导 Monad 后，实际箭头仍须保持可计算。 *)

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

(** 具体自由图式余单位可穿过一般选定逗号始性构造计算，而不仅是直接路径映射。 *)

Example generator_counit_computes
  : adj_counit
      (GenFreeAdj (DiscreteGraph unit) SetCat)
      (@ConstF (FreeCat (DiscreteGraph unit)) SetCat BoolS) tt true = true.
Proof. reflexivity. Qed.
