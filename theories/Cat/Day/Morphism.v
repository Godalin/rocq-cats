From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Functor.Product
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.Terminal
  Cat.Monoidal.Cartesian.
From Cats Require Export
  Cat.Day.Monoid
  Cat.Monoidal.Natural.

(** * Preservation of Day Monoid Operations *)

(** * Day 幺半群运算的保持性 *)

(** ** Unit Preservation through Lifted Yoneda

    Fix one base object, two setoid-valued functors and their candidate unit
    transformations. The existing Yoneda round trip detects preservation
    at the identity value; no convolution or monoidal structure is needed. *)

(** ** 经提升 Yoneda 的单位保持性

    固定基对象、两个广集值函子及其候选单位变换。已有 Yoneda 往返在恒等值处
    检验保持性，不需要卷积或幺半结构。 *)

Section UnitPreservation.
Universes u p.
Context {C : Cat} (I : @Ob C)
    (F G : Fct C (SetCat@{u p _ _ _ _ _}))
    (η : DayUnitF I ⇒ F) (θ : DayUnitF I ⇒ G) (α : F ⇒ G).

(** A unit square commutes exactly when the selected values are preserved. *)

(** 单位方块交换，当且仅当选定值被保持。 *)

Theorem day_unit_hom_law
  : ((α ∘Nv η) ≈N θ) ↔
      (α I (day_unit_value I F η) ≈S day_unit_value I G θ).
Proof.
  split; intros H.
  - exact (H I {|lower := id|}).
  - intros X [j].
    transitivity (α X (fmap F j (day_unit_value I F η))).
    + apply (@func_proper _ _ (α X)). symmetry.
      exact (day_unit_extend_value I F η X {|lower := j|}).
    + transitivity (fmap G j (α I (day_unit_value I F η))).
      * exact (nt_naturality α j (day_unit_value I F η)).
      * transitivity (fmap G j (day_unit_value I G θ)).
        -- exact (@func_proper _ _ (fmap G j) _ _ H).
        -- exact (day_unit_extend_value I G θ X {|lower := j|}).
Defined.

End UnitPreservation.

(** ** Binary Preservation through the Day Universal Correspondence

    Fix a binary base functor and only the two endpoint convolutions.
    Candidate multiplications and a natural transformation need no laws.
    Restriction and extension compare the full multiplication square with
    its equation on ordinary pairs, without unfolding the selected coends. *)

(** ** 经 Day 泛对应的二元保持性

    固定二元基函子及仅两个端点卷积。候选乘法和自然变换不必满足定律。
    限制与延拓将完整乘法方块与通常值对上的方程比较，不展开选定 coend。 *)

Section BinaryPreservation.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C)
    (F G : Fct C (SetCat@{u p _ _ _ _ _}))
    `{HF : !HasDay C T F F} `{HG : !HasDay C T G G}
    (μ : DayF T F F ⇒ F) (ν : DayF T G G ⇒ G) (α : F ⇒ G).

(** Restrict the transformed multiplication by the original map computation. *)

(** 通过原映射计算律限制变换后的乘法。 *)

Lemma day_mul_hom_restrict (a b : @Ob C) (x : F a) (y : F b)
  : DayRestrictN T (ν ∘Nv DayMapN T α α) (a,b) (x,y) ≈S
      DayRestrictN T ν (a,b) (α a x,α b y).
Proof.
  exact (@func_proper _ _ (ν (T (a,b))) _ _
    (day_map_inject T α α (a,b) id x y)).
Defined.

(** Binary preservation can be tested on generating pairs. The reverse
    implication reuses the two inverse universal correspondences. *)

(** 二元保持性可在生成对上检验；反向蕴涵复用两个互逆泛对应。 *)

Theorem day_mul_hom_law
  : ((α ∘Nv μ) ≈N (ν ∘Nv DayMapN T α α)) ↔
      (∀ a b (x : F a) (y : F b),
        α (T (a,b)) (DayRestrictN T μ (a,b) (x,y)) ≈S
        DayRestrictN T ν (a,b) (α a x,α b y)).
Proof.
  split; intros H.
  - intros a b x y.
    transitivity (DayRestrictN T (ν ∘Nv DayMapN T α α) (a,b) (x,y)).
    + exact (H (T (a,b)) (DayGenN T F F (a,b) (x,y))).
    + exact (day_mul_hom_restrict a b x y).
  - transitivity (DayExtendN T (DayRestrictN T (α ∘Nv μ))).
    + symmetry. exact (day_extend_restrict T (α ∘Nv μ)).
    + transitivity (DayExtendN T
        (DayRestrictN T (ν ∘Nv DayMapN T α α))).
      * apply day_extend_proper. intros [a b] [x y].
        transitivity (DayRestrictN T ν (a,b) (α a x,α b y)).
        -- exact (H a b x y).
        -- symmetry. exact (day_mul_hom_restrict a b x y).
      * exact (day_extend_restrict T (ν ∘Nv DayMapN T α α)).
Defined.

End BinaryPreservation.

(** ** The Same Homomorphisms in the Two Presentations

    Fix a monoidal base and the same explicit Day choices as the object
    conversion. The native target keeps its original terminal object and
    products. Compare the reconstructed Day action in natural equality. *)

(** ** 两种呈现中相同的同态

    固定幺半基及与对象转换相同的显式 Day 选择。原生目标保留原终对象与积；
    按自然相等比较重建的 Day 作用。 *)

Section MonoidPreservation.
Universes u p.
Context {C : Cat} (MC : MonoidalCat C)
    (HD : ∀ F G : Fct C (SetCat@{u p _ _ _ _ _}),
      HasDay C (tensorF MC) F G).
Local Existing Instance HD.
Let DM
  : MonoidalCat (FctCat C (SetCat@{u p _ _ _ _ _}))
  := MonoidalDay MC HD.
Let SM
  : MonoidalCat (SetCat@{u p _ _ _ _ _})
  := @CartesianMonoidal SetCat SetCat_HasTerminal SetCat_HasProduct.

(** The selected tensor action agrees with the universal Day action. *)

(** 选定张量作用与泛 Day 作用一致。 *)

Local Lemma day_hom_tensor_map {F G : Fct C (SetCat@{u p _ _ _ _ _})}
    (α : F ⇒ G)
  : @tensor_map _ DM F G F G α α ≈N
      @DayMapN C (tensorF MC) F G F G (HD F F) (HD G G) α α.
Proof.
  exact (day_monoidal_map (tensorF MC) (TensorUnit MC)
    (@monoidal_associator C MC)
    (@monoidal_left_unitor C MC) (@monoidal_right_unitor C MC)
    (@monoidal_pentagon C MC) (@monoidal_triangle C MC) HD α α).
Defined.

(** A Day monoid homomorphism is exactly a monoidal transformation of the
    restricted lax functors. Witnesses are transferred, not identified. *)

(** Day 幺半群同态恰好是限制所得 lax 函子之间的幺半变换；运输而不识别见证。 *)

Theorem day_monoid_hom_laws (M N : MonoidObj DM)
    (α : MonoidCarrier M ⇒ MonoidCarrier N)
  : is_monoid_hom M N α ↔
      is_lax_monoidal_hom (DayMonoidLax MC HD M) (DayMonoidLax MC HD N) α.
Proof.
  split; intros [Hu Hm]; split.
  - intros []. exact (fst (day_unit_hom_law (TensorUnit MC)
      (MonoidCarrier M) (MonoidCarrier N)
      (monoid_object_unit M) (monoid_object_unit N) α) Hu).
  - assert (H : (α ∘Nv monoid_object_mul M) ≈N
      (monoid_object_mul N ∘Nv DayMapN (tensorF MC) α α)).
    { rewrite <- (day_hom_tensor_map α). exact Hm. }
    intros a b [x y].
    exact (fst (day_mul_hom_law (tensorF MC)
      (MonoidCarrier M) (MonoidCarrier N)
      (monoid_object_mul M) (monoid_object_mul N) α) H a b x y).
  - apply (snd (day_unit_hom_law (TensorUnit MC)
      (MonoidCarrier M) (MonoidCarrier N)
      (monoid_object_unit M) (monoid_object_unit N) α)).
    exact (Hu tt).
  - pose proof (snd (day_mul_hom_law (tensorF MC)
      (MonoidCarrier M) (MonoidCarrier N)
      (monoid_object_mul M) (monoid_object_mul N) α)
      (λ a b x y, Hm a b (x,y))) as H.
    rewrite <- (day_hom_tensor_map α) in H. exact H.
Defined.

(** The lax operation round trips transfer the same preservation diagrams. *)

(** Lax 运算往返运输相同的保持性交换图。 *)

Lemma day_lax_hom_roundtrip (L K : LaxMonoidalFct MC SM) (α : L ⇒ K)
  : is_lax_monoidal_hom
      (DayMonoidLax MC HD (LaxDayMonoid MC HD L))
      (DayMonoidLax MC HD (LaxDayMonoid MC HD K)) α ↔
    is_lax_monoidal_hom L K α.
Proof.
  unfold is_lax_monoidal_hom.
  split; intros [Hu Ht]; split.
  - rewrite (day_lax_unit_roundtrip MC HD L),
      (day_lax_unit_roundtrip MC HD K) in Hu. exact Hu.
  - intros X Y.
    specialize (Ht X Y).
    rewrite (day_lax_tensor_roundtrip MC HD L (X,Y)),
      (day_lax_tensor_roundtrip MC HD K (X,Y)) in Ht. exact Ht.
  - rewrite (day_lax_unit_roundtrip MC HD L),
      (day_lax_unit_roundtrip MC HD K). exact Hu.
  - intros X Y.
    rewrite (day_lax_tensor_roundtrip MC HD L (X,Y)),
      (day_lax_tensor_roundtrip MC HD K (X,Y)). exact (Ht X Y).
Defined.

(** Conversely, a monoidal transformation extends to a Day monoid
    homomorphism on the original underlying natural transformation. *)

(** 反之，幺半变换在原底层自然变换上延拓为 Day 幺半群同态。 *)

Theorem lax_day_monoid_hom (L K : LaxMonoidalFct MC SM) (α : L ⇒ K)
  : is_lax_monoidal_hom L K α ↔
      is_monoid_hom (LaxDayMonoid MC HD L) (LaxDayMonoid MC HD K) α.
Proof.
  split; intros H.
  - apply (snd (day_monoid_hom_laws
      (LaxDayMonoid MC HD L) (LaxDayMonoid MC HD K) α)).
    exact (snd (day_lax_hom_roundtrip L K α) H).
  - apply (fst (day_lax_hom_roundtrip L K α)).
    exact (fst (day_monoid_hom_laws
      (LaxDayMonoid MC HD L) (LaxDayMonoid MC HD K) α) H).
Defined.

End MonoidPreservation.
