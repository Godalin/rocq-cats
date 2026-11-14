From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.Product
  Cat.Natural
  Cat.Isomorphism
  Cat.Monoidal.Functor
  Cat.Monoidal.Cartesian
  Instance.Set.Core
  Instance.Set.Lift
  Instance.Set.Hom
  Instance.Set.Yoneda
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Representable.
From Cats Require Export
  Cat.Day.Monoidal
  Cat.Monoidal.Monoid.

(** * Day Monoids and Lax Monoidal Functors *)

(** * Day 幺半群与 Lax Monoidal 函子 *)

(** ** The Representable Unit Correspondence

    Fix an object and a setoid-valued functor at independent ambient
    carrier/equality sizes. Lifted Yoneda reconstructs a transformation
    from its value at the identity. No convolution choice is needed. *)

(** ** 可表单位对应

    固定对象和环境载体／相等大小相互独立的广集值函子。提升 Yoneda 从恒等处
    的值重构变换，不需要卷积选择。 *)

Section UnitCorrespondence.
Universes u p.
Context {C : Cat} (I : @Ob C)
    (F : Fct C (SetCat@{u p _ _ _ _ _})).

(** Extract the value classifying a map from the representable unit. *)

(** 提取分类可表单位出射映射的值。 *)

Definition day_unit_value (η : DayUnitF I ⇒ F)
  : F I
  := η I {|lower := id|}.

(** Reuse lifted Yoneda to extend a chosen unit value naturally. *)

(** 复用提升 Yoneda，将选定单位值自然地延拓。 *)

Definition DayUnitExtendN (e : F I)
  : DayUnitF I ⇒ F
  := LiftedYonedaN F e.

(** Evaluation after extension recovers the selected value. *)

(** 延拓后求值恢复选定值。 *)

Lemma day_unit_value_extend (e : F I)
  : day_unit_value (DayUnitExtendN e) ≈S e.
Proof. exact (@functor_id C SetCat F I e). Defined.

(** Reindex the same components along the double opposite for Yoneda. *)

(** 沿双反范畴重新包装相同分量，以便应用 Yoneda。 *)

Local Program Definition DayUnitOpN (η : DayUnitF I ⇒ F)
  : (LiftF ∘F (ℎ2F (C := C^op) I)) ⇒
      (F ∘F (FromDoubleOpF (C := C)))
  :=
  {|nt X := _
  |}.
Next Obligation. exact (η X). Defined.
Next Obligation. exact (nt_naturality η f). Defined.

(** Extension after evaluation reuses presheaf Yoneda on the opposite,
    just as the existing lifted covariant construction does. *)

(** 求值后延拓在反范畴上复用预层 Yoneda，与已有提升协变构造一致。 *)

Lemma day_unit_extend_value (η : DayUnitF I ⇒ F)
  : DayUnitExtendN (day_unit_value η) ≈N η.
Proof.
  intros X [j].
  exact (presheaf_yoneda_η (C := C^op)
    (P := F ∘F (FromDoubleOpF (C := C))) (DayUnitOpN η) X {|lower := j|}).
Defined.

(** Unit extension preserves the specified equality of values. *)

(** 单位延拓保持值的指定相等。 *)

Lemma day_unit_extend_proper (e e' : F I) (H : e ≈S e')
  : DayUnitExtendN e ≈N DayUnitExtendN e'.
Proof. intros X [j]. exact (@func_proper _ _ (fmap F j) e e' H). Defined.

End UnitCorrespondence.

(** ** The Native Cartesian Tensorator

    Fix a monoidal base and the existing explicit finite products on the
    value setoids. The derived cartesian tensor action is compared with
    the external value pair; their functor records are not identified. *)

(** ** 原生笛卡尔 Tensorator

    固定幺半基底和已有显式选定的值广集有限积。比较导出的笛卡尔张量作用
    与外部值对，不识别它们的函子记录。 *)

Section NativeTensorator.
Universes u p.
Context {C : Cat} (MC : MonoidalCat C).
Let SM
  : MonoidalCat (SetCat@{u p _ _ _ _ _})
  := @CartesianMonoidal SetCat SetCat_HasTerminal SetCat_HasProduct.

(** Regard a lax tensorator as the natural binary operation required by
    Day extension. Only the tensor-map comparison is necessary. *)

(** 将 lax tensorator 看作 Day 延拓所需的自然二元操作，只需张量映射比较。 *)

Program Definition LaxDayTensorN (L : LaxMonoidalFct MC SM)
  : DayValuesF L L ⇒ (L ∘F tensorF MC)
  :=
  {|nt q := lax_tensorN L q
  |}.
Next Obligation.
  destruct X as [X1 X2], Y as [Y1 Y2], f as [f g].
  pose proof (nt_naturality (lax_tensorN L)
    (X := (X1,X2)) (Y := (Y1,Y2)) (f,g)) as H.
  change (lax_tensorN L (Y1,Y2) ∘
    @tensor_map SetCat SM _ _ _ _ (fmap L f) (fmap L g) ≈
    fmap L (fmap (tensorF MC) (X := (X1,X2)) (Y := (Y1,Y2)) (f,g)) ∘
      lax_tensorN L (X1,X2)) in H.
  intros [x y]. exact (H (x,y)).
Defined.

(** Restore the native cartesian tensorator from a binary operation. *)

(** 从二元操作恢复原生笛卡尔 tensorator。 *)

Program Definition DayLaxTensorN
    {F : Fct C (SetCat@{u p _ _ _ _ _})}
    (β : DayValuesF F F ⇒ (F ∘F tensorF MC))
  : (tensorF SM ∘F (F ×F F)) ⇒ (F ∘F tensorF MC)
  :=
  {|nt q := β q
  |}.
Next Obligation.
  destruct X as [X1 X2], Y as [Y1 Y2], f as [f g].
  change (β (Y1,Y2) ∘
    @tensor_map SetCat SM _ _ _ _ (fmap F f) (fmap F g) ≈
    fmap F (fmap (tensorF MC) (X := (X1,X2)) (Y := (Y1,Y2)) (f,g)) ∘
      β (X1,X2)).
  intros [x y]. exact (nt_naturality β (f,g) (x,y)).
Defined.

(** A unit value defines the constant map from the selected terminal setoid. *)

(** 单位值定义从选定终广集出发的常映射。 *)

Program Definition DayLaxUnit
    {F : Fct C (SetCat@{u p _ _ _ _ _})} (e : F (TensorUnit MC))
  : (@Hom SetCat) (TensorUnit SM) (F (TensorUnit MC))
  :=
  {|func _ := e
  |}.
Next Obligation. intros x y H. reflexivity. Defined.

End NativeTensorator.

(** ** Unit Diagrams through the Original Unit Isomorphisms

    Fix a monoidal base, explicit convolution choices, a functor and two
    candidate natural operations. Precomposing with each unitor's inverse
    tests the entire unit diagram on ordinary values, rather than all coend
    representatives. No monoid or lax laws are assumed by the computation. *)

(** ** 通过原单位同构比较单位图

    固定幺半基底、显式卷积选择、函子及两个候选自然操作。与各单位子之逆
    预合成，即可在通常值上检验整个单位图，无需遍历 coend 代表。
    计算本身不假定幺半群或 lax 定律。 *)

Section UnitDiagrams.
Universes u p.
Context {C : Cat} (MC : MonoidalCat C).
Let T
  : Fct (C ×C C) C
  := tensorF MC.
Let I
  : @Ob C
  := TensorUnit MC.
Let L
  : π2F T I ≅N IdF
  := @monoidal_left_unitor C MC.
Let R
  : π1F T I ≅N IdF
  := @monoidal_right_unitor C MC.
Context (HD : ∀ F G : Fct C (SetCat@{u p _ _ _ _ _}), HasDay C T F G).
Local Existing Instance HD.
Context (F : Fct C (SetCat@{u p _ _ _ _ _}))
    (η : DayUnitF I ⇒ F) (μ : DayF T F F ⇒ F).

(** The left inverse unitor inserts just the identity representable value. *)

(** 左逆单位子仅插入可表恒等值。 *)

Lemma day_unit_l_compute (X : @Ob C) (x : F X)
  : μ X (DayMapN T (HD := HD (DayUnitF I) F) (HD' := HD F F)
      η (idN (F := F)) X (day_left_unitor_inv T L F X x)) ≈S
    fmap F (L.1 X)
      (DayRestrictN T μ (I,X) (day_unit_value I F η,x)).
Proof.
  transitivity (μ X (day_inject T F F (I,X) (L.1 X)
    (η I {|lower := id|},x))).
  - apply (@func_proper _ _ (μ X)).
    exact (day_map_inject T η (idN (F := F))
      (I,X) (L.1 X) {|lower := id|} x).
  - exact (day_transform_inject T μ (I,X) (L.1 X)
      (day_unit_value I F η,x)).
Defined.

(** The right computation uses the other original inverse unitor. *)

(** 右侧计算使用另一个原逆单位子。 *)

Lemma day_unit_r_compute (X : @Ob C) (x : F X)
  : μ X (DayMapN T (HD := HD F (DayUnitF I)) (HD' := HD F F)
      (idN (F := F)) η X (day_right_unitor_inv T R F X x)) ≈S
    fmap F (R.1 X)
      (DayRestrictN T μ (X,I) (x,day_unit_value I F η)).
Proof.
  transitivity (μ X (day_inject T F F (X,I) (R.1 X)
    (x,η I {|lower := id|}))).
  - apply (@func_proper _ _ (μ X)).
    exact (day_map_inject T (idN (F := F)) η
      (X,I) (R.1 X) x {|lower := id|}).
  - exact (day_transform_inject T μ (X,I) (R.1 X)
      (x,day_unit_value I F η)).
Defined.

(** The full left Day unit diagram is equivalent to its value equation. *)

(** 完整左 Day 单位图等价于其值方程。 *)

Theorem day_unit_l_law
  : ((μ ∘Nv DayMapN T (HD := HD (DayUnitF I) F) (HD' := HD F F)
        η (idN (F := F))) ≈N DayLeftUnitorN T L F) ↔
    (∀ X (x : F X), fmap F (L.1 X)
      (DayRestrictN T μ (I,X) (day_unit_value I F η,x)) ≈S x).
Proof.
  split; intros H.
  - intros X x.
    transitivity (μ X (DayMapN T η (idN (F := F)) X
      (day_left_unitor_inv T L F X x))).
    + symmetry. exact (day_unit_l_compute X x).
    + transitivity (DayLeftUnitorN T L F X
        (day_left_unitor_inv T L F X x)).
      * exact (H X (day_left_unitor_inv T L F X x)).
      * exact (day_left_unitor_inv_r T L F X x).
  - intros X. apply (iso_cancel_r
      (iso_symm (DayLeftUnitorN T L F X; (DayLeftUnitor T L F).2 X))).
    intros x.
    transitivity (fmap F (L.1 X)
      (DayRestrictN T μ (I,X) (day_unit_value I F η,x))).
    + exact (day_unit_l_compute X x).
    + transitivity x; [exact (H X x) |].
      symmetry. exact (day_left_unitor_inv_r T L F X x).
Defined.

(** The full right unit diagram is equivalent to its other value equation. *)

(** 完整右单位图等价于另一值方程。 *)

Theorem day_unit_r_law
  : ((μ ∘Nv DayMapN T (HD := HD F (DayUnitF I)) (HD' := HD F F)
        (idN (F := F)) η) ≈N DayRightUnitorN T R F) ↔
    (∀ X (x : F X), fmap F (R.1 X)
      (DayRestrictN T μ (X,I) (x,day_unit_value I F η)) ≈S x).
Proof.
  split; intros H.
  - intros X x.
    transitivity (μ X (DayMapN T (idN (F := F)) η X
      (day_right_unitor_inv T R F X x))).
    + symmetry. exact (day_unit_r_compute X x).
    + transitivity (DayRightUnitorN T R F X
        (day_right_unitor_inv T R F X x)).
      * exact (H X (day_right_unitor_inv T R F X x)).
      * exact (day_right_unitor_inv_r T R F X x).
  - intros X. apply (iso_cancel_r
      (iso_symm (DayRightUnitorN T R F X; (DayRightUnitor T R F).2 X))).
    intros x.
    transitivity (fmap F (R.1 X)
      (DayRestrictN T μ (X,I) (x,day_unit_value I F η))).
    + exact (day_unit_r_compute X x).
    + transitivity x; [exact (H X x) |].
      symmetry. exact (day_right_unitor_inv_r T R F X x).
Defined.

End UnitDiagrams.

(** ** Multiplication Diagrams on Ternary Generators

    Fix the same monoidal base and explicit convolution family, but only
    a candidate multiplication. Restriction gives its binary operation.
    The inverse associator moves the Day diagram to right generators;
    naturality leaves the ordinary lax associativity equation. *)

(** ** 三元生成元上的乘法图

    固定同一幺半基底及显式卷积族，只给定候选乘法。限制给出其二元操作。
    逆结合子将 Day 图移到右生成元，自然性留下通常 lax 结合方程。 *)

Section MultiplicationDiagrams.
Universes u p.
Context {C : Cat} (MC : MonoidalCat C).
Let T
  : Fct (C ×C C) C
  := tensorF MC.
Let A
  : TensorLeftF T ≅N TensorRightF T
  := @monoidal_associator C MC.
Context (HD : ∀ F G : Fct C (SetCat@{u p _ _ _ _ _}), HasDay C T F G).
Local Existing Instance HD.
Context (F : Fct C (SetCat@{u p _ _ _ _ _})) (μ : DayF T F F ⇒ F).
Let β
  : DayValuesF F F ⇒ (F ∘F T)
  := DayRestrictN T μ.
Let ML
  : DayF T (DayF T F F) F ⇒ F
  := μ ∘Nv DayMapN T (HD := HD (DayF T F F) F) (HD' := HD F F)
      μ (idN (F := F)).
Let MR
  : DayF T F (DayF T F F) ⇒ F
  := μ ∘Nv DayMapN T (HD := HD F (DayF T F F)) (HD' := HD F F)
      (idN (F := F)) μ.

(** Restriction exposes multiplication on an identity generator. *)

(** 限制暴露恒等生成元上的乘法。 *)

Lemma day_mul_gen (q : @Ob (C ×C C)) (xy : DayValuesF F F q)
  : μ (T q) (DayGenN T F F q xy) ≈S β q xy.
Proof. reflexivity. Defined.

(** Multiplying the left nested generator first combines its first two values. *)

(** 对左嵌套生成元相乘，先组合前两个值。 *)

Lemma day_mul_l_compute (a b c : @Ob C) (x : F a) (y : F b) (z : F c)
  : ML (T (T (a,b),c))
      (DayTripleLeftGenN T F F F ((a,b),c) ((x,y),z)) ≈S
    β (T (a,b),c) (β (a,b) (x,y),z).
Proof.
  transitivity (μ (T (T (a,b),c))
    (day_inject T F F (T (a,b),c) id
      (μ (T (a,b)) (DayGenN T F F (a,b) (x,y)),z))).
  - apply (@func_proper _ _ (μ (T (T (a,b),c)))).
    exact (day_map_inject T μ (idN (F := F)) (T (a,b),c) id
      (DayGenN T F F (a,b) (x,y)) z).
  - transitivity (β (T (a,b),c)
      (μ (T (a,b)) (DayGenN T F F (a,b) (x,y)),z)).
    + exact (day_mul_gen (T (a,b),c)
        (μ (T (a,b)) (DayGenN T F F (a,b) (x,y)),z)).
    + apply (@func_proper _ _ (β (T (a,b),c))).
      split; [exact (day_mul_gen (a,b) (x,y)) | reflexivity].
Defined.

(** The right nested computation first combines the last two values. *)

(** 右嵌套计算先组合后两个值。 *)

Lemma day_mul_r_compute (a b c : @Ob C) (x : F a) (y : F b) (z : F c)
  : MR (T (a,T (b,c)))
      (DayTripleRightGenN T F F F ((a,b),c) ((x,y),z)) ≈S
    β (a,T (b,c)) (x,β (b,c) (y,z)).
Proof.
  transitivity (μ (T (a,T (b,c)))
    (day_inject T F F (a,T (b,c)) id
      (x,μ (T (b,c)) (DayGenN T F F (b,c) (y,z))))).
  - apply (@func_proper _ _ (μ (T (a,T (b,c))))).
    exact (day_map_inject T (idN (F := F)) μ (a,T (b,c)) id
      x (DayGenN T F F (b,c) (y,z))).
  - transitivity (β (a,T (b,c))
      (x,μ (T (b,c)) (DayGenN T F F (b,c) (y,z)))).
    + exact (day_mul_gen (a,T (b,c))
        (x,μ (T (b,c)) (DayGenN T F F (b,c) (y,z)))).
    + apply (@func_proper _ _ (β (a,T (b,c)))).
      split; [reflexivity | exact (day_mul_gen (b,c) (y,z))].
Defined.

(** Inverse Day associativity exposes the forward base associator. *)

(** Day 逆结合性暴露基正向结合子。 *)

Lemma day_mul_assoc_inv_compute (a b c : @Ob C)
    (x : F a) (y : F b) (z : F c)
  : ML (T (a,T (b,c)))
      (DayAssociatorInvN T A F F F (T (a,T (b,c)))
        (DayTripleRightGenN T F F F ((a,b),c) ((x,y),z))) ≈S
    fmap F (A.1 ((a,b),c)) (β (T (a,b),c) (β (a,b) (x,y),z)).
Proof.
  transitivity (ML (T (a,T (b,c)))
    (fmap (DayF T (DayF T F F) F) (A.1 ((a,b),c))
      (DayTripleLeftGenN T F F F ((a,b),c) ((x,y),z)))).
  - exact (@func_proper _ _ (ML (T (a,T (b,c)))) _ _
      (day_associator_inv_gen T A F F F ((a,b),c) ((x,y),z))).
  - transitivity (fmap F (A.1 ((a,b),c))
      (ML (T (T (a,b),c))
        (DayTripleLeftGenN T F F F ((a,b),c) ((x,y),z)))).
    + exact (nt_naturality ML (A.1 ((a,b),c))
        (DayTripleLeftGenN T F F F ((a,b),c) ((x,y),z))).
    + exact (@func_proper _ _ (fmap F (A.1 ((a,b),c))) _ _
        (day_mul_l_compute a b c x y z)).
Defined.

(** Associativity of the full Day multiplication is equivalent to the
    ordinary lax associativity equation on the restricted binary operation. *)

(** 完整 Day 乘法的结合律等价于受限二元操作上的通常 lax 结合方程。 *)

Theorem day_mul_assoc_law
  : (ML ≈N (MR ∘Nv DayAssociatorN T A F F F)) ↔
    (∀ a b c (x : F a) (y : F b) (z : F c),
      fmap F (A.1 ((a,b),c)) (β (T (a,b),c) (β (a,b) (x,y),z)) ≈S
      β (a,T (b,c)) (x,β (b,c) (y,z))).
Proof.
  split; intros H.
  - intros a b c x y z.
    pose (v := DayTripleRightGenN T F F F ((a,b),c) ((x,y),z)).
    transitivity (ML (T (a,T (b,c)))
      (DayAssociatorInvN T A F F F (T (a,T (b,c))) v)).
    + symmetry. exact (day_mul_assoc_inv_compute a b c x y z).
    + transitivity (MR (T (a,T (b,c)))
        (DayAssociatorN T A F F F (T (a,T (b,c)))
          (DayAssociatorInvN T A F F F (T (a,T (b,c))) v))).
      * exact (H (T (a,T (b,c)))
          (DayAssociatorInvN T A F F F (T (a,T (b,c))) v)).
      * transitivity (MR (T (a,T (b,c))) v).
        -- exact (@func_proper _ _ (MR (T (a,T (b,c)))) _ _
             (day_associator_inv_r_at T A F F F (T (a,T (b,c))) v)).
        -- exact (day_mul_r_compute a b c x y z).
  - assert (Hinv : (ML ∘Nv DayAssociatorInvN T A F F F) ≈N MR).
    { apply (day_triple_right_nat_ext T F F F).
      intros [[a b] c] [[x y] z].
      transitivity (fmap F (A.1 ((a,b),c))
        (β (T (a,b),c) (β (a,b) (x,y),z))).
      - exact (day_mul_assoc_inv_compute a b c x y z).
      - transitivity (β (a,T (b,c)) (x,β (b,c) (y,z))).
        + exact (H a b c x y z).
        + symmetry. exact (day_mul_r_compute a b c x y z). }
    intros X v.
    transitivity (ML X (DayAssociatorInvN T A F F F X
      (DayAssociatorN T A F F F X v))).
    + exact (@func_proper _ _ (ML X) _ _
        (symmetry (day_associator_inv_l_at T A F F F X v))).
    + exact (Hinv X (DayAssociatorN T A F F F X v)).
Defined.

End MultiplicationDiagrams.

(** ** Pointwise Lax Coherence for the Same Operations

    Fix a monoidal source and a setoid-valued functor. A unit value and a
    natural binary operation satisfy the native lax diagrams exactly when
    their value equations hold. The existing lax interface remains the
    complete structure; this predicate merely compares fixed data. *)

(** ** 相同运算的逐点 Lax 相干性

    固定幺半来源及广集值函子。单位值和自然二元操作满足原生 lax 图，当且
    仅当其值方程成立。完整结构仍使用已有 lax 接口，此谓词仅比较固定数据。 *)

Section PointwiseLax.
Universes u p.
Context {C : Cat} (MC : MonoidalCat C).
Let T
  : Fct (C ×C C) C
  := tensorF MC.
Let I
  : @Ob C
  := TensorUnit MC.
Let SM
  : MonoidalCat (SetCat@{u p _ _ _ _ _})
  := @CartesianMonoidal SetCat SetCat_HasTerminal SetCat_HasProduct.

(** Fixed-data coherence keeps the chosen base unitors and associator. *)

(** 固定数据的相干性保留选定基单位子和结合子。 *)

Definition is_day_lax (F : Fct C (SetCat@{u p _ _ _ _ _}))
    (e : F I) (β : DayValuesF F F ⇒ (F ∘F T))
  : Type
  := (∀ X (x : F X),
        fmap F (@tensor_unit_l C MC X) (β (I,X) (e,x)) ≈S x) ∧
     (∀ X (x : F X),
        fmap F (@tensor_unit_r C MC X) (β (X,I) (x,e)) ≈S x) ∧
     (∀ a b c (x : F a) (y : F b) (z : F c),
        fmap F (@tensor_assoc C MC a b c)
          (β (T (a,b),c) (β (a,b) (x,y),z)) ≈S
        β (a,T (b,c)) (x,β (b,c) (y,z))).

(** A native lax functor satisfies the pointwise equations by evaluation. *)

(** 对原生 lax 函子求值即得逐点方程。 *)

Lemma lax_day_coherence (L : LaxMonoidalFct MC SM)
  : is_day_lax L (lax_unit L tt) (LaxDayTensorN MC L).
Proof.
  split; [| split].
  - intros X x. exact (lax_unit_l L X (tt,x)).
  - intros X x. exact (lax_unit_r L X (x,tt)).
  - intros a b c x y z. exact (lax_assoc L a b c ((x,y),z)).
Defined.

(** Recover the existing complete lax interface from those same operations. *)

(** 从相同运算恢复已有的完整 lax 接口。 *)

Program Definition DayOperationLax
    (F : Fct C (SetCat@{u p _ _ _ _ _}))
    (e : F I) (β : DayValuesF F F ⇒ (F ∘F T))
    (H : is_day_lax F e β)
  : LaxMonoidalFct MC SM
  :=
  {|LaxMonoidalF := F
  ; lax_unit := DayLaxUnit MC e
  ; lax_tensorN := DayLaxTensorN MC β
  |}.
Next Obligation.
  intros [t x]. destruct t. exact (fst H X x).
Defined.
Next Obligation.
  intros [x t]. destruct t. exact (fst (snd H) X x).
Defined.
Next Obligation.
  intros [[x y] z]. exact (snd (snd H) X Y Z x y z).
Defined.

(** Equivalent unit values and binary operations satisfy the same coherence.
    Transport only their equations, never their proof records. *)

(** 等价单位值与二元操作满足相同相干性；只运输其方程，不比较证明记录。 *)

Lemma day_lax_transport {F : Fct C (SetCat@{u p _ _ _ _ _})}
    (e e' : F I) (β β' : DayValuesF F F ⇒ (F ∘F T))
    (He : e ≈S e') (Hβ : β ≈N β') (H : is_day_lax F e β)
  : is_day_lax F e' β'.
Proof.
  destruct H as [Hl [Hr Ha]]. split; [| split].
  - intros X x. transitivity (fmap F (@tensor_unit_l C MC X)
      (β (I,X) (e,x))); [| exact (Hl X x)].
    apply (@func_proper _ _ (fmap F (@tensor_unit_l C MC X))).
    transitivity (β' (I,X) (e,x)).
    + apply (@func_proper _ _ (β' (I,X))).
      split; [symmetry; exact He | reflexivity].
    + symmetry. exact (Hβ (I,X) (e,x)).
  - intros X x. transitivity (fmap F (@tensor_unit_r C MC X)
      (β (X,I) (x,e))); [| exact (Hr X x)].
    apply (@func_proper _ _ (fmap F (@tensor_unit_r C MC X))).
    transitivity (β' (X,I) (x,e)).
    + apply (@func_proper _ _ (β' (X,I))).
      split; [reflexivity | symmetry; exact He].
    + symmetry. exact (Hβ (X,I) (x,e)).
  - intros a b c x y z.
    assert (K : β' (T (a,b),c) (β' (a,b) (x,y),z) ≈S
      β (T (a,b),c) (β (a,b) (x,y),z)).
    { transitivity (β' (T (a,b),c) (β (a,b) (x,y),z)).
      - apply (@func_proper _ _ (β' (T (a,b),c))).
        split; [symmetry; exact (Hβ (a,b) (x,y)) | reflexivity].
      - symmetry. exact (Hβ (T (a,b),c) (β (a,b) (x,y),z)). }
    transitivity (fmap F (@tensor_assoc C MC a b c)
      (β (T (a,b),c) (β (a,b) (x,y),z))).
    + exact (@func_proper _ _ (fmap F (@tensor_assoc C MC a b c)) _ _ K).
    + transitivity (β (a,T (b,c)) (x,β (b,c) (y,z)));
        [exact (Ha a b c x y z) |].
      transitivity (β' (a,T (b,c)) (x,β (b,c) (y,z))).
      * exact (Hβ (a,T (b,c)) (x,β (b,c) (y,z))).
      * apply (@func_proper _ _ (β' (a,T (b,c)))).
        split; [reflexivity | exact (Hβ (b,c) (y,z))].
Defined.

End PointwiseLax.

(** ** Fixed-Data Monoid Characterization

    Fix a monoidal base and a uniform family of selected Day convolutions.
    Keep those same choices throughout both presentations; the derived
    tensor map is compared by natural equality, not by record equality. *)

(** ** 固定数据上的幺半群刻画

    固定幺半基及统一选定的 Day 卷积族。两个呈现始终保留相同选择；导出张量
    映射按自然相等比较，不要求记录相等。 *)

Section MonoidCharacterization.
Universes u p.
Context {C : Cat} (MC : MonoidalCat C)
    (HD : ∀ F G : Fct C (SetCat@{u p _ _ _ _ _}),
      HasDay C (tensorF MC) F G).
Local Existing Instance HD.
Let DM
  : MonoidalCat (FctCat C (SetCat@{u p _ _ _ _ _}))
  := MonoidalDay MC HD.

(** Compare the inherited Day tensor action with the universal action. *)

(** 比较继承的 Day 张量作用与泛作用。 *)

Local Lemma day_object_tensor_map
    {F F' G G' : Fct C (SetCat@{u p _ _ _ _ _})}
    (α : F ⇒ F') (β : G ⇒ G')
  : @tensor_map _ DM F F' G G' α β ≈N
      @DayMapN C (tensorF MC) F F' G G' (HD F G) (HD F' G') α β.
Proof.
  exact (day_monoidal_map (tensorF MC) (TensorUnit MC)
    (@monoidal_associator C MC)
    (@monoidal_left_unitor C MC) (@monoidal_right_unitor C MC)
    (@monoidal_pentagon C MC) (@monoidal_triangle C MC) HD α β).
Defined.

(** The three monoid diagrams are precisely the lax value equations.
    All coend existence and size conditions remain in [HD]. *)

(** 三个幺半群图恰好对应 lax 值方程；全部 coend 存在及大小条件仍在 [HD] 中。 *)

Theorem day_monoid_laws (F : Fct C (SetCat@{u p _ _ _ _ _}))
    (η : DayUnitF (TensorUnit MC) ⇒ F)
    (μ : DayF (tensorF MC) F F ⇒ F)
  : is_monoid_object DM F η μ ↔
      is_day_lax MC F (day_unit_value (TensorUnit MC) F η)
        (DayRestrictN (tensorF MC) μ).
Proof.
  unfold is_monoid_object, is_day_lax.
  split; intros [Hl [Hr Ha]]; (split; [| split]).
  - apply (fst (day_unit_l_law MC HD F η μ)).
    rewrite <- (day_object_tensor_map η (idN (F := F))). exact Hl.
  - apply (fst (day_unit_r_law MC HD F η μ)).
    rewrite <- (day_object_tensor_map (idN (F := F)) η). exact Hr.
  - apply (fst (day_mul_assoc_law MC HD F μ)).
    rewrite <- (day_object_tensor_map μ (idN (F := F))),
      <- (day_object_tensor_map (idN (F := F)) μ). exact Ha.
  - pose proof (snd (day_unit_l_law MC HD F η μ) Hl) as K.
    rewrite <- (day_object_tensor_map η (idN (F := F))) in K. exact K.
  - pose proof (snd (day_unit_r_law MC HD F η μ) Hr) as K.
    rewrite <- (day_object_tensor_map (idN (F := F)) η) in K. exact K.
  - pose proof (snd (day_mul_assoc_law MC HD F μ) Ha) as K.
    rewrite <- (day_object_tensor_map μ (idN (F := F))),
      <- (day_object_tensor_map (idN (F := F)) μ) in K. exact K.
Defined.

End MonoidCharacterization.

(** ** Constructive Structure Conversions

    Fix the same monoidal base and explicit convolution choices. The native
    cartesian setoid target is unchanged. Both conversions retain the
    underlying functor and compare their operations in designated equality. *)

(** ** 构造性的结构转换

    固定相同幺半基及显式卷积选择，保持原生笛卡尔广集目标。两个转换均保留
    底层函子，并按指定相等比较其运算。 *)

Section StructureConversions.
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

(** Extending a lax unit and tensorator satisfies the Day monoid diagrams. *)

(** 延拓 lax 单位和张量子即满足 Day 幺半群图。 *)

Lemma lax_day_monoid_laws (L : LaxMonoidalFct MC SM)
  : is_monoid_object DM L
      (DayUnitExtendN (TensorUnit MC) L (lax_unit L tt))
      (DayExtendN (tensorF MC) (LaxDayTensorN MC L)).
Proof.
  apply (snd (day_monoid_laws MC HD L _ _)).
  refine (day_lax_transport MC (lax_unit L tt) _
    (LaxDayTensorN MC L) _ _ _ (lax_day_coherence MC L)).
  - symmetry. exact (day_unit_value_extend (TensorUnit MC) L (lax_unit L tt)).
  - symmetry. exact (day_restrict_extend (tensorF MC) (LaxDayTensorN MC L)).
Defined.

(** A lax monoidal functor is a monoid for the selected Day structure. *)

(** Lax monoidal 函子构成选定 Day 结构下的幺半群。 *)

Program Definition LaxDayMonoid (L : LaxMonoidalFct MC SM)
  : MonoidObj DM
  :=
  {|MonoidCarrier := L
  ; monoid_object_unit := DayUnitExtendN (TensorUnit MC) L (lax_unit L tt)
  ; monoid_object_mul := DayExtendN (tensorF MC) (LaxDayTensorN MC L)
  |}.
Next Obligation. exact (fst (lax_day_monoid_laws L)). Defined.
Next Obligation. exact (fst (snd (lax_day_monoid_laws L))). Defined.
Next Obligation. exact (snd (snd (lax_day_monoid_laws L))). Defined.

(** Restrict a Day monoid by Yoneda evaluation and binary generation. *)

(** 通过 Yoneda 求值与二元生成，限制 Day 幺半群。 *)

Definition DayMonoidLax (M : MonoidObj DM)
  : LaxMonoidalFct MC SM
  := DayOperationLax MC (MonoidCarrier M)
      (day_unit_value (TensorUnit MC) (MonoidCarrier M) (monoid_object_unit M))
      (DayRestrictN (tensorF MC) (monoid_object_mul M))
      (fst (day_monoid_laws MC HD (MonoidCarrier M)
        (monoid_object_unit M) (monoid_object_mul M)) (monoid_object_laws M)).

(** The Day unit survives restriction followed by extension. *)

(** Day 单位在先限制后延拓的往返中保持不变。 *)

Lemma day_monoid_unit_roundtrip (M : MonoidObj DM)
  : monoid_object_unit (LaxDayMonoid (DayMonoidLax M)) ≈N
      monoid_object_unit M.
Proof.
  exact (day_unit_extend_value (TensorUnit MC) (MonoidCarrier M)
    (monoid_object_unit M)).
Defined.

(** The Day multiplication survives the same round trip. *)

(** Day 乘法在相同往返中保持不变。 *)

Lemma day_monoid_mul_roundtrip (M : MonoidObj DM)
  : monoid_object_mul (LaxDayMonoid (DayMonoidLax M)) ≈N
      monoid_object_mul M.
Proof.
  transitivity (DayExtendN (tensorF MC)
    (DayRestrictN (tensorF MC) (monoid_object_mul M))).
  - apply day_extend_proper. intros [X Y] [x y]. reflexivity.
  - exact (day_extend_restrict (tensorF MC) (monoid_object_mul M)).
Defined.

(** The native lax unit survives extension followed by restriction. *)

(** 原生 lax 单位在先延拓后限制的往返中保持不变。 *)

Lemma day_lax_unit_roundtrip (L : LaxMonoidalFct MC SM)
  : lax_unit (DayMonoidLax (LaxDayMonoid L)) ≈ lax_unit L.
Proof.
  intros []. exact (day_unit_value_extend (TensorUnit MC) L (lax_unit L tt)).
Defined.

(** The native tensorator survives that round trip in natural equality. *)

(** 原生张量子在该往返中按自然相等保持不变。 *)

Lemma day_lax_tensor_roundtrip (L : LaxMonoidalFct MC SM)
  : lax_tensorN (DayMonoidLax (LaxDayMonoid L)) ≈N lax_tensorN L.
Proof.
  intros q xy.
  exact (day_restrict_extend (tensorF MC) (LaxDayTensorN MC L) q xy).
Defined.

End StructureConversions.
