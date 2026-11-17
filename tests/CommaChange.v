From Cats Require Import
  Cat.Comma.Change
  Cat.Diagram.Core
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Bool.Action
  Instance.Bool.Group.
From CatsTests Require Import
  Gluing.

(** * Change of Comma Diagrams: Interfaces and Computation

    Strict level profiles separate all nine categories used by consecutive
    changes. Concrete constant diagrams over a non-thin groupoid test
    noninvertible boundaries, side loops and observable setoid witnesses. *)

(** * 逗号图式变化：接口及计算

    严格层级配置分离连续变化所用的全部九个范畴。非薄群胚上的具体常图式
    检查不可逆边界、侧边环路及可观察的广集见证。 *)

(** ** Independent Levels

    Fix nine separate category boundaries and two compatible diagram changes.
    Check the full functors and their identity/composition comparisons. *)

(** ** 独立层级

    固定九个分离的范畴边界及两次相容图式变化，检查完整函子及恒等／复合比较。 *)

Section IndependentChange.
Universes
  o0 h0 e0 l0 o1 h1 e1 l1 o2 h2 e2 l2
  o3 h3 e3 l3 o4 h4 e4 l4 o5 h5 e5 l5
  o6 h6 e6 l6 o7 h7 e7 l7 o8 h8 e8 l8.
Constraint h0 < e0, e0 < o0, o0 < l0.
Constraint e1 < h1, h1 < o1, o1 < l1.
Constraint h2 < e2, e2 < o2, o2 < l2.
Constraint e3 < h3, h3 < o3, o3 < l3.
Constraint h4 < e4, e4 < o4, o4 < l4.
Constraint e5 < h5, h5 < o5, o5 < l5.
Constraint h6 < e6, e6 < o6, o6 < l6.
Constraint e7 < h7, h7 < o7, o7 < l7.
Constraint h8 < e8, e8 < o8, o8 < l8.
Constraint l0 < o1, l1 < o2, l2 < o3, l3 < o4, l4 < o5, l5 < o6, l6 < o7, l7 < o8.
Context {A : Cat@{o0 h0 e0 l0 l0}}.
Context {B : Cat@{o1 h1 e1 l1 l1}}.
Context {C : Cat@{o2 h2 e2 l2 l2}}.
Context {A' : Cat@{o3 h3 e3 l3 l3}}.
Context {B' : Cat@{o4 h4 e4 l4 l4}}.
Context {C' : Cat@{o5 h5 e5 l5 l5}}.
Context {A'' : Cat@{o6 h6 e6 l6 l6}}.
Context {B'' : Cat@{o7 h7 e7 l7 l7}}.
Context {C'' : Cat@{o8 h8 e8 l8 l8}}.
Context {F : Fct A C} {G : Fct B C}.
Context {F' : Fct A' C'} {G' : Fct B' C'}.
Context {F'' : Fct A'' C''} {G'' : Fct B'' C''}.
Context (L : Fct A A') (R : Fct B B') (K : Fct C C').
Context (L' : Fct A' A'') (R' : Fct B' B'') (K' : Fct C' C'').
Context (α : (F' ∘F L) ⇒ (K ∘F F))
    (β : (K ∘F G) ⇒ (G' ∘F R)).
Context (α' : (F'' ∘F L') ⇒ (K' ∘F F'))
    (β' : (K' ∘F G') ⇒ (G'' ∘F R')).

(** The diagram change retains native endpoint hom equalities. *)

(** 图式变化保留原生端点 Hom 相等。 *)

Definition independent_comma_change
  : Fct (F ↓C G) (F' ↓C G')
  := CommaChangeF L R K α β.

(** The left projection comparison accepts these strict boundaries. *)

(** 左投影比较接受这些严格边界。 *)

Definition independent_comma_projection
  : (CommaLeftF F' G' ∘F CommaChangeF L R K α β)
      ≅N (L ∘F CommaLeftF F G)
  := comma_change_left_iso L R K α β.

(** Identity changes do not identify transformation proof fields. *)

(** 恒等变化不等同自然变换证明字段。 *)

Definition independent_comma_identity
  : CommaChangeF IdF IdF IdF (CommaChangeIdLeftN F) (CommaChangeIdRightN G)
      ≅N IdF
  := comma_change_id_iso F G.

(** Composite change uses all nine category levels at their strict orders. *)

(** 复合变化按严格次序使用全部九个范畴层级。 *)

Definition independent_comma_composite
  : (CommaChangeF L' R' K' α' β' ∘F CommaChangeF L R K α β) ≅N
      CommaChangeF (L' ∘F L) (R' ∘F R) (K' ∘F K)
        (CommaChangeCompLeftN L K L' K' α α')
        (CommaChangeCompRightN R K R' K' β β')
  := comma_change_comp_iso L R K L' R' K' α β α' β'.

End IndependentChange.

(** ** Reversed Independent Levels

    Fix nine separate category boundaries and two compatible diagram changes.
    Check the full functors and their identity/composition comparisons. *)

(** ** 反向独立层级

    固定九个分离的范畴边界及两次相容图式变化，检查完整函子及恒等／复合比较。 *)

Section ReversedChange.
Universes
  o0 h0 e0 l0 o1 h1 e1 l1 o2 h2 e2 l2
  o3 h3 e3 l3 o4 h4 e4 l4 o5 h5 e5 l5
  o6 h6 e6 l6 o7 h7 e7 l7 o8 h8 e8 l8.
Constraint e0 < h0, h0 < o0, o0 < l0.
Constraint h1 < e1, e1 < o1, o1 < l1.
Constraint e2 < h2, h2 < o2, o2 < l2.
Constraint h3 < e3, e3 < o3, o3 < l3.
Constraint e4 < h4, h4 < o4, o4 < l4.
Constraint h5 < e5, e5 < o5, o5 < l5.
Constraint e6 < h6, h6 < o6, o6 < l6.
Constraint h7 < e7, e7 < o7, o7 < l7.
Constraint e8 < h8, h8 < o8, o8 < l8.
Constraint l8 < o7, l7 < o6, l6 < o5, l5 < o4, l4 < o3, l3 < o2, l2 < o1, l1 < o0.
Context {A : Cat@{o0 h0 e0 l0 l0}}.
Context {B : Cat@{o1 h1 e1 l1 l1}}.
Context {C : Cat@{o2 h2 e2 l2 l2}}.
Context {A' : Cat@{o3 h3 e3 l3 l3}}.
Context {B' : Cat@{o4 h4 e4 l4 l4}}.
Context {C' : Cat@{o5 h5 e5 l5 l5}}.
Context {A'' : Cat@{o6 h6 e6 l6 l6}}.
Context {B'' : Cat@{o7 h7 e7 l7 l7}}.
Context {C'' : Cat@{o8 h8 e8 l8 l8}}.
Context {F : Fct A C} {G : Fct B C}.
Context {F' : Fct A' C'} {G' : Fct B' C'}.
Context {F'' : Fct A'' C''} {G'' : Fct B'' C''}.
Context (L : Fct A A') (R : Fct B B') (K : Fct C C').
Context (L' : Fct A' A'') (R' : Fct B' B'') (K' : Fct C' C'').
Context (α : (F' ∘F L) ⇒ (K ∘F F))
    (β : (K ∘F G) ⇒ (G' ∘F R)).
Context (α' : (F'' ∘F L') ⇒ (K' ∘F F'))
    (β' : (K' ∘F G') ⇒ (G'' ∘F R')).

(** The diagram change retains native endpoint hom equalities. *)

(** 图式变化保留原生端点 Hom 相等。 *)

Definition reversed_comma_change
  : Fct (F ↓C G) (F' ↓C G')
  := CommaChangeF L R K α β.

(** The left projection comparison accepts these strict boundaries. *)

(** 左投影比较接受这些严格边界。 *)

Definition reversed_comma_projection
  : (CommaLeftF F' G' ∘F CommaChangeF L R K α β)
      ≅N (L ∘F CommaLeftF F G)
  := comma_change_left_iso L R K α β.

(** Identity changes do not identify transformation proof fields. *)

(** 恒等变化不等同自然变换证明字段。 *)

Definition reversed_comma_identity
  : CommaChangeF IdF IdF IdF (CommaChangeIdLeftN F) (CommaChangeIdRightN G)
      ≅N IdF
  := comma_change_id_iso F G.

(** Composite change uses all nine category levels at their strict orders. *)

(** 复合变化按严格次序使用全部九个范畴层级。 *)

Definition reversed_comma_composite
  : (CommaChangeF L' R' K' α' β' ∘F CommaChangeF L R K α β) ≅N
      CommaChangeF (L' ∘F L) (R' ∘F R) (K' ∘F K)
        (CommaChangeCompLeftN L K L' K' α α')
        (CommaChangeCompRightN R K R' K' β β')
  := comma_change_comp_iso L R K L' R' K' α β α' β'.

End ReversedChange.

(** ** Noninvertible Boundaries and Specified Equality

    Constant diagrams over the Boolean groupoid admit arbitrary respectful
    boundary maps. No pullback or other chosen structure is enabled. The
    tagged setoid retains a Boolean equality witness. *)

(** ** 不可逆边界与指定相等

    布尔群胚上的常图式允许任意尊重相等的边界映射。不启用拉回或其他选定
    结构；标签广集保留布尔相等见证。 *)

Section ConcreteChange.

(** A constant left boundary forgets the Boolean argument. *)

(** 常值左边界忘却布尔实参。 *)

Program Definition NoninvertLeftN
  : (@CompF BoolGpd BoolGpd SetCat
        (ConstF BoolGpd (C := SetCat) BoolS) (@IdF BoolGpd)) ⇒
      (CompF (C := BoolGpd) (@IdF SetCat)
        (ConstF BoolGpd TaggedGluingS))
  :=
  {|nt X := {|func b := (0, false)
             |}
  |}.
Next Obligation. intros b. exact (eq_refl, false). Defined.

(** The right boundary forgets all tagged data. *)

(** 右边界忘却全部标签数据。 *)

Program Definition NoninvertRightN
  : (CompF (C := BoolGpd) (@IdF SetCat)
        (ConstF BoolGpd (C := SetCat) TaggedGluingS)) ⇒
      (@CompF BoolGpd BoolGpd SetCat
        (ConstF BoolGpd UnitS) (@IdF BoolGpd))
  :=
  {|nt X := {|func x := tt
             |}
  |}.
Next Obligation. intros x y H. exact tt. Defined.
Next Obligation. intros x. exact tt. Defined.

(** This left boundary cannot be inverted, even at the sole base object. *)

(** 即使在唯一基对象处，该左边界也不可逆。 *)

Example noninvertible_left_boundary
  : ¬ is_iso (NoninvertLeftN tt).
Proof.
  intros [g [Hl Hr]].
  pose proof (Hl false) as Hf. pose proof (Hl true) as Ht.
  cbn in Hf, Ht. rewrite Hf in Ht. discriminate Ht.
Defined.

(** Keep an actual tag-changing structural arrow in the source diagram. *)

(** 在源图式中保留实际改变标签的结构箭头。 *)

Program Definition ConstantCommaOb
  : Comma (A := BoolGpd) (B := BoolGpd) (C := SetCat)
      (ConstF BoolGpd TaggedGluingS) (ConstF BoolGpd TaggedGluingS)
  :=
  {|comma_left_ob := tt
  ; comma_right_ob := tt
  ; comma_arrow := gluing_toggle
  |}.

(** Nonidentity loops on both sides still give a commuting square. *)

(** 两侧的非恒等环路仍给出交换方形。 *)

Program Definition constant_comma_loop
  : Hom ConstantCommaOb ConstantCommaOb
  :=
  {|comma_left := bool_loop
  ; comma_right := bool_loop
  |}.
Next Obligation. intros [n b]. exact (eq_refl, true). Defined.

(** Change the diagram using the two noninvertible boundaries. *)

(** 使用两个不可逆边界改变图式。 *)

Definition NoninvertCommaF
  : Fct
      (Comma (A := BoolGpd) (B := BoolGpd) (C := SetCat)
        (ConstF BoolGpd TaggedGluingS) (ConstF BoolGpd TaggedGluingS))
      (Comma (A := BoolGpd) (B := BoolGpd) (C := SetCat)
        (ConstF BoolGpd BoolS) (ConstF BoolGpd UnitS))
  := CommaChangeF (@IdF BoolGpd) (@IdF BoolGpd) (@IdF SetCat)
      NoninvertLeftN NoninvertRightN.

(** The mapped structural arrow computes from Boolean to unit. *)

(** 映射后的结构箭头从布尔到单位直接计算。 *)

Example noninvertible_change_computes
  : comma_arrow (NoninvertCommaF ConstantCommaOb) true = tt.
Proof. reflexivity. Defined.

(** Mapping a square preserves both original nonidentity loops. *)

(** 映射方形保留原来的两条非恒等环路。 *)

Example changed_side_loops_compute
  : (comma_left (fmap NoninvertCommaF constant_comma_loop),
      comma_right (fmap NoninvertCommaF constant_comma_loop)) = (true, true).
Proof. reflexivity. Defined.

(** Identity change keeps the original tag-changing structural computation. *)

(** 恒等变化保留原结构箭头改变标签的计算。 *)

Example identity_change_computes
  : comma_arrow (CommaChangeF (@IdF BoolGpd) (@IdF BoolGpd) (@IdF SetCat)
      (CommaChangeIdLeftN _) (CommaChangeIdRightN _) ConstantCommaOb)
      (3, false) = (3, true).
Proof. reflexivity. Defined.

(** Alter only the ignored tag in the left boundary. *)

(** 只改变左边界中被忽略的标签。 *)

Program Definition TaggedAlternativeN
  : (@CompF BoolGpd BoolGpd SetCat
        (ConstF BoolGpd (C := SetCat) BoolS) (@IdF BoolGpd)) ⇒
      (CompF (C := BoolGpd) (@IdF SetCat)
        (ConstF BoolGpd TaggedGluingS))
  :=
  {|nt X := {|func b := (0, true)
             |}
  |}.
Next Obligation. intros b. exact (eq_refl, true). Defined.

(** A specified equality with an observable false witness compares them. *)

(** 带可观察假见证的指定相等比较这两个边界。 *)

Definition tagged_boundary_equal
  : NoninvertLeftN ≈N TaggedAlternativeN.
Proof. intros X b. exact (eq_refl, false). Defined.

(** The equality witness remains data rather than becoming proof-irrelevant. *)

(** 相等见证仍为数据，不变成证明无关的值。 *)

Example tagged_boundary_witness_computes
  : snd (tagged_boundary_equal tt true) = false.
Proof. reflexivity. Defined.

(** Equivalent boundaries induce an actual comparison of changed functors. *)

(** 等价边界诱导变化后函子之间的实际比较。 *)

Definition tagged_change_comparison
  : NoninvertCommaF ≅N
      CommaChangeF (@IdF BoolGpd) (@IdF BoolGpd) (@IdF SetCat)
        TaggedAlternativeN NoninvertRightN
  := comma_change_equiv_iso (@IdF BoolGpd) (@IdF BoolGpd)
      (@IdF SetCat) tagged_boundary_equal
      (λ X, reflexivity (NoninvertRightN X)).

(** The comparison component keeps the groupoid's identity loops. *)

(** 比较分量保留群胚的恒等环路。 *)

Example tagged_change_comparison_computes
  : (comma_left (tagged_change_comparison.1 ConstantCommaOb),
      comma_right (tagged_change_comparison.1 ConstantCommaOb)) =
      (false, false).
Proof. reflexivity. Defined.

(** The next change maps a unit source constantly into the Boolean source. *)

(** 下一变化将单位源常值映入布尔源。 *)

Program Definition SecondLeftN
  : (@CompF BoolGpd BoolGpd SetCat
        (ConstF BoolGpd (C := SetCat) UnitS) (@IdF BoolGpd)) ⇒
      (CompF (C := BoolGpd) (@IdF SetCat)
        (ConstF BoolGpd BoolS))
  :=
  {|nt X := {|func x := false
             |}
  |}.
Next Obligation. intros x y H. reflexivity. Defined.
Next Obligation. intros x. reflexivity. Defined.

(** Its right boundary chooses true in the Boolean target. *)

(** 其右边界在布尔目标中选择真。 *)

Program Definition SecondRightN
  : (CompF (C := BoolGpd) (@IdF SetCat)
        (ConstF BoolGpd (C := SetCat) UnitS)) ⇒
      (@CompF BoolGpd BoolGpd SetCat
        (ConstF BoolGpd BoolS) (@IdF BoolGpd))
  :=
  {|nt X := {|func x := true
             |}
  |}.
Next Obligation. intros x y H. reflexivity. Defined.
Next Obligation. intros x. reflexivity. Defined.

(** The actual composite comparison retains transparent identity side maps. *)

(** 实际复合比较保留透明恒等侧边映射。 *)

Definition NoninvertCompositeIso
  : (CommaChangeF (@IdF BoolGpd) (@IdF BoolGpd) (@IdF SetCat)
      SecondLeftN SecondRightN ∘F NoninvertCommaF) ≅N
      CommaChangeF
        ((@IdF BoolGpd) ∘F IdF) ((@IdF BoolGpd) ∘F IdF)
        ((@IdF SetCat) ∘F IdF)
        (CommaChangeCompLeftN (@IdF BoolGpd) (@IdF SetCat)
          (@IdF BoolGpd) (@IdF SetCat) NoninvertLeftN SecondLeftN)
        (CommaChangeCompRightN (@IdF BoolGpd) (@IdF SetCat)
          (@IdF BoolGpd) (@IdF SetCat) NoninvertRightN SecondRightN)
  := comma_change_comp_iso (@IdF BoolGpd) (@IdF BoolGpd)
      (@IdF SetCat) (@IdF BoolGpd) (@IdF BoolGpd) (@IdF SetCat)
      NoninvertLeftN NoninvertRightN SecondLeftN SecondRightN.

(** The direct composite structural arrow computes the supplied true value. *)

(** 直接复合的结构箭头计算出给定的真值。 *)

Example composite_change_arrow_computes
  : comma_arrow (CommaChangeF
      ((@IdF BoolGpd) ∘F IdF) ((@IdF BoolGpd) ∘F IdF)
      ((@IdF SetCat) ∘F IdF)
      (CommaChangeCompLeftN (@IdF BoolGpd) (@IdF SetCat)
        (@IdF BoolGpd) (@IdF SetCat) NoninvertLeftN SecondLeftN)
      (CommaChangeCompRightN (@IdF BoolGpd) (@IdF SetCat)
        (@IdF BoolGpd) (@IdF SetCat) NoninvertRightN SecondRightN)
      ConstantCommaOb) tt = true.
Proof. reflexivity. Defined.

(** The saved inverse comparison computes without inspecting square laws. *)

(** 保存的逆比较无需检查方形定律即可计算。 *)

Example composite_change_inverse_computes
  : (comma_left ((NoninvertCompositeIso.2 ConstantCommaOb).1),
      comma_right ((NoninvertCompositeIso.2 ConstantCommaOb).1)) =
      (false, false).
Proof. reflexivity. Defined.

End ConcreteChange.

(** ** Respecting Nontrivial Square Equality

    The identity diagram change acts on the original tagged gluing test
    category. Its side maps may differ natively while their specified
    equality forgets the tags. No equality of square witnesses is used. *)

(** ** 保持非平凡方形相等

    恒等图式变化作用于原标签粘合测试范畴。侧边映射可原生不同，而指定相等
    忘却标签；不使用方形见证相等。 *)

Section TaggedSquareEquality.

(** Enable the general construction at the identity/identity diagram. *)

(** 在恒等／恒等图式处使用一般构造。 *)

Definition IdentityTaggedCommaF
  : Fct ((@IdF SetCat) ↓C IdF) ((@IdF SetCat) ↓C IdF)
  := CommaChangeF (@IdF SetCat) (@IdF SetCat) (@IdF SetCat)
      (CommaChangeIdLeftN IdF) (CommaChangeIdRightN IdF).

(** Its hom action respects the original specified tag-changing equality. *)

(** 其 Hom 作用保持原来改变标签的指定相等。 *)

Example tagged_changed_square_equal
  : @HomEq ((@IdF SetCat) ↓C IdF)
      (IdentityTaggedCommaF TaggedGluingObj)
      (IdentityTaggedCommaF TaggedGluingObj)
      (fmap IdentityTaggedCommaF tagged_gluing_toggle)
      (fmap IdentityTaggedCommaF id).
Proof. apply fct_fmap_proper. exact tagged_gluing_toggle_equal. Defined.

(** Respecting equality keeps the actual changed tag in the mapped side. *)

(** 保持相等仍在映射后的侧边保留实际改变的标签。 *)

Example tagged_changed_side_computes
  : comma_left (fmap IdentityTaggedCommaF tagged_gluing_toggle)
      (3, false) = (3, true).
Proof. reflexivity. Defined.

End TaggedSquareEquality.
