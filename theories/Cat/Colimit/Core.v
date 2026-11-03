From Cats Require Export
  Cat.Diagram.Dual.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Terminal
  Cat.Limit.Core.

(** * Colimit Interfaces from Opposite Limits *)

(** * 从反范畴极限提供余极限接口 *)

(** The colimit property is exactly the original limit property on the
    underlying opposite cone. *)

(** 余极限性质直接取底层反锥的原极限性质。 *)

Definition is_colimit {J C : Cat} {D : Functor J C} {L : @Ob C}
    (κ : D ⇒∇ L)
  := is_limit (op_cone κ).

Notation "κ '⦂' 'Colim(' D ')'" := (@is_colimit _ _ D _ κ)
  (at level 50, no associativity) : cat_scope.

(** Expose the same universal property with arrows in [C]. No second
    universal property or comparison construction is stored. *)

(** 用 [C] 中的箭头展开同一个泛性质，不另存泛性质或比较构造。 *)

Definition colimit_universal_iff {J C : Cat} {D : Functor J C}
    {L : @Ob C} (κ : D ⇒∇ L)
  : is_colimit κ ↔
      ∀ X (μ : D ⇒∇ X), ∃ h : Hom L X,
        is_unique (λ h, h ∘Cocone κ ≈N μ) h.
Proof.
  split; intros H X μ.
  - exact (H X (op_cone μ)).
  - exact (H X {|op_cone := μ|}).
Defined.

(** The opposite cocone of a limiting cone has the same mediator data. *)

(** 极限锥的反余锥保留同一份中介数据。 *)

Theorem limit_iff_op_colimit {J C : Cat} {D : Functor J C} {L : @Ob C}
    (κ : L ⇒Δ D)
  : is_limit κ ↔ is_colimit (ConeOp κ).
Proof.
  split; intros H X μ.
  - exact (H X (ConeUnop {|op_cone := μ|})).
  - exact (H X (op_cone (ConeOp μ))).
Defined.

(** A selected colimit contains only the original selected opposite limit. *)

(** 选定余极限只包含原来的选定反范畴极限。 *)

Class HasColimit (C : Cat) {J : Cat} (D : Functor J C)
  :=
  { hasOpLimit :: HasLimit (C^op) (D^opF)
  }.

(** Enable a given opposite limit through the colimit interface. *)

(** 将给定的反范畴极限通过余极限接口启用。 *)

Program Definition OpLimitColimit {J C : Cat} {D : Functor J C}
    `{HL : !HasLimit (C^op) (D^opF)}
  : HasColimit C D
  :=
  {|hasOpLimit := HL
  |}.

(** The selected colimit object is the selected opposite limit object. *)

(** 选定余极限对象就是选定反范畴极限对象。 *)

Definition Colim {J C : Cat} (D : Functor J C) `{HC : !HasColimit C D}
  : @Ob C
  := lim (D^opF).

Arguments Colim {_ _} _ {_}.
Notation "'colim' D" := (Colim D) (at level 35) : ob_scope.

(** The injections are the original opposite-limit cone legs. *)

(** 注入就是原来的反范畴极限锥腿。 *)

Definition colimit_cocone {J C : Cat} (D : Functor J C)
    `{HC : !HasColimit C D}
  : D ⇒∇ colim D
  :=
  {|op_cone := πlim[D^opF]
  |}.

Arguments colimit_cocone {_ _} _ {_}.
Notation "'ιcolim[' D ']'" := (colimit_cocone D) : hom_scope.

(** Universality is inherited without rebuilding mediator witnesses. *)

(** 泛性质直接继承，不重建中介见证。 *)

Definition colimit_universal {J C : Cat} (D : Functor J C)
    `{HC : !HasColimit C D}
  : is_colimit ιcolim[D]
  := limit_universal (D^opF).

Arguments colimit_universal {_ _} _ {_} _ _.

(** Descending is lifting into the selected opposite limit. *)

(** 下降映射就是指向选定反范畴极限的提升映射。 *)

Definition colimit_desc {J C : Cat} {D : Functor J C}
    `{HC : !HasColimit C D} {X} (κ : D ⇒∇ X)
  : Hom (colim D) X
  := lim⟨op_cone κ⟩.

Notation "'colim⟨' κ '⟩'" := (colimit_desc κ)
  (at level 35) : hom_scope.

Section ChosenColimit.
Context {J C : Cat} {D : Functor J C} `{HC : !HasColimit C D}.

(** Mediator uniqueness is inherited from the opposite limit. *)

(** 中介唯一性继承自反范畴极限。 *)

Theorem colimit_desc_unique {X} (κ : D ⇒∇ X)
  : is_unique (λ h, h ∘Cocone ιcolim[D] ≈N κ) (colim⟨κ⟩).
Proof. exact (limit_lift_unique (op_cone κ)). Defined.

(** The injection equation is the original limit beta law. *)

(** 注入方程就是原来的极限 β 律。 *)

Theorem colimit_β {X} (κ : D ⇒∇ X)
  : colim⟨κ⟩ ∘Cocone ιcolim[D] ≈N κ.
Proof. exact (limit_β (op_cone κ)). Qed.

(** The colimit eta law is the opposite limit eta law. *)

(** 余极限 η 律就是反范畴极限 η 律。 *)

Theorem colimit_η {X} (f : Hom (colim D) X)
  : colim⟨f ∘Cocone ιcolim[D]⟩ ≈ f.
Proof.
  exact (@limit_η (J^op) (C^op) (D^opF) (@hasOpLimit C J D HC) X f).
Qed.

(** Descending respects equality by the existing lift preservation law. *)

(** 下降映射的保相等性直接使用已有提升映射定律。 *)

Global Instance colimit_desc_proper {X}
  : Proper ((λ κ μ : D ⇒∇ X, κ ≈N μ) ==> @HomEq[colim D, X])
      (@colimit_desc J C D HC X).
Proof.
  intros κ μ H.
  exact (@limit_lift_proper (J^op) (C^op) (D^opF) _ X
    (op_cone κ) (op_cone μ) H).
Qed.

(** Postcomposition is the original precomposition law read in [C]. *)

(** 后合成律就是将原来的预合成律读回 [C]。 *)

Lemma colimit_desc_comp {X Y} (f : Hom X Y) (κ : D ⇒∇ X)
  : colim⟨f ∘Cocone κ⟩ ≈ f ∘ colim⟨κ⟩.
Proof. exact (limit_lift_comp (op_cone κ) f). Qed.

End ChosenColimit.

(** The initial-object characterization is the original terminal-object
    characterization in the opposite cone category. *)

(** 始对象刻画就是反锥范畴中原来的终对象刻画。 *)

Theorem colimit_iff_initial {J C : Cat} {D : Functor J C} {L : @Ob C}
    (κ : D ⇒∇ L)
  : is_colimit κ ↔ @is_initial (CoconeCat D) (L; op_cone κ).
Proof. exact (limit_iff_terminal (op_cone κ)). Defined.

(** Object uniqueness reuses opposite-limit uniqueness, with the inverse
    laws read in the original category. *)

(** 对象唯一性复用反范畴极限唯一性，并将互逆定律读回原范畴。 *)

Definition colimit_unique {J C : Cat} {D : Functor J C} {L M : @Ob C}
    {κ : D ⇒∇ L} {μ : D ⇒∇ M}
    (Hκ : is_colimit κ) (Hμ : is_colimit μ)
  : L ≅[C] M.
Proof.
  pose (i := limit_unique Hμ Hκ).
  exists i.1, i.2.1. split;
    [exact (snd i.2.2) | exact (fst i.2.2)].
Defined.

(** All selected colimits of a shape are the original selected limits of
    the opposite shape in the opposite category. *)

(** 某形状的全部选定余极限直接取反范畴中反形状的原选定极限结构。 *)

Class HasColimitsOfShape (C J : Cat)
  :=
  { hasOpLimits :: HasLimitsOfShape (C^op) (J^op)
  }.

(** Select an individual colimit from the inherited opposite-shape limits.
    This instance requires an explicitly enabled shape structure. *)

(** 从继承的反形状极限选取单个余极限；该实例要求显式启用形状结构。 *)

Global Program Instance hasColimit {J C : Cat}
    `{HC : !HasColimitsOfShape C J} (D : Functor J C)
  : HasColimit C D
  :=
  {|hasOpLimit := hasLimit (D^opF)
  |}.

Section ColimitFunctor.
Context {J C : Cat} `{HC : !HasColimitsOfShape C J}.

(** The colimit functor is the opposite of the original limit functor after
    [OpFctF]. Endpoint adapters only remove double-opposite categories. *)

(** 余极限函子由原极限函子沿 [OpFctF] 复合后取反得到；端点适配仅去除双重反范畴。 *)

Definition ColimitF
  : Functor (Fct J C) C
  := FromDoubleOpF ∘F
      ((@LimitF (J^op) (C^op) _ ∘F OpFctF)^opF ∘F ToDoubleOpF).

(** The induced map is the morphism action of that same dual functor. *)

(** 诱导映射就是同一个对偶函子的态射作用。 *)

Definition colimit_map {D E : Functor J C} (α : D ⇒ E)
  : Hom (colim D) (colim E)
  := fmap ColimitF α.

(** The injection equation is the opposite limit-map projection equation. *)

(** 注入方程就是反范畴中极限映射的投影方程。 *)

Lemma colimit_map_β {D E : Functor J C} (α : D ⇒ E) (j : @Ob J)
  : colimit_map α ∘ ιcolim[D] j ≈ ιcolim[E] j ∘ α j.
Proof. exact (limit_map_β (α^opN) j). Qed.

(** The inherited functor action respects natural-transformation equality. *)

(** 继承的函子作用保持自然变换相等。 *)

Global Instance colimit_map_proper {D E : Functor J C}
  : Proper (NatEq ==> @HomEq[colim D, colim E]) (@colimit_map D E).
Proof. exact (@functor_fmap_proper (Fct J C) C ColimitF D E). Qed.

(** The identity law is inherited from the composite opposite functor. *)

(** 恒等律继承自复合反函子。 *)

Lemma colimit_map_id {D : Functor J C}
  : colimit_map (idN (F := D)) ≈ id.
Proof. exact (@functor_id (Fct J C) C ColimitF D). Qed.

(** Composition is inherited from the composite opposite functor. *)

(** 复合律继承自复合反函子。 *)

Lemma colimit_map_comp {D E K : Functor J C}
    (β : E ⇒ K) (α : D ⇒ E)
  : colimit_map (β ∘Nv α) ≈ colimit_map β ∘ colimit_map α.
Proof. exact (@functor_comp (Fct J C) C ColimitF D E K β α). Qed.

(** Transformation compatibility is the original limit lift-map law. *)

(** 与图式自然变换的相容性就是原来的极限提升映射定律。 *)

Lemma colimit_desc_map {D E : Functor J C} (α : D ⇒ E) {X}
    (κ : E ⇒∇ X)
  : colim⟨ κ ∘∇ α ⟩ ≈ colim⟨ κ ⟩ ∘ colimit_map α.
Proof. exact (limit_lift_map (α^opN) (op_cone κ)). Qed.

End ColimitFunctor.
