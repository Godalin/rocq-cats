From Cats Require Export
  Cat.Diagram.Dual.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Terminal
  Cat.Limit.Core.

(** * Colimits by Duality *)

(** * 由对偶得到余极限 *)

(** A cocone is colimiting when its opposite cone is limiting. This retains
    the full Type-valued universal property and computational mediators. *)

(** 余锥为余极限，当且仅当其反锥为极限；保留完整 Type 值泛性质与可计算中介。 *)

Definition is_colimit {J C : Cat} {D : Functor J C} {L : @Ob C}
    (κ : D ⇒∇ L)
  := is_limit (CoconeOp κ).

Notation "κ '⦂' 'Colim(' D ')'" := (@is_colimit _ _ D _ κ)
  (at level 50, no associativity) : cat_scope.

(** The direct universal property sends each cocone out of the candidate
    apex, comparing mediators only by the designated hom equality. *)

(** 直接泛性质为每个余锥给出从候选顶点出发的中介，仅按指定 Hom 相等比较中介。 *)

Definition colimit_universal_iff {J C : Cat} {D : Functor J C}
    {L : @Ob C} (κ : D ⇒∇ L)
  : is_colimit κ ↔
      ∀ X (μ : D ⇒∇ X), ∃ h : Hom L X,
        is_unique (λ h, h ∘Cocone κ ≈N μ) h.
Proof.
  split; intros H X μ.
  - exact (H X (CoconeOp μ)).
  - exact (H X (CoconeUnop μ)).
Defined.

(** A cone is limiting exactly when its opposite cocone is colimiting.
    Rebuilding naturality witnesses avoids identifying double-opposite
    functor records. *)

(** 锥为极限，当且仅当反余锥为余极限；重组自然性见证，不等同双重取反函子记录。 *)

Theorem limit_iff_op_colimit {J C : Cat} {D : Functor J C} {L : @Ob C}
    (κ : L ⇒Δ D)
  : is_limit κ ↔ is_colimit (ConeOp κ).
Proof.
  split; intros H X μ.
  - exact (H X (ConeUnop (CoconeUnop μ))).
  - exact (H X (CoconeOp (ConeOp μ))).
Defined.

(** Choose a colimit apex and cocone with its universal property. *)

(** 选择余极限顶点、余锥及其泛性质。 *)

Class HasColimit (C : Cat) {J : Cat} (D : Functor J C)
  :=
  { Colim : @Ob C
  ; colimit_cocone : D ⇒∇ Colim
  ; colimit_universal : is_colimit colimit_cocone
  }.

Arguments Colim {_ _} _ {_}.
Arguments colimit_cocone {_ _} _ {_}.
Arguments colimit_universal {_ _} _ {_} _ _.

Notation "'colim' D" := (Colim D) (at level 35) : ob_scope.
Notation "'ιcolim[' D ']'" := (colimit_cocone D) : hom_scope.

(** Regard a chosen colimit as a limit of the opposite diagram. *)

(** 将选定余极限视为反图式的极限。 *)

Program Definition ColimitOpLimit {J C : Cat} {D : Functor J C}
    `{HC : !HasColimit C D}
  : HasLimit (C^op) (D^opF)
  :=
  {|Lim := colim D
  ; limit_cone := CoconeOp ιcolim[D]
  ; limit_universal := colimit_universal D
  |}.

(** Recover a chosen colimit from a limit of the opposite diagram. This
    conversion does not install a global chosen-structure instance. *)

(** 从反图式的极限恢复选定余极限；该转换不会全局注册选定结构实例。 *)

Program Definition OpLimitColimit {J C : Cat} {D : Functor J C}
    `{HL : !HasLimit (C^op) (D^opF)}
  : HasColimit C D
  :=
  {|Colim := lim (D^opF)
  ; colimit_cocone := CoconeUnop πlim[D^opF]
  |}.
Next Obligation. exact (limit_universal (D^opF)). Defined.

Section ChosenColimit.
Context {J C : Cat} {D : Functor J C} `{HC : !HasColimit C D}.

(** Extract the universal arrow from the selected colimit to a cocone. *)

(** 提取从选定余极限指向余锥的泛箭头。 *)

Definition colimit_desc {X} (κ : D ⇒∇ X)
  : Hom (colim D) X
  := (colimit_universal D X (CoconeOp κ)).1.

(** The extracted arrow uniquely factors the given cocone. *)

(** 提取的箭头唯一分解给定余锥。 *)

Theorem colimit_desc_unique {X} (κ : D ⇒∇ X)
  : is_unique (λ h, h ∘Cocone ιcolim[D] ≈N κ) (colimit_desc κ).
Proof. exact (colimit_universal D X (CoconeOp κ)).2. Defined.

(** Descending after a colimit injection recovers the input cocone leg. *)

(** 下降映射与余极限注入复合后恢复输入余锥腿。 *)

Theorem colimit_β {X} (κ : D ⇒∇ X)
  : colimit_desc κ ∘Cocone ιcolim[D] ≈N κ.
Proof. exact (@this _ _ _ _ _ (colimit_desc_unique κ)). Qed.

(** Descending a cocone obtained from a map recovers that map. *)

(** 由映射得到的余锥，其下降映射恢复原映射。 *)

Theorem colimit_η {X} (f : Hom (colim D) X)
  : colimit_desc (f ∘Cocone ιcolim[D]) ≈ f.
Proof. symmetry. apply colimit_desc_unique. reflexivity. Qed.

(** Equal cocones induce equal arrows, without comparing naturality proofs. *)

(** 相等余锥诱导相等箭头，不比较自然性证明。 *)

Global Instance colimit_desc_proper {X}
  : Proper (NatEq ==> @HomEq[colim D, X]) (@colimit_desc X).
Proof.
  intros κ μ H. apply colimit_desc_unique. rewrite colimit_β. exact H.
Qed.

(** The universal arrow commutes with postcomposition. *)

(** 泛箭头与后合成交换。 *)

Lemma colimit_desc_comp {X Y} (f : Hom X Y) (κ : D ⇒∇ X)
  : colimit_desc (f ∘Cocone κ) ≈ f ∘ colimit_desc κ.
Proof.
  symmetry. apply colimit_desc_unique.
  rewrite <- cocone_comp_assoc, colimit_β. reflexivity.
Qed.

End ChosenColimit.

Notation "'colim⟨' κ '⟩'" := (colimit_desc κ)
  (at level 35) : hom_scope.

(** A colimiting cocone is an initial object of the cocone category. *)

(** 余极限余锥是余锥范畴的始对象。 *)

Theorem colimit_iff_initial {J C : Cat} {D : Functor J C} {L : @Ob C}
    (κ : D ⇒∇ L)
  : is_colimit κ ↔ @is_initial (CoconeCat D) (L; CoconeOp κ).
Proof. exact (limit_iff_terminal (CoconeOp κ)). Defined.

(** Two colimits of one diagram have isomorphic apex objects. The inverse
    orientation of the opposite-category isomorphism is explicit. *)

(** 同一图式的两个余极限具有同构顶点；显式反转反范畴同构的方向。 *)

Definition colimit_unique {J C : Cat} {D : Functor J C} {L M : @Ob C}
    {κ : D ⇒∇ L} {μ : D ⇒∇ M}
    (Hκ : is_colimit κ) (Hμ : is_colimit μ)
  : L ≅[C] M.
Proof.
  pose (i := limit_unique Hμ Hκ).
  exists i.1, i.2.1. split;
    [exact (snd i.2.2) | exact (fst i.2.2)].
Defined.

(** Choose colimits for every diagram of one specified shape. *)

(** 为一个指定形状的每个图式选择余极限。 *)

Class HasColimitsOfShape (C J : Cat)
  :=
  { hasColimit (D : Functor J C) :: HasColimit C D
  }.

Section ColimitFunctor.
Context {J C : Cat} `{HC : !HasColimitsOfShape C J}.

(** A diagram transformation induces a map between the selected colimits. *)

(** 图式自然变换诱导选定余极限之间的映射。 *)

Definition colimit_map {D E : Functor J C} (α : D ⇒ E)
  : Hom (colim D) (colim E)
  := colim⟨ ιcolim[E] ∘Nv α ⟩.

(** The induced map has the specified value on each colimit injection. *)

(** 诱导映射在每个余极限注入上具有指定值。 *)

Lemma colimit_map_β {D E : Functor J C} (α : D ⇒ E) (j : @Ob J)
  : colimit_map α ∘ ιcolim[D] j ≈ ιcolim[E] j ∘ α j.
Proof. exact (colimit_β (ιcolim[E] ∘Nv α) j). Qed.

(** The induced map respects pointwise equality of diagram transformations. *)

(** 诱导映射保持图式自然变换的逐点相等。 *)

Global Instance colimit_map_proper {D E : Functor J C}
  : Proper (NatEq ==> @HomEq[colim D, colim E]) (@colimit_map D E).
Proof.
  intros α β H. apply colimit_desc_proper.
  intros j. cbn. rewrite (H j). reflexivity.
Qed.

(** Identity transformations induce identity colimit maps. *)

(** 恒等自然变换诱导恒等余极限映射。 *)

Lemma colimit_map_id {D : Functor J C}
  : colimit_map (idN (F := D)) ≈ id.
Proof.
  symmetry. apply colimit_desc_unique. intros j. cbn. carw.
Qed.

(** Colimit maps preserve composition of diagram transformations. *)

(** 余极限映射保持图式自然变换的复合。 *)

Lemma colimit_map_comp {D E K : Functor J C}
    (β : E ⇒ K) (α : D ⇒ E)
  : colimit_map (β ∘Nv α) ≈ colimit_map β ∘ colimit_map α.
Proof.
  symmetry. apply colimit_desc_unique. intros j.
  change ((colimit_map β ∘ colimit_map α) ∘ ιcolim[D] j ≈
    ιcolim[K] j ∘ (β j ∘ α j)).
  rewrite comp_assoc, (colimit_map_β α j),
    <- (comp_assoc (colimit_map β)), (colimit_map_β β j).
  apply comp_assoc.
Qed.

(** Selected colimits form a covariant functor on the diagram category. *)

(** 选定余极限在图式范畴上构成协变函子。 *)

Program Definition ColimitF
  : Functor (Fct J C) C
  :=
  {|F0 D := colim D
  ; F1 D E α := colimit_map α
  |}.
Next Obligation. apply colimit_map_id. Qed.
Next Obligation. apply colimit_map_comp. Qed.

(** Descending a cocone commutes with precomposition by a diagram
    transformation. *)

(** 余锥的下降映射与图式自然变换的预合成交换。 *)

Lemma colimit_desc_map {D E : Functor J C} (α : D ⇒ E) {X}
    (κ : E ⇒∇ X)
  : colim⟨ κ ∘Nv α ⟩ ≈ colim⟨ κ ⟩ ∘ colimit_map α.
Proof.
  symmetry. apply colimit_desc_unique. intros j.
  change ((colim⟨ κ ⟩ ∘ colimit_map α) ∘ ιcolim[D] j ≈ κ j ∘ α j).
  rewrite comp_assoc, (colimit_map_β α j),
    <- (comp_assoc (colim⟨ κ ⟩)).
  apply comp_r. exact (colimit_β κ j).
Qed.

End ColimitFunctor.
