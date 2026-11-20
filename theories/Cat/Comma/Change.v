From Cats Require Export
  Cat.Comma.Core.

(** * Change of Comma Diagrams

    A comma arrow can be mapped through an ambient functor, then composed
    with a boundary at either end. The left boundary points into the mapped
    source and the right boundary out of the mapped target. Neither needs
    to be invertible. The construction uses the original comma category
    and compares its side maps in their specified equalities.

    Endpoint and ambient categories retain independent object, hom and
    equality levels. No limit, preservation or choice is assumed. *)

(** * 逗号图式的变化

    逗号箭头先经共同目标函子映射，再与两端边界复合。左边界指向映射后的源，
    右边界从映射后的目标出发；二者都不必可逆。构造复用原逗号范畴，并按
    指定相等比较侧边映射。

    端点及共同目标范畴的对象、Hom 与相等层级独立；不要求极限、保持性或选择。 *)

(** ** Mapping a Comma Arrow

    Fix two diagrams and functors between their three categories. Natural
    boundaries make each mapped square commute, with no inverse data. *)

(** ** 映射逗号箭头

    固定两个图式及其三个范畴间的函子。自然边界使映射后的方形交换，不需逆数据。 *)

Section Change.
Context {A B C A' B' C' : Cat}.
Context {F : Fct A C} {G : Fct B C}.
Context {F' : Fct A' C'} {G' : Fct B' C'}.
Context (L : Fct A A') (R : Fct B B') (K : Fct C C').
Context (α : (F' ∘F L) ⇒ (K ∘F F))
    (β : (K ∘F G) ⇒ (G' ∘F R)).

(** Map the structural arrow and compose with the two boundaries. *)

(** 映射结构箭头，并与两端边界复合。 *)

Program Definition CommaChangeOb (X : F ↓C G)
  : F' ↓C G'
  :=
  {|comma_left_ob := L (comma_left_ob X)
  ; comma_right_ob := R (comma_right_ob X)
  ; comma_arrow := β (comma_right_ob X) ∘ fmap K (comma_arrow X) ∘
      α (comma_left_ob X)
  |}.

(** The side maps retain the supplied endpoint functor actions. *)

(** 侧边保留给定端点函子的箭头作用。 *)

Program Definition comma_change_map {X Y : F ↓C G} (h : Hom X Y)
  : (@Hom (F' ↓C G')) (CommaChangeOb X) (CommaChangeOb Y)
  :=
  {|comma_left := fmap L (comma_left h)
  ; comma_right := fmap R (comma_right h)
  |}.
Next Obligation.
  rewrite <- !(@comp_assoc C').
  rewrite <- (nat_naturality β (comma_right h)).
  change ((β (comma_right_ob Y) ∘ fmap K (fmap G (comma_right h))) ∘
    fmap K (comma_arrow X) ∘ α (comma_left_ob X) ≈
    β (comma_right_ob Y) ∘ fmap K (comma_arrow Y) ∘
    α (comma_left_ob Y) ∘ fmap F' (fmap L (comma_left h))).
  rewrite (comp_assoc (β (comma_right_ob Y))).
  rewrite <- (@fmap_comp _ _ _ _ (@isFct C C' K) _ _ _
    (fmap G (comma_right h)) (comma_arrow X)).
  rewrite (comma_comm h).
  rewrite (@fmap_comp _ _ _ _ (@isFct C C' K) _ _ _
    (comma_arrow Y) (fmap F (comma_left h))).
  rewrite !(@comp_assoc C'), (nat_naturality α (comma_left h)).
  reflexivity.
Defined.

(** Changing the whole diagram is functorial on the original squares. *)

(** 整个图式变化在原交换方形上构成函子。 *)

Program Definition CommaChangeF
  : Fct (F ↓C G) (F' ↓C G')
  :=
  {|fobj := CommaChangeOb
  ; fmap X Y := comma_change_map
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation.
  intros h k [Hl Hr]. split.
  - exact (fmap_proper (IsFct := isFct L) _ _ Hl).
  - exact (fmap_proper (IsFct := isFct R) _ _ Hr).
Qed.
Next Obligation.
  split; [apply (fmap_id (IsFct := isFct L)) |
    apply (fmap_id (IsFct := isFct R))].
Qed.
Next Obligation.
  split; [apply (fmap_comp (IsFct := isFct L)) |
    apply (fmap_comp (IsFct := isFct R))].
Qed.

(** The left projection comparison keeps an identity component. *)

(** 左投影比较保留恒等分量。 *)

Program Definition CommaChangeLeftN
  : (CommaLeftF F' G' ∘F CommaChangeF) ⇒ (L ∘F CommaLeftF F G)
  :=
  {|nt X := id
  |}.
Next Obligation. rewrite comp_id_l, comp_id_r. reflexivity. Qed.

(** Thus the left projection comparison is a natural isomorphism. *)

(** 因而左投影比较为自然同构。 *)

Definition comma_change_left_iso
  : (CommaLeftF F' G' ∘F CommaChangeF) ≅N (L ∘F CommaLeftF F G).
Proof.
  exists CommaChangeLeftN. intro X. exists id.
  split; apply comp_id_l.
Defined.

(** The right projection likewise keeps an identity component. *)

(** 右投影也保留恒等分量。 *)

Program Definition CommaChangeRightN
  : (CommaRightF F' G' ∘F CommaChangeF) ⇒ (R ∘F CommaRightF F G)
  :=
  {|nt X := id
  |}.
Next Obligation. rewrite comp_id_l, comp_id_r. reflexivity. Qed.

(** The right projection comparison has a transparent inverse. *)

(** 右投影比较具有透明逆。 *)

Definition comma_change_right_iso
  : (CommaRightF F' G' ∘F CommaChangeF) ≅N (R ∘F CommaRightF F G).
Proof.
  exists CommaChangeRightN. intro X. exists id.
  split; apply comp_id_l.
Defined.

End Change.

(** ** Equivalent Boundaries

    Keep the functors fixed and vary only the two natural boundaries.
    Pointwise hom equality yields an identity-side isomorphism of the
    resulting comma functors, without equality of transformation records. *)

(** ** 等价边界

    固定各个函子，只改变两个自然边界。逐点 Hom 相等给出所得逗号函子的恒等
    侧边同构，不要求自然变换记录相等。 *)

Section EquivalentBoundaries.
Context {A B C A' B' C' : Cat}.
Context {F : Fct A C} {G : Fct B C}.
Context {F' : Fct A' C'} {G' : Fct B' C'}.
Context (L : Fct A A') (R : Fct B B') (K : Fct C C').
Context {α α' : (F' ∘F L) ⇒ (K ∘F F)}
    {β β' : (K ∘F G) ⇒ (G' ∘F R)}.

(** Equivalent boundaries give equal structural arrows. *)

(** 等价边界给出相等的结构箭头。 *)

Definition comma_change_equiv_arrow (Hα : α ≈N α') (Hβ : β ≈N β')
    (X : F ↓C G)
  : comma_arrow (CommaChangeOb L R K α β X) ≈
      comma_arrow (CommaChangeOb L R K α' β' X).
Proof.
  cbn. rewrite (Hα (comma_left_ob X)), (Hβ (comma_right_ob X)).
  reflexivity.
Defined.

(** Identity side maps compare the two changed objects. *)

(** 恒等侧边映射比较两个变化后的对象。 *)

Program Definition CommaChangeEqN (Hα : α ≈N α') (Hβ : β ≈N β')
  : CommaChangeF L R K α β ⇒ CommaChangeF L R K α' β'
  :=
  {|nt X := {|comma_left := id
             ; comma_right := id
             |}
  |}.
Next Obligation.
  rewrite (@fmap_id _ _ _ _ (@isFct B' C' G')), (@fmap_id _ _ _ _ (@isFct A' C' F')),
    comp_id_l, comp_id_r.
  exact (comma_change_equiv_arrow Hα Hβ X).
Defined.
Next Obligation.
  split; cbn; rewrite comp_id_l, comp_id_r; reflexivity.
Defined.

(** The reverse comparison keeps the same identity side maps. *)

(** 反向比较保留同样的恒等侧边映射。 *)

Program Definition comma_change_equiv_inverse
    (Hα : α ≈N α') (Hβ : β ≈N β') (X : F ↓C G)
  : (@Hom (F' ↓C G')) (CommaChangeOb L R K α' β' X)
      (CommaChangeOb L R K α β X)
  :=
  {|comma_left := id
  ; comma_right := id
  |}.
Next Obligation.
  rewrite (@fmap_id _ _ _ _ (@isFct B' C' G')), (@fmap_id _ _ _ _ (@isFct A' C' F')),
    comp_id_l, comp_id_r.
  symmetry. exact (comma_change_equiv_arrow Hα Hβ X).
Defined.

(** Both directions keep transparent identity components. *)

(** 两个方向都保留透明恒等分量。 *)

Definition comma_change_equiv_iso (Hα : α ≈N α') (Hβ : β ≈N β')
  : CommaChangeF L R K α β ≅N CommaChangeF L R K α' β'.
Proof.
  exists (CommaChangeEqN Hα Hβ). intro X.
  exists (comma_change_equiv_inverse Hα Hβ X).
  split; split; apply comp_id_l.
Defined.

(** Equality witnesses do not affect the comparison's side maps. *)

(** 相等见证不影响比较的侧边映射。 *)

Definition comma_change_equiv_witness_independent
    (Hα : α ≈N α') (Hβ : β ≈N β')
    (Kα : α ≈N α') (Kβ : β ≈N β')
  : CommaChangeEqN Hα Hβ ≈N CommaChangeEqN Kα Kβ.
Proof. intro X. split; reflexivity. Defined.

End EquivalentBoundaries.

(** ** Identity Diagram Change

    Fix one comma diagram. The identity endpoint and ambient functors
    require identity-component boundaries, since their functor records
    need not be definitionally equal. The resulting comparison is an
    isomorphism, not equality of comma objects or functor records. *)

(** ** 恒等图式变化

    固定一个逗号图式。恒等端点及共同目标函子需要以恒等分量给出边界，因为
    函子记录不必定义相等。所得比较为同构，不等同逗号对象或函子记录。 *)

Section IdentityChange.
Context {A B C : Cat} (F : Fct A C) (G : Fct B C).

(** The identity left boundary only changes functor presentations. *)

(** 恒等左边界只改变函子表示。 *)

Program Definition CommaChangeIdLeftN
  : (F ∘F IdF) ⇒ (IdF ∘F F)
  :=
  {|nt X := id
  |}.
Next Obligation. rewrite comp_id_l, comp_id_r. reflexivity. Qed.

(** The right identity boundary has the opposite required direction. *)

(** 右恒等边界具有所需的相反方向。 *)

Program Definition CommaChangeIdRightN
  : (IdF ∘F G) ⇒ (G ∘F IdF)
  :=
  {|nt X := id
  |}.
Next Obligation. rewrite comp_id_l, comp_id_r. reflexivity. Qed.

(** Compare identity change with the unchanged comma category. *)

(** 比较恒等变化与未改变的逗号范畴。 *)

Program Definition CommaChangeIdN
  : CommaChangeF IdF IdF IdF CommaChangeIdLeftN CommaChangeIdRightN
      ⇒ IdF
  :=
  {|nt X := {|comma_left := id
             ; comma_right := id
             |}
  |}.
Next Obligation.
  rewrite (@fmap_id _ _ _ _ (@isFct B C G)), (@fmap_id _ _ _ _ (@isFct A C F)).
  cbn. rewrite !comp_id_l, !comp_id_r. reflexivity.
Defined.
Next Obligation.
  split; cbn; rewrite comp_id_l, comp_id_r; reflexivity.
Defined.

(** The reverse identity comparison keeps both endpoints unchanged. *)

(** 反向恒等比较保持两端点不变。 *)

Program Definition comma_change_id_inverse (X : F ↓C G)
  : (@Hom (F ↓C G)) X
      (CommaChangeF IdF IdF IdF CommaChangeIdLeftN CommaChangeIdRightN X)
  :=
  {|comma_left := id
  ; comma_right := id
  |}.
Next Obligation.
  rewrite (@fmap_id _ _ _ _ (@isFct B C G)), (@fmap_id _ _ _ _ (@isFct A C F)).
  cbn. rewrite !comp_id_l, !comp_id_r. reflexivity.
Defined.

(** Identity diagram change is naturally isomorphic to identity. *)

(** 恒等图式变化自然同构于恒等函子。 *)

Definition comma_change_id_iso
  : CommaChangeF IdF IdF IdF CommaChangeIdLeftN CommaChangeIdRightN
      ≅N IdF.
Proof.
  exists CommaChangeIdN. intro X. exists (comma_change_id_inverse X).
  split; split; apply comp_id_l.
Defined.

End IdentityChange.

(** ** Two Consecutive Diagram Changes

    Fix three diagrams and two compatible changes. Whisker the inner
    boundaries by the second ambient functor, then compose them with the
    outer boundaries. Comparison uses the functor composition laws;
    neither change is required to preserve any universal construction. *)

(** ** 连续两次图式变化

    固定三个图式及两次相容变化。先以第二个共同目标函子须化内边界，再与
    外边界复合。比较只使用函子复合律；不要求任一次变化保持任何泛构造。 *)

Section CompositeChange.
Context {A B C A' B' C' A'' B'' C'' : Cat}.
Context {F : Fct A C} {G : Fct B C}.
Context {F' : Fct A' C'} {G' : Fct B' C'}.
Context {F'' : Fct A'' C''} {G'' : Fct B'' C''}.
Context (L : Fct A A') (R : Fct B B') (K : Fct C C').
Context (L' : Fct A' A'') (R' : Fct B' B'') (K' : Fct C' C'').
Context (α : (F' ∘F L) ⇒ (K ∘F F))
    (β : (K ∘F G) ⇒ (G' ∘F R)).
Context (α' : (F'' ∘F L') ⇒ (K' ∘F F'))
    (β' : (K' ∘F G') ⇒ (G'' ∘F R')).

(** The composite left boundary is mapped inner, then supplied outer. *)

(** 复合左边界由映射后的内边界与给定外边界组成。 *)

Program Definition CommaChangeCompLeftN
  : (F'' ∘F (L' ∘F L)) ⇒ ((K' ∘F K) ∘F F)
  :=
  {|nt X := fmap K' (α X) ∘ α' (L X)
  |}.
Next Obligation.
  rewrite (comp_assoc (fmap K' (α Y))),
    (nat_naturality α' (fmap L f)).
  change (fmap K' (α Y) ∘
    (fmap K' (fmap F' (fmap L f)) ∘ α' (L X)) ≈
    fmap K' (fmap K (fmap F f)) ∘ (fmap K' (α X) ∘ α' (L X))).
  rewrite <- (comp_assoc (fmap K' (α Y))).
  rewrite <- (@fmap_comp _ _ _ _ (@isFct C' C'' K') _ _ _
    (α Y) (fmap F' (fmap L f))), (nat_naturality α f).
  rewrite (@fmap_comp _ _ _ _ (@isFct C' C'' K') _ _ _
    (fmap K (fmap F f)) (α X)), (@comp_assoc C'').
  reflexivity.
Qed.

(** The composite right boundary has the dual pasting order, using the
    same functor action and naturality laws. *)

(** 复合右边界按相反粘合次序组成，使用同一函子作用及自然性定律。 *)

Program Definition CommaChangeCompRightN
  : ((K' ∘F K) ∘F G) ⇒ (G'' ∘F (R' ∘F R))
  :=
  {|nt X := β' (R X) ∘ fmap K' (β X)
  |}.
Next Obligation.
  rewrite (comp_assoc (β' (R Y))).
  rewrite <- (@fmap_comp _ _ _ _ (@isFct C' C'' K') _ _ _
    (β Y) (fmap K (fmap G f))), (nat_naturality β f).
  rewrite (@fmap_comp _ _ _ _ (@isFct C' C'' K') _ _ _
    (fmap G' (fmap R f)) (β X)).
  change (β' (R Y) ∘ (fmap K' (fmap G' (fmap R f)) ∘ fmap K' (β X)) ≈
    fmap G'' (fmap R' (fmap R f)) ∘ (β' (R X) ∘ fmap K' (β X))).
  rewrite <- (comp_assoc (β' (R Y))).
  rewrite (nat_naturality β' (fmap R f)), (@comp_assoc C'').
  reflexivity.
Qed.

(** The two structural arrows agree in the last ambient category. *)

(** 两个结构箭头在最后的共同目标范畴中相等。 *)

Definition comma_change_comp_arrow (X : F ↓C G)
  : comma_arrow (CommaChangeF L' R' K' α' β'
      (CommaChangeF L R K α β X)) ≈
    comma_arrow (CommaChangeF (L' ∘F L) (R' ∘F R) (K' ∘F K)
      CommaChangeCompLeftN CommaChangeCompRightN X).
Proof.
  cbn.
  rewrite (@fmap_comp _ _ _ _ (@isFct C' C'' K') _ _ _
    (β (comma_right_ob X) ∘ fmap K (comma_arrow X))
    (α (comma_left_ob X))).
  rewrite (@fmap_comp _ _ _ _ (@isFct C' C'' K') _ _ _
    (β (comma_right_ob X)) (fmap K (comma_arrow X))).
  rewrite !(@comp_assoc C''). reflexivity.
Defined.

(** Identity sides compare the iterated and composite changes. *)

(** 恒等侧边比较迭代变化与复合变化。 *)

Program Definition CommaChangeCompN
  : (CommaChangeF L' R' K' α' β' ∘F CommaChangeF L R K α β) ⇒
      CommaChangeF (L' ∘F L) (R' ∘F R) (K' ∘F K)
        CommaChangeCompLeftN CommaChangeCompRightN
  :=
  {|nt X := {|comma_left := id
             ; comma_right := id
             |}
  |}.
Next Obligation.
  rewrite (@fmap_id _ _ _ _ (@isFct B'' C'' G'')), (@fmap_id _ _ _ _ (@isFct A'' C'' F'')),
    comp_id_l, comp_id_r.
  exact (comma_change_comp_arrow X).
Defined.
Next Obligation.
  split; cbn; rewrite comp_id_l, comp_id_r; reflexivity.
Defined.

(** Reverse the comparison while preserving both endpoint values. *)

(** 反向比较同时保持两端点的值。 *)

Program Definition comma_change_comp_inverse (X : F ↓C G)
  : (@Hom (F'' ↓C G''))
      (CommaChangeF (L' ∘F L) (R' ∘F R) (K' ∘F K)
        CommaChangeCompLeftN CommaChangeCompRightN X)
      ((CommaChangeF L' R' K' α' β' ∘F CommaChangeF L R K α β) X)
  :=
  {|comma_left := id
  ; comma_right := id
  |}.
Next Obligation.
  rewrite (@fmap_id _ _ _ _ (@isFct B'' C'' G'')), (@fmap_id _ _ _ _ (@isFct A'' C'' F'')),
    comp_id_l, comp_id_r.
  symmetry. exact (comma_change_comp_arrow X).
Defined.

(** Consecutive changes compose up to this specified natural isomorphism. *)

(** 连续变化通过此指定自然同构与复合变化比较。 *)

Definition comma_change_comp_iso
  : (CommaChangeF L' R' K' α' β' ∘F CommaChangeF L R K α β) ≅N
      CommaChangeF (L' ∘F L) (R' ∘F R) (K' ∘F K)
        CommaChangeCompLeftN CommaChangeCompRightN.
Proof.
  exists CommaChangeCompN. intro X. exists (comma_change_comp_inverse X).
  split; split; apply comp_id_l.
Defined.

End CompositeChange.
