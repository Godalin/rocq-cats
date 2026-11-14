From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Binoidal.Bifunctor
  Instance.Set.Core
  Instance.Set.Product
  Cat.Isomorphism.
From Cats Require Export
  Cat.Day.Unit
  Cat.Day.Associator.

(** * Coherence of Day Convolution *)

(** * Day 卷积的相干性 *)

(** Evaluate vertical composition with abstract component maps before
    inserting potentially large coend representatives. *)

(** 先用抽象分量映射求值竖直复合，再代入可能较大的 coend 代表。 *)

Local Lemma day_nat_comp_at@{u p +} {C : Cat}
    {F G H : Fct C (SetCat@{u p _ _ _ _ _})}
    (α : G ⇒ H) (β : F ⇒ G) (Z : @Ob C) (v : F Z)
  : (α ∘Nv β) Z v ≈S α Z (β Z v).
Proof. reflexivity. Defined.

(** ** Inserting the Unit through an Associator

    Fix natural associativity and unit isomorphisms for a bifunctor.
    The base triangle alone relates the two unit insertions; no pentagon
    or coend choice is needed for this equation. *)

(** ** 穿过结合子插入单位

    固定双函子的自然结合与单位同构。仅基三角形律就联系两种单位插入；
    这一方程不需要五边形律或 coend 选择。 *)

Section UnitInsertion.
Context {C : Cat} (T : Fct (C ×C C) C) {I : @Ob C}
    (A : TensorLeftF T ≅N TensorRightF T)
    (L : π2F T I ≅N IdF) (R : π1F T I ≅N IdF).
Context (Ht : ∀ X Y : @Ob C,
    fmap T (X := (X,T (I,Y))) (Y := (X,Y)) (id,L.1 Y) ∘
      A.1 ((X,I),Y) ≈
    fmap T (X := (T (X,I),Y)) (Y := (X,Y)) (R.1 X,id)).

(** At the unit itself, the triangle identifies the inverse insertions. *)

(** 在单位本身处，三角形律识别两个逆插入。 *)

Lemma day_triangle_unit_insertion (X Z : @Ob C)
  : (A.2 ((X,I),Z)).1 ∘
      fmap T (X := (X,Z)) (Y := (X,T (I,Z)))
        (id,(L.2 Z).1) ≈
    fmap T (X := (X,Z)) (Y := (T (X,I),Z)) ((R.2 X).1,id).
Proof.
  apply (iso_cancel_l (A.1 ((X,I),Z); A.2 ((X,I),Z))).
  rewrite <- comp_assoc, (snd (A.2 ((X,I),Z)).2), comp_id_l.
  apply (iso_cancel_l
    (fmap (π2F T X) (L.1 Z);
      functor_is_iso (π2F T X) (L.1 Z) (L.2 Z))).
  change (fmap T (X := (X,T (I,Z))) (Y := (X,Z)) (id,L.1 Z) ∘
    fmap T (X := (X,Z)) (Y := (X,T (I,Z))) (id,(L.2 Z).1) ≈
    fmap T (X := (X,T (I,Z))) (Y := (X,Z)) (id,L.1 Z) ∘
      (A.1 ((X,I),Z) ∘
        fmap T (X := (X,Z)) (Y := (T (X,I),Z)) ((R.2 X).1,id))).
  rewrite <- comp_assoc, Ht, <- !functor_comp.
  transitivity (@id (T (X,Z))).
  - transitivity (fmap T (X := (X,Z)) (Y := (X,Z)) (id,id)).
    + apply (@functor_fmap_proper (C ×C C) C T). split; cbn;
        [apply comp_id_l | exact (snd (L.2 Z).2)].
    + apply functor_id.
  - symmetry.
    transitivity (fmap T (X := (X,Z)) (Y := (X,Z)) (id,id)).
    + transitivity (fmap T (X := (X,Z)) (Y := (X,Z))
        (R.1 X ∘ (R.2 X).1,(@id Z) ∘ id)).
      * symmetry. exact (@functor_comp (C ×C C) C T
          (X,Z) (T (X,I),Z) (X,Z) (R.1 X,id) ((R.2 X).1,id)).
      * apply (@functor_fmap_proper (C ×C C) C T). split; cbn;
          [exact (snd (R.2 X).2) | apply comp_id_l].
    + apply functor_id.
Defined.

(** Transporting a left insertion by the inverse associator gives the
    right insertion in the other tensor coordinate. *)

(** 用逆结合子运输左插入，得到另一个张量坐标中的右插入。 *)

Lemma day_triangle_insertion (X Y Z : @Ob C) (j : Hom I Y)
  : (A.2 ((X,Y),Z)).1 ∘
      fmap T (X := (X,Z)) (Y := (X,T (Y,Z)))
        (id,day_left_arrow T L Z j) ≈
    fmap T (X := (X,Z)) (Y := (T (X,Y),Z))
      (day_right_arrow T R X j,id).
Proof.
  pose proof (nt_naturality (NatIso_inv A.1 A.2)
    (X := ((X,I),Z)) (Y := ((X,Y),Z)) ((id,j),id)) as Hn.
  change ((A.2 ((X,Y),Z)).1 ∘
    fmap T (X := (X,T (I,Z))) (Y := (X,T (Y,Z)))
      (id,fmap T (X := (I,Z)) (Y := (Y,Z)) (j,id)) ≈
    fmap T (X := (T (X,I),Z)) (Y := (T (X,Y),Z))
      (fmap T (X := (X,I)) (Y := (X,Y)) (id,j),id) ∘
      (A.2 ((X,I),Z)).1) in Hn.
  unfold day_left_arrow, day_right_arrow.
  transitivity ((A.2 ((X,Y),Z)).1 ∘
    (fmap T (X := (X,T (I,Z))) (Y := (X,T (Y,Z)))
      (id,fmap T (X := (I,Z)) (Y := (Y,Z)) (j,id)) ∘
    fmap T (X := (X,Z)) (Y := (X,T (I,Z))) (id,(L.2 Z).1))).
  - apply comp_proper; [reflexivity |].
    rewrite <- (@functor_comp (C ×C C) C T). apply (@functor_fmap_proper (C ×C C) C T).
    split; cbn; [symmetry; apply comp_id_l | reflexivity].
  - rewrite <- comp_assoc, Hn, comp_assoc, day_triangle_unit_insertion.
    transitivity (fmap T (X := (X,Z)) (Y := (T (X,Y),Z))
      (fmap T (X := (X,I)) (Y := (X,Y)) (id,j) ∘ (R.2 X).1,
        (@id Z) ∘ id)).
    + symmetry. exact (@functor_comp (C ×C C) C T
        (X,Z) (T (X,I),Z) (T (X,Y),Z)
        (fmap T (X := (X,I)) (Y := (X,Y)) (id,j),id)
        ((R.2 X).1,id)).
    + apply (@functor_fmap_proper (C ×C C) C T).
      split; cbn; [reflexivity | apply comp_id_l].
Defined.

End UnitInsertion.

(** ** Moving Input Actions into Weights

    Select just one convolution. The coend gluing law moves either input
    action into the weight; the unused coordinate is unchanged. *)

(** ** 将输入作用移入权重

    只选择一个卷积。coend 粘合律将任一输入作用移入权重，另一个坐标不变。 *)

Section InputWeights.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C)
    (F G : Fct C (SetCat@{u p _ _ _ _ _}))
    `{HD : !HasDay C T F G}.

(** Move the first input action into its tensor coordinate. *)

(** 将第一个输入的作用移入其张量坐标。 *)

Lemma day_inject_first {X X' Y Z : @Ob C} (f : Hom X X')
    (h : Hom (T (X',Y)) Z) (x : F X) (y : G Y)
  : day_inject T F G (X',Y) h (fmap F f x,y) ≈S
      day_inject T F G (X,Y)
        (h ∘ fmap T (X := (X,Y)) (Y := (X',Y)) (f,id)) (x,y).
Proof.
  symmetry. transitivity (day_inject T F G (X',Y) h
    (fmap F f x,fmap G id y)).
  - exact (day_inject_gluing T F G (p := (X,Y)) (q := (X',Y))
      (f,id) h (x,y)).
  - exact (@func_proper _ _ (day_inject T F G (X',Y) h)
      (fmap F f x,fmap G id y) (fmap F f x,y)
      (reflexivity _,@functor_id C SetCat G Y y)).
Defined.

(** Move the second input action without a symmetry assumption. *)

(** 不假定对称性，移动第二个输入的作用。 *)

Lemma day_inject_second {X Y Y' Z : @Ob C} (g : Hom Y Y')
    (h : Hom (T (X,Y')) Z) (x : F X) (y : G Y)
  : day_inject T F G (X,Y') h (x,fmap G g y) ≈S
      day_inject T F G (X,Y)
        (h ∘ fmap T (X := (X,Y)) (Y := (X,Y')) (id,g)) (x,y).
Proof.
  symmetry. transitivity (day_inject T F G (X,Y') h
    (fmap F id x,fmap G g y)).
  - exact (day_inject_gluing T F G (p := (X,Y)) (q := (X,Y'))
      (id,g) h (x,y)).
  - exact (@func_proper _ _ (day_inject T F G (X,Y') h)
      (fmap F id x,fmap G g y) (x,fmap G g y)
      (@functor_id C SetCat F X x,reflexivity _)).
Defined.

End InputWeights.

(** ** The Day Triangle

    Assume the base triangle, two input functors and the five convolutions
    appearing in this diagram. Joint distinction of ternary generators
    reduces the law to unit insertion. No base pentagon is required. *)

(** ** Day 三角形

    假定基三角形、两个输入函子及此图中出现的五个卷积。三重生成元的联合
    区分性将定律归约到单位插入，不需要基五边形律。 *)

Section Triangle.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C) {I : @Ob C}
    (A : TensorLeftF T ≅N TensorRightF T)
    (L : π2F T I ≅N IdF) (R : π1F T I ≅N IdF).
Context (Ht : ∀ X Y : @Ob C,
    fmap T (X := (X,T (I,Y))) (Y := (X,Y)) (id,L.1 Y) ∘
      A.1 ((X,I),Y) ≈
    fmap T (X := (T (X,I),Y)) (Y := (X,Y)) (R.1 X,id)).
Context (F G : Fct C (SetCat@{u p _ _ _ _ _}))
    `{HFU : !HasDay C T F (DayUnitF I)}
    `{HUG : !HasDay C T (DayUnitF I) G}
    `{HL : !HasDay C T (DayF T F (DayUnitF I)) G}
    `{HR : !HasDay C T F (DayF T (DayUnitF I) G)}
    `{HFG : !HasDay C T F G}.

(** The two routes around the triangle agree in designated natural equality. *)

(** 三角形两路在指定的自然相等下相同。 *)

Lemma day_triangle
  : (DayMapN T (idN (F := F)) (DayLeftUnitorN T L G) ∘Nv
      DayAssociatorN T A F (DayUnitF I) G) ≈N
    DayMapN T (DayRightUnitorN T R F) (idN (F := G)).
Proof.
  apply (day_triple_left_nat_ext T F (DayUnitF I) G).
  intros [[X Y] Z] [[x [j]] y].
  rewrite !day_nat_comp_at.
  pose (l := day_left_arrow T L Z j).
  pose (r := day_right_arrow T R X j).
  assert (Hleft : DayLeftUnitorN T L G (T (Y,Z))
    (day_inject T (DayUnitF I) G (Y,Z) id ({|lower := j|},y)) ≈S
    fmap G l y).
  { transitivity (fmap G (id ∘ l) y).
    - exact (day_left_unitor_β T L G id j y).
    - exact (@functor_fmap_proper C SetCat G _ _ _ _ (comp_id_l l) y). }
  assert (Hright : DayRightUnitorN T R F (T (X,Y))
    (day_inject T F (DayUnitF I) (X,Y) id (x,{|lower := j|})) ≈S
    fmap F r x).
  { transitivity (fmap F (id ∘ r) x).
    - exact (day_right_unitor_β T R F id x j).
    - exact (@functor_fmap_proper C SetCat F _ _ _ _ (comp_id_l r) x). }
  transitivity (day_inject T F G (X,Z)
    (fmap T (X := (X,Z)) (Y := (T (X,Y),Z)) (r,id)) (x,y)).
  - transitivity (DayMapN T (idN (F := F)) (DayLeftUnitorN T L G) (T (T (X,Y),Z))
      (fmap (DayF T F (DayF T (DayUnitF I) G)) ((A.2 ((X,Y),Z)).1)
        (DayTripleRightGenN T F (DayUnitF I) G ((X,Y),Z)
          ((x,{|lower := j|}),y)))).
    + exact (@func_proper _ _
        (DayMapN T (idN (F := F)) (DayLeftUnitorN T L G) (T (T (X,Y),Z)))
        (DayAssociatorN T A F (DayUnitF I) G (T (T (X,Y),Z))
          (DayTripleLeftGenN T F (DayUnitF I) G ((X,Y),Z)
            ((x,{|lower := j|}),y)))
        (fmap (DayF T F (DayF T (DayUnitF I) G)) ((A.2 ((X,Y),Z)).1)
          (DayTripleRightGenN T F (DayUnitF I) G ((X,Y),Z)
            ((x,{|lower := j|}),y)))
        (day_associator_gen T A F (DayUnitF I) G ((X,Y),Z)
          ((x,{|lower := j|}),y))).
    + transitivity (fmap (DayF T F G) ((A.2 ((X,Y),Z)).1)
        (DayMapN T (idN (F := F)) (DayLeftUnitorN T L G) (T (X,T (Y,Z)))
          (DayTripleRightGenN T F (DayUnitF I) G ((X,Y),Z)
            ((x,{|lower := j|}),y)))).
      * exact (nt_naturality (DayMapN T (idN (F := F)) (DayLeftUnitorN T L G))
          ((A.2 ((X,Y),Z)).1)
          (DayTripleRightGenN T F (DayUnitF I) G ((X,Y),Z)
            ((x,{|lower := j|}),y))).
      * transitivity (fmap (DayF T F G) ((A.2 ((X,Y),Z)).1)
          (day_inject T F G (X,T (Y,Z)) id (x,fmap G l y))).
        -- apply (@func_proper _ _
             (fmap (DayF T F G) ((A.2 ((X,Y),Z)).1))).
           transitivity (day_inject T F G (X,T (Y,Z)) id
             (x,DayLeftUnitorN T L G (T (Y,Z))
               (day_inject T (DayUnitF I) G (Y,Z) id
                 ({|lower := j|},y)))).
           ++ exact (day_map_inject T (idN (F := F)) (DayLeftUnitorN T L G)
                (X,T (Y,Z)) id x
                (day_inject T (DayUnitF I) G (Y,Z) id ({|lower := j|},y))).
           ++ exact (@func_proper _ _ (day_inject T F G (X,T (Y,Z)) id)
                (x,_) (x,_) (reflexivity _,Hleft)).
        -- transitivity (fmap (DayF T F G) ((A.2 ((X,Y),Z)).1)
             (day_inject T F G (X,Z)
               (id ∘ fmap T (X := (X,Z)) (Y := (X,T (Y,Z))) (id,l))
               (x,y))).
           ++ exact (@func_proper _ _
                (fmap (DayF T F G) ((A.2 ((X,Y),Z)).1)) _ _
                (day_inject_second T F G l id x y)).
           ++ transitivity (day_inject T F G (X,Z)
                ((A.2 ((X,Y),Z)).1 ∘
                  (id ∘ fmap T (X := (X,Z)) (Y := (X,T (Y,Z))) (id,l)))
                (x,y)).
              ** exact (day_inject_post T F G (X,Z) ((A.2 ((X,Y),Z)).1)
                   (id ∘ fmap T (X := (X,Z)) (Y := (X,T (Y,Z))) (id,l))
                   (x,y)).
              ** apply (@day_inject_proper C T F G HFG (X,Z)).
                 rewrite comp_id_l. exact (day_triangle_insertion T A L R Ht X Y Z j).
  - symmetry. transitivity (day_inject T F G (T (X,Y),Z) id
      (DayRightUnitorN T R F (T (X,Y))
        (day_inject T F (DayUnitF I) (X,Y) id (x,{|lower := j|})),y)).
    + exact (day_map_inject T (DayRightUnitorN T R F) (idN (F := G))
        (T (X,Y),Z) id
        (day_inject T F (DayUnitF I) (X,Y) id (x,{|lower := j|})) y).
    + transitivity (day_inject T F G (T (X,Y),Z) id (fmap F r x,y)).
      * exact (@func_proper _ _ (day_inject T F G (T (X,Y),Z) id)
          (_,y) (_,y) (Hright,reflexivity _)).
      * transitivity (day_inject T F G (X,Z)
          (id ∘ fmap T (X := (X,Z)) (Y := (T (X,Y),Z)) (r,id)) (x,y)).
        -- exact (day_inject_first T F G r id x y).
        -- exact (@day_inject_proper C T F G HFG (X,Z) _ _ _
             (comp_id_l _) (x,y)).
Defined.

(** A pointwise boundary keeps representatives abstract before concrete
    clients insert their computations. *)

(** 逐点边界先保持代表抽象，再由具体客户端代入计算。 *)

Lemma day_triangle_at (Z : @Ob C)
    (v : DayF T (DayF T F (DayUnitF I)) G Z)
  : DayMapN T (idN (F := F)) (DayLeftUnitorN T L G) Z
      (DayAssociatorN T A F (DayUnitF I) G Z v) ≈S
    DayMapN T (DayRightUnitorN T R F) (idN (F := G)) Z v.
Proof.
  pose proof (day_triangle Z v) as H.
  rewrite day_nat_comp_at in H. exact H.
Defined.

End Triangle.

(** ** Weighted Identity Generators

    A single selected convolution suffices to move an output action onto
    an identity generator. This convenient form avoids extra identity weights. *)

(** ** 加权恒等生成元

    只需一个选定卷积，即可将输出作用移到恒等生成元上；这种形式避免多余的
    恒等权重。 *)

Section WeightedGenerators.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C)
    (F G : Fct C (SetCat@{u p _ _ _ _ _}))
    `{HD : !HasDay C T F G}.

(** An output action turns the identity generator into its weighted version. *)

(** 输出作用将恒等生成元转为其加权版本。 *)

Lemma day_gen_post (q : @Ob (C ×C C)) {Z : @Ob C}
    (h : Hom (T q) Z) (xy : DayValuesF F G q)
  : fmap (DayF T F G) h (DayGenN T F G q xy) ≈S
      day_inject T F G q h xy.
Proof.
  transitivity (day_inject T F G q (h ∘ id) xy).
  - exact (day_inject_post T F G q h id xy).
  - exact (@day_inject_proper C T F G HD q Z _ _ (comp_id_r h) xy).
Defined.

End WeightedGenerators.

(** ** Four Inputs Distinguish Natural Maps

    Only the three convolutions in the fully left-associated source are
    selected. The ternary distinction theorem and one parameterized coend
    reduce an additional input without choosing any other bracketing. *)

(** ** 四个输入区分自然映射

    只选择完全左结合来源中的三个卷积。三元区分定理与一个带参数 coend
    再减少一个输入，无需选择任何其他括号。 *)

Section FourInputs.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C)
    (F G H K : Fct C (SetCat@{u p _ _ _ _ _}))
    `{HFG : !HasDay C T F G}
    `{HFGH : !HasDay C T (DayF T F G) H}
    `{HFGHK : !HasDay C T (DayF T (DayF T F G) H) K}.
Context {E : Fct C (SetCat@{u p _ _ _ _ _})}.

(** Testing identity quadruples suffices for natural equality. *)

(** 在恒等四重值上检验即足以得到自然相等。 *)

Lemma day_quad_left_nat_ext
    (α β : DayF T (DayF T (DayF T F G) H) K ⇒ E)
    (P : ∀ a b c d (x : F a) (y : G b) (z : H c) (w : K d),
      α (T (T (T (a,b),c),d))
        (DayTripleLeftGenN T (DayF T F G) H K ((T (a,b),c),d)
          ((DayGenN T F G (a,b) (x,y),z),w)) ≈S
      β (T (T (T (a,b),c),d))
        (DayTripleLeftGenN T (DayF T F G) H K ((T (a,b),c),d)
          ((DayGenN T F G (a,b) (x,y),z),w)))
  : α ≈N β.
Proof.
  apply (day_triple_left_nat_ext T (DayF T F G) H K).
  intros [[U c] d] [[v z] w].
  unshelve epose (f := ({|func t :=
    α (T (T (U,c),d))
      (DayTripleLeftGenN T (DayF T F G) H K ((U,c),d)
        ((fst t,fst (snd t)),snd (snd t)))|}
      : (DayF T F G U ×S (H c ×S K d)) →r E (T (T (U,c),d)))).
  { intros [v0 [z0 w0]] [v1 [z1 w1]] [Hv [Hz Hw]].
    apply func_proper. apply func_proper. exact ((Hv,Hz),Hw). }
  unshelve epose (g := ({|func t :=
    β (T (T (U,c),d))
      (DayTripleLeftGenN T (DayF T F G) H K ((U,c),d)
        ((fst t,fst (snd t)),snd (snd t)))|}
      : (DayF T F G U ×S (H c ×S K d)) →r E (T (T (U,c),d)))).
  { intros [v0 [z0 w0]] [v1 [z1 w1]] [Hv [Hz Hw]].
    apply func_proper. apply func_proper. exact ((Hv,Hz),Hw). }
  assert (Q : f ≈f g).
  { apply (@day_parameter_hom_ext C T F G HFG (H c ×S K d)
      U (E (T (T (U,c),d)))).
    intros [a b] h [x y] [z0 w0].
    pose (v0 := DayGenN T F G (a,b) (x,y)).
    pose (s := DayTripleLeftGenN T (DayF T F G) H K
      ((T (a,b),c),d) ((v0,z0),w0)).
    pose (k := fmap T
      (X := (T (T (a,b),c),d)) (Y := (T (U,c),d))
      (fmap T (X := (T (a,b),c)) (Y := (U,c)) (h,id),id)).
    assert (J : DayTripleLeftGenN T (DayF T F G) H K ((U,c),d)
        ((day_inject T F G (a,b) h (x,y),z0),w0) ≈S
        fmap (DayF T (DayF T (DayF T F G) H) K) k s).
    { transitivity (DayTripleLeftGenN T (DayF T F G) H K ((U,c),d)
        ((fmap (DayF T F G) h v0,fmap H id z0),fmap K id w0)).
      - apply (@func_proper _ _
          (DayTripleLeftGenN T (DayF T F G) H K ((U,c),d))).
        split; [split |].
        + symmetry. exact (day_gen_post T F G (a,b) h (x,y)).
        + symmetry. exact (@functor_id C SetCat H c z0).
        + symmetry. exact (@functor_id C SetCat K d w0).
      - exact (nt_naturality (DayTripleLeftGenN T (DayF T F G) H K)
          (X := ((T (a,b),c),d)) (Y := ((U,c),d)) ((h,id),id)
          ((v0,z0),w0)). }
    change (α (T (T (U,c),d))
      (DayTripleLeftGenN T (DayF T F G) H K ((U,c),d)
        ((day_inject T F G (a,b) h (x,y),z0),w0)) ≈S
      β (T (T (U,c),d))
      (DayTripleLeftGenN T (DayF T F G) H K ((U,c),d)
        ((day_inject T F G (a,b) h (x,y),z0),w0))).
    transitivity (fmap E k (α (T (T (T (a,b),c),d)) s)).
    - transitivity (α (T (T (U,c),d))
        (fmap (DayF T (DayF T (DayF T F G) H) K) k s)).
      + exact (@func_proper _ _ (α (T (T (U,c),d))) _ _ J).
      + exact (nt_naturality α k s).
    - transitivity (fmap E k (β (T (T (T (a,b),c),d)) s)).
      + exact (@func_proper _ _ (fmap E k) _ _ (P a b c d x y z0 w0)).
      + transitivity (β (T (T (U,c),d))
          (fmap (DayF T (DayF T (DayF T F G) H) K) k s)).
        * symmetry. exact (nt_naturality β k s).
        * exact (@func_proper _ _ (β (T (T (U,c),d))) _ _ (symmetry J)). }
  exact (Q (v,(z,w))).
Defined.

End FourInputs.

(** ** Inverting the Base Pentagon

    Day uses the inverse base associator as its weight. Inverse uniqueness
    therefore turns a supplied base pentagon into the equation of weights
    needed below; no equality of inverse witnesses is imposed. *)

(** ** 对基五边形取逆

    Day 以基逆结合子作为权重。故逆的唯一性将给定基五边形转为以下所需的
    权重方程，不要求逆见证本身相等。 *)

Section BasePentagon.
Context {C : Cat} (T : Fct (C ×C C) C)
    (A : TensorLeftF T ≅N TensorRightF T).
Context (Hp : ∀ a b c d : @Ob C,
    A.1 ((a,b),T (c,d)) ∘ A.1 ((T (a,b),c),d) ≈
      fmap T (X := (a,T (T (b,c),d))) (Y := (a,T (b,T (c,d))))
        (id,A.1 ((b,c),d)) ∘
      (A.1 ((a,T (b,c)),d) ∘
        fmap T (X := (T (T (a,b),c),d)) (Y := (T (a,T (b,c)),d))
          (A.1 ((a,b),c),id))).

(** The two reversed paths have equal weights. *)

(** 两条反向路径具有相等权重。 *)

Lemma day_pentagon_weight (a b c d : @Ob C)
  : (A.2 ((T (a,b),c),d)).1 ∘ (A.2 ((a,b),T (c,d))).1 ≈
      fmap T (X := (T (a,T (b,c)),d)) (Y := (T (T (a,b),c),d))
        ((A.2 ((a,b),c)).1,id) ∘
      ((A.2 ((a,T (b,c)),d)).1 ∘
        fmap T (X := (a,T (b,T (c,d)))) (Y := (a,T (T (b,c),d)))
          (id,(A.2 ((b,c),d)).1)).
Proof.
  pose (Hs := is_iso_comp (A.2 ((T (a,b),c),d))
    (A.2 ((a,b),T (c,d)))).
  pose (Hl := is_iso_comp
    (functor_is_iso (π1F T d) (A.1 ((a,b),c)) (A.2 ((a,b),c)))
    (is_iso_comp (A.2 ((a,T (b,c)),d))
      (functor_is_iso (π2F T a) (A.1 ((b,c),d)) (A.2 ((b,c),d))))).
  assert (Heq :
    (fmap (π2F T a) (A.1 ((b,c),d)) ∘ A.1 ((a,T (b,c)),d)) ∘
      fmap (π1F T d) (A.1 ((a,b),c)) ≈
    A.1 ((a,b),T (c,d)) ∘ A.1 ((T (a,b),c),d)).
  { rewrite comp_assoc. symmetry. exact (Hp a b c d). }
  exact (inverse_unique _ _ _ (fst Hs.2)
    (snd (is_iso_equiv Heq Hl).2)).
Defined.

End BasePentagon.

(** ** Computing an Associator on Weighted Triples

    Keep only the four convolution choices required by the associator.
    Its ternary universal extension computes on both weights explicitly. *)

(** ** 在加权三重值上计算结合子

    只保留结合子所需的四个卷积选择。其三元泛延拓显式计算两个权重。 *)

Section AssociatorWeights.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C)
    (A : TensorLeftF T ≅N TensorRightF T)
    (F G H : Fct C (SetCat@{u p _ _ _ _ _}))
    `{HFG : !HasDay C T F G} `{HGH : !HasDay C T G H}
    `{HL : !HasDay C T (DayF T F G) H}
    `{HR : !HasDay C T F (DayF T G H)}.

(** The inverse base associator follows the two original result weights. *)

(** 基逆结合子跟在两个原结果权重之后。 *)

Lemma day_associator_inject {a b c U Z : @Ob C}
    (h : Hom (T (U,c)) Z) (k : Hom (T (a,b)) U)
    (x : F a) (y : G b) (z : H c)
  : DayAssociatorN T A F G H Z
      (day_inject T (DayF T F G) H (U,c) h
        (day_inject T F G (a,b) k (x,y),z)) ≈S
    day_inject T F (DayF T G H) (a,T (b,c))
      ((h ∘ fmap T (X := (T (a,b),c)) (Y := (U,c)) (k,id)) ∘
        (A.2 ((a,b),c)).1)
      (x,day_inject T G H (b,c) id (y,z)).
Proof.
  pose (w := h ∘ fmap T (X := (T (a,b),c)) (Y := (U,c)) (k,id)).
  transitivity (fmap (DayF T F (DayF T G H)) w
    (fmap (DayF T F (DayF T G H)) ((A.2 ((a,b),c)).1)
      (DayTripleRightGenN T F G H ((a,b),c) ((x,y),z)))).
  - exact (day_triple_left_extend_β T (DayAssociatorOperationN T A F G H)
      h k x y z).
  - transitivity (fmap (DayF T F (DayF T G H))
      (w ∘ (A.2 ((a,b),c)).1)
      (DayTripleRightGenN T F G H ((a,b),c) ((x,y),z))).
    + symmetry. exact (@functor_comp C SetCat (DayF T F (DayF T G H))
        _ _ _ w ((A.2 ((a,b),c)).1)
        (DayTripleRightGenN T F G H ((a,b),c) ((x,y),z))).
    + exact (day_gen_post T F (DayF T G H) (a,T (b,c))
        (w ∘ (A.2 ((a,b),c)).1)
        (x,day_inject T G H (b,c) id (y,z))).
Defined.

End AssociatorWeights.

(** ** Associating a Single Outer Weight

    With the four indicated convolution choices, the inner identity weight
    disappears. This is the computation form used by the pentagon. *)

(** ** 对单个外权重结合

    给定四个指定的卷积选择后，内恒等权重消去。这是五边形所用的计算形式。 *)

Section OuterWeight.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C)
    (A : TensorLeftF T ≅N TensorRightF T)
    (F G H : Fct C (SetCat@{u p _ _ _ _ _}))
    `{HFG : !HasDay C T F G} `{HGH : !HasDay C T G H}
    `{HL : !HasDay C T (DayF T F G) H}
    `{HR : !HasDay C T F (DayF T G H)}.

(** Retain the outer weight and append the inverse base associator. *)

(** 保留外权重，并接上基逆结合子。 *)

Lemma day_associator_outer {a b c Z : @Ob C}
    (h : Hom (T (T (a,b),c)) Z) (x : F a) (y : G b) (z : H c)
  : DayAssociatorN T A F G H Z
      (day_inject T (DayF T F G) H (T (a,b),c) h
        (DayGenN T F G (a,b) (x,y),z)) ≈S
    day_inject T F (DayF T G H) (a,T (b,c))
      (h ∘ (A.2 ((a,b),c)).1) (x,DayGenN T G H (b,c) (y,z)).
Proof.
  transitivity (day_inject T F (DayF T G H) (a,T (b,c))
    ((h ∘ fmap T (X := (T (a,b),c)) (Y := (T (a,b),c)) (id,id)) ∘
      (A.2 ((a,b),c)).1) (x,DayGenN T G H (b,c) (y,z))).
  - exact (day_associator_inject T A F G H h id x y z).
  - apply (@day_inject_proper C T F (DayF T G H) HR (a,T (b,c))).
    rewrite functor_id, comp_id_r. reflexivity.
Defined.

End OuterWeight.

(** ** The Day Pentagon

    Fix a base pentagon and precisely the twelve binary choices used by
    the five bracketings of four inputs. No unit, symmetry, or strength
    is assumed. The two routes reduce to the inverse base pentagon. *)

(** ** Day 五边形

    固定基五边形及四个输入的五种括号所用的恰好十二个二元选择。不假定单位、
    对称或强度；两条路径归约到基逆五边形。 *)

Section Pentagon.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C)
    (A : TensorLeftF T ≅N TensorRightF T).
Context (Hp : ∀ a b c d : @Ob C,
    A.1 ((a,b),T (c,d)) ∘ A.1 ((T (a,b),c),d) ≈
      fmap T (X := (a,T (T (b,c),d))) (Y := (a,T (b,T (c,d))))
        (id,A.1 ((b,c),d)) ∘
      (A.1 ((a,T (b,c)),d) ∘
        fmap T (X := (T (T (a,b),c),d)) (Y := (T (a,T (b,c)),d))
          (A.1 ((a,b),c),id))).
Context (F G H K : Fct C (SetCat@{u p _ _ _ _ _}))
    `{HFG : !HasDay C T F G} `{HGH : !HasDay C T G H}
    `{HHK : !HasDay C T H K}
    `{HFGH : !HasDay C T (DayF T F G) H}
    `{HFGH' : !HasDay C T F (DayF T G H)}
    `{HGHK : !HasDay C T (DayF T G H) K}
    `{HGHK' : !HasDay C T G (DayF T H K)}
    `{H0 : !HasDay C T (DayF T (DayF T F G) H) K}
    `{H1 : !HasDay C T (DayF T F G) (DayF T H K)}
    `{H2 : !HasDay C T F (DayF T G (DayF T H K))}
    `{H3 : !HasDay C T (DayF T F (DayF T G H)) K}
    `{H4 : !HasDay C T F (DayF T (DayF T G H) K)}.

(** The short and long associativity routes agree on all convolution values. *)

(** 结合的短路与长路在所有卷积值上相等。 *)

Lemma day_pentagon
  : (DayAssociatorN T A F G (DayF T H K) ∘Nv
      DayAssociatorN T A (DayF T F G) H K) ≈N
    (DayMapN T (HD := H4) (HD' := H2) (idN (F := F))
        (DayAssociatorN T A G H K) ∘Nv
      (DayAssociatorN T A F (DayF T G H) K ∘Nv
        DayMapN T (HD := H0) (HD' := H3)
          (DayAssociatorN T A F G H) (idN (F := K)))).
Proof.
  apply (day_quad_left_nat_ext T F G H K).
  intros a b c d x y z w.
  rewrite !day_nat_comp_at.
  pose (vFG := DayGenN T F G (a,b) (x,y)).
  pose (vGH := DayGenN T G H (b,c) (y,z)).
  pose (vHK := DayGenN T H K (c,d) (z,w)).
  pose (vR := DayGenN T G (DayF T H K) (b,T (c,d)) (y,vHK)).
  pose (s := (A.2 ((T (a,b),c),d)).1).
  pose (t := (A.2 ((a,b),T (c,d))).1).
  transitivity (day_inject T F (DayF T G (DayF T H K))
    (a,T (b,T (c,d))) (s ∘ t) (x,vR)).
  - transitivity (DayAssociatorN T A F G (DayF T H K)
      (T (T (T (a,b),c),d))
      (day_inject T (DayF T F G) (DayF T H K) (T (a,b),T (c,d))
        (id ∘ s) (vFG,vHK))).
    + apply (@func_proper _ _
        (DayAssociatorN T A F G (DayF T H K) (T (T (T (a,b),c),d)))).
      exact (day_associator_outer T A (DayF T F G) H K id vFG z w).
    + transitivity (day_inject T F (DayF T G (DayF T H K))
        (a,T (b,T (c,d))) ((id ∘ s) ∘ t) (x,vR)).
      * exact (day_associator_outer T A F G (DayF T H K) (id ∘ s) x y vHK).
      * exact (@day_inject_proper C T F (DayF T G (DayF T H K)) H2
          (a,T (b,T (c,d))) _ _ _
          (@comp_proper C _ _ _ _ _ (comp_id_l s) _ _ (reflexivity t)) (x,vR)).
  - symmetry.
    pose (B := T (T (T (a,b),c),d)).
    pose (i := id ∘ (A.2 ((a,b),c)).1).
    pose (j := (id ∘ fmap T
      (X := (T (a,T (b,c)),d)) (Y := (T (T (a,b),c),d)) (i,id)) ∘
      (A.2 ((a,T (b,c)),d)).1).
    pose (vL := DayTripleLeftGenN T F G H ((a,b),c) ((x,y),z)).
    pose (v0 := DayTripleLeftGenN T (DayF T F G) H K
      ((T (a,b),c),d) ((vFG,z),w)).
    pose (u := day_inject T F (DayF T G H) (a,T (b,c)) i (x,vGH)).
    pose (v := DayGenN T (DayF T G H) K (T (b,c),d) (vGH,w)).
    assert (M : DayMapN T (HD := H0) (HD' := H3)
          (DayAssociatorN T A F G H) (idN (F := K)) B v0 ≈S
      day_inject T (DayF T F (DayF T G H)) K
        (T (T (a,b),c),d) id (u,w)).
    { transitivity (DayMapN T (HD := H0) (HD' := H3)
          (DayAssociatorN T A F G H) (idN (F := K)) B
        (day_inject T (DayF T (DayF T F G) H) K
          (T (T (a,b),c),d) id (vL,w))).
      - apply (@func_proper _ _
          (DayMapN T (HD := H0) (HD' := H3)
          (DayAssociatorN T A F G H) (idN (F := K)) B)).
        reflexivity.
      - transitivity (day_inject T (DayF T F (DayF T G H)) K
          (T (T (a,b),c),d) id (DayAssociatorN T A F G H (T (T (a,b),c)) vL,w)).
        + exact (day_map_inject T (DayAssociatorN T A F G H)
            (idN (F := K)) (T (T (a,b),c),d) id vL w).
        + apply (@func_proper _ _
            (day_inject T (DayF T F (DayF T G H)) K (T (T (a,b),c),d) id)).
          split; [exact (day_associator_outer T A F G H id x y z) | reflexivity]. }
    transitivity (DayMapN T (HD := H4) (HD' := H2) (idN (F := F))
        (DayAssociatorN T A G H K) B
      (DayAssociatorN T A F (DayF T G H) K B
        (day_inject T (DayF T F (DayF T G H)) K
          (T (T (a,b),c),d) id (u,w)))).
    + apply (@func_proper _ _
        (DayMapN T (HD := H4) (HD' := H2) (idN (F := F))
        (DayAssociatorN T A G H K) B)).
      exact (@func_proper _ _ (DayAssociatorN T A F (DayF T G H) K B) _ _ M).
    + transitivity (DayMapN T (HD := H4) (HD' := H2) (idN (F := F))
        (DayAssociatorN T A G H K) B
        (day_inject T F (DayF T (DayF T G H) K)
          (a,T (T (b,c),d)) j (x,v))).
      * apply (@func_proper _ _
          (DayMapN T (HD := H4) (HD' := H2) (idN (F := F))
        (DayAssociatorN T A G H K) B)).
        exact (day_associator_inject T A F (DayF T G H) K id i x vGH w).
      * transitivity (day_inject T F (DayF T G (DayF T H K))
          (a,T (T (b,c),d)) j
          (x,DayAssociatorN T A G H K (T (T (b,c),d)) v)).
        -- exact (day_map_inject T (idN (F := F)) (DayAssociatorN T A G H K)
             (a,T (T (b,c),d)) j x v).
        -- transitivity (day_inject T F (DayF T G (DayF T H K))
             (a,T (T (b,c),d)) j
             (x,day_inject T G (DayF T H K) (b,T (c,d))
               (id ∘ (A.2 ((b,c),d)).1) (y,vHK))).
           ++ apply (@func_proper _ _ (day_inject T F (DayF T G (DayF T H K))
                (a,T (T (b,c),d)) j)).
              split; [reflexivity |].
              exact (day_associator_outer T A G H K id y z w).
           ++ transitivity (day_inject T F (DayF T G (DayF T H K))
                (a,T (T (b,c),d)) j
                (x,fmap (DayF T G (DayF T H K))
                  (id ∘ (A.2 ((b,c),d)).1) vR)).
              ** apply (@func_proper _ _
                   (day_inject T F (DayF T G (DayF T H K))
                     (a,T (T (b,c),d)) j)).
                 split; [reflexivity |]. symmetry.
                 exact (day_gen_post T G (DayF T H K) (b,T (c,d))
                   (id ∘ (A.2 ((b,c),d)).1) (y,vHK)).
              ** transitivity (day_inject T F (DayF T G (DayF T H K))
                   (a,T (b,T (c,d)))
                   (j ∘ fmap T (X := (a,T (b,T (c,d))))
                     (Y := (a,T (T (b,c),d)))
                     (id,id ∘ (A.2 ((b,c),d)).1)) (x,vR)).
                 --- exact (day_inject_second T F (DayF T G (DayF T H K))
                       (id ∘ (A.2 ((b,c),d)).1) j x vR).
                 --- apply (@day_inject_proper C T F (DayF T G (DayF T H K))
                       H2 (a,T (b,T (c,d)))).
                     unfold j, i, s, t.
                     rewrite !comp_id_l, comp_assoc.
                     transitivity (fmap T
                       (X := (T (a,T (b,c)),d)) (Y := (T (T (a,b),c),d))
                       ((A.2 ((a,b),c)).1,id) ∘
                       ((A.2 ((a,T (b,c)),d)).1 ∘
                         fmap T (X := (a,T (b,T (c,d))))
                           (Y := (a,T (T (b,c),d)))
                           (id,(A.2 ((b,c),d)).1))).
                     { apply comp_proper.
                       { apply (@functor_fmap_proper (C ×C C) C T).
                         split; [apply comp_id_l | reflexivity]. }
                       { apply comp_proper; [reflexivity |].
                         apply (@functor_fmap_proper (C ×C C) C T).
                         split; [reflexivity | apply comp_id_l]. } }
                     { symmetry. exact (day_pentagon_weight T A Hp a b c d). }
Defined.

(** The pointwise pentagon exposes the three intermediate maps before
    a client supplies any large coend representative. *)

(** 逐点五边形在客户端代入较大的 coend 代表之前暴露三个中间映射。 *)

Lemma day_pentagon_at (Z : @Ob C)
    (v : DayF T (DayF T (DayF T F G) H) K Z)
  : DayAssociatorN T A F G (DayF T H K) Z
      (DayAssociatorN T A (DayF T F G) H K Z v) ≈S
    DayMapN T (HD := H4) (HD' := H2) (idN (F := F))
      (DayAssociatorN T A G H K) Z
      (DayAssociatorN T A F (DayF T G H) K Z
        (DayMapN T (HD := H0) (HD' := H3)
          (DayAssociatorN T A F G H) (idN (F := K)) Z v)).
Proof.
  pose proof (day_pentagon Z v) as Hpath.
  rewrite !day_nat_comp_at in Hpath. exact Hpath.
Defined.

End Pentagon.
