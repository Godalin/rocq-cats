From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.Product
  Cat.Natural
  Cat.Binoidal.Bifunctor
  Instance.Set.Core
  Instance.Set.Product.
From Cats Require Export
  Cat.Day.Parameter.

(** * Extending Operations through Nested Day Convolutions *)

(** * 沿嵌套 Day 卷积延拓操作 *)

(** The triples use one fixed bracketing of the indexing category. Only
    their output tensor is rebracketed; the input representatives and
    selected convolution objects are not identified by native equality. *)

(** 三重指标范畴使用一种固定括号。只改变输出张量的括号，不以原生相等
    认同输入代表或选定卷积对象。 *)

(** Three independent input values, with a fixed left bracketing. *)

(** 三个独立输入值，采用固定的左括号。 *)

Definition DayTripleValuesF@{u p +} {C : Cat}
    (F G H : Fct C (SetCat@{u p _ _ _ _ _}))
  : Fct ((C ×C C) ×C C) SetCat
  := @PointwiseProductF _ SetCat SetCat_HasProduct
      (DayValuesF F G ∘F FstF (C ×C C) C)
      (H ∘F SndF (C ×C C) C).

(** ** Slicing a Left-Bracketed Operation

    Fix a natural operation on three inputs, with output at the left
    tensor bracketing. The third input supplies the external parameter
    for extending the first two. No associator is required here. *)

(** ** 切片左括号操作

    固定三个输入上的自然操作，其输出位于左括号张量。第三个输入为前两个
    输入的延拓提供外部参数；此处尚不要求结合子。 *)

Section LeftSlice.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C).
Context {F G H K : Fct C (SetCat@{u p _ _ _ _ _})}.
Context (β : DayTripleValuesF F G H ⇒ (K ∘F TensorLeftF T)).

(** Fix the third object while retaining its value as a parameter. *)

(** 固定第三个对象，而将其值保留为参数。 *)

Program Definition DayTripleLeftSliceN (Z : @Ob C)
  : DayParameterF (H Z) (DayValuesF F G) ⇒ ((K ∘F π1F T Z) ∘F T)
  :=
  {|nt q := β (q,Z)
  |}.
Next Obligation.
  intros [xy w].
  transitivity (β (Y,Z)
    (fmap (DayValuesF F G) f xy, fmap H (@id Z) w)).
  - exact (@func_proper _ _ (β (Y,Z))
      (fmap (DayValuesF F G) f xy,w)
      (fmap (DayValuesF F G) f xy,fmap H (@id Z) w)
      (reflexivity _, symmetry (@functor_id C SetCat H Z w))).
  - exact (nt_naturality β (X := (X,Z)) (Y := (Y,Z)) (f,id) (xy,w)).
Defined.

(** Varying the third object changes parameters and outputs coherently. *)

(** 改变第三个对象时，参数与输出相干地改变。 *)

Lemma day_triple_left_slice_change {Z Z' : @Ob C} (g : Hom Z Z')
    (q : @Ob (C ×C C)) (xy : DayValuesF F G q) (w : H Z)
  : DayTripleLeftSliceN Z' q (xy, fmap H g w) ≈S
      fmap K (fmap T (X := (T q,Z)) (Y := (T q,Z')) (id,g))
        (DayTripleLeftSliceN Z q (xy,w)).
Proof.
  transitivity (β (q,Z')
    (fmap (DayValuesF F G) (@id q) xy, fmap H g w)).
  - exact (@func_proper _ _ (β (q,Z'))
      (xy,fmap H g w)
      (fmap (DayValuesF F G) (@id q) xy,fmap H g w)
      (symmetry (@functor_id (C ×C C) SetCat (DayValuesF F G) q xy),
        reflexivity _)).
  - transitivity (fmap K
      (fmap T (X := (T q,Z)) (Y := (T q,Z')) (fmap T (@id q),g))
        (β (q,Z) (xy,w))).
    + exact (nt_naturality β (X := (q,Z)) (Y := (q,Z')) (id,g) (xy,w)).
    + apply (@functor_fmap_proper C SetCat K). apply functor_fmap_proper.
      split; [apply functor_id | reflexivity].
Defined.

Context `{HFG : !HasDay C T F G}.

(** Extend the first two inputs while the third remains an external value. *)

(** 延拓前两个输入，同时使第三个输入保持为外部值。 *)

Program Definition DayTripleLeftOperationN
  : DayValuesF (DayF T F G) H ⇒ (K ∘F T)
  :=
  {|nt q := _
  |}.
Next Obligation.
  destruct q as [a b].
  exact (DayParameterExtendN T (H b) (DayTripleLeftSliceN b) a).
Defined.
Next Obligation.
  destruct X as [a b], Y as [a' b'], f as [f g]. intros [z w].
  transitivity (fmap K (fmap T (X := (a,b')) (Y := (a',b')) (f,id))
    (DayParameterExtendN T (H b') (DayTripleLeftSliceN b') a
      (z, fmap H g w))).
  - exact (nt_naturality (DayParameterExtendN T (H b')
      (DayTripleLeftSliceN b')) f (z, fmap H g w)).
  - transitivity (fmap K (fmap T (X := (a,b')) (Y := (a',b')) (f,id))
      (fmap K (fmap T (X := (a,b)) (Y := (a,b')) (id,g))
        (DayParameterExtendN T (H b) (DayTripleLeftSliceN b) a (z,w)))).
    + apply (@func_proper _ _
        (fmap K (fmap T (X := (a,b')) (Y := (a',b')) (f,id)))).
      exact (day_parameter_extend_change T (DayTripleLeftSliceN b)
        (DayTripleLeftSliceN b') (fmap H g) (K ∘Nl ProductAtN T g)
        (day_triple_left_slice_change g) a z w).
    + transitivity (fmap K
        (fmap T (X := (a,b')) (Y := (a',b')) (f,id) ∘
          fmap T (X := (a,b)) (Y := (a,b')) (id,g))
          (DayParameterExtendN T (H b) (DayTripleLeftSliceN b) a (z,w))).
      * symmetry. apply (@functor_comp C SetCat K).
      * apply (@functor_fmap_proper C SetCat K).
        symmetry. exact (product_at_map T f g).
Defined.

(** ** Extending the Outer Left Convolution

    Supply just the outer convolution of the first convolution with the
    third input. The ordinary binary Day extension completes the ternary
    operation, with an explicit computation on doubly weighted generators. *)

(** ** 延拓外层左卷积

    只另提供第一层卷积与第三个输入的外层卷积。通常二元 Day 延拓完成三元
    操作，并在双重加权生成元上给出显式计算。 *)

Context `{HL : !HasDay C T (DayF T F G) H}.

(** Extend a natural ternary operation through both selected coends. *)

(** 将自然三元操作延拓过两个选定 coend。 *)

Definition DayTripleLeftExtendN
  : DayF T (DayF T F G) H ⇒ K
  := DayExtendN T DayTripleLeftOperationN.

(** The nested extension composes the two tensor weights in their order. *)

(** 嵌套延拓按原次序复合两个张量权重。 *)

Lemma day_triple_left_extend_β {A B D U Z : @Ob C}
    (h : Hom (T (U,D)) Z) (k : Hom (T (A,B)) U)
    (x : F A) (y : G B) (z : H D)
  : DayTripleLeftExtendN Z
      (day_inject T (DayF T F G) H (U,D) h
        (day_inject T F G (A,B) k (x,y),z)) ≈S
      fmap K (h ∘ fmap T (X := (T (A,B),D)) (Y := (U,D)) (k,id))
        (β ((A,B),D) ((x,y),z)).
Proof.
  transitivity (fmap K h (DayTripleLeftOperationN (U,D)
    (day_inject T F G (A,B) k (x,y),z))).
  - exact (day_extend_β T DayTripleLeftOperationN (U,D) h
      (day_inject T F G (A,B) k (x,y),z)).
  - transitivity (fmap K h
      (fmap K (fmap T (X := (T (A,B),D)) (Y := (U,D)) (k,id))
        (β ((A,B),D) ((x,y),z)))).
    + apply (@func_proper _ _ (fmap K h)).
      exact (day_parameter_extend_β T (H D) (DayTripleLeftSliceN D)
        (A,B) k (x,y) z).
    + symmetry. apply (@functor_comp C SetCat K).
Defined.

End LeftSlice.

(** ** Slicing a Right-Bracketed Operation

    With the same fixed triple indexing, the first input is now external.
    Exchange value coordinates only at the parameter boundary, then reuse
    the same parameterized extension for the second and third inputs. *)

(** ** 切片右括号操作

    保持相同的三重指标，现在使第一个输入处于外部。只在参数边界交换值坐标，
    再对第二、第三个输入复用同一个带参数延拓。 *)

Section RightSlice.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C).
Context {F G H K : Fct C (SetCat@{u p _ _ _ _ _})}.
Context (β : DayTripleValuesF F G H ⇒ (K ∘F TensorRightF T)).

(** Retain the first value as an external parameter of the remaining pair. *)

(** 将第一个值保留为其余值对的外部参数。 *)

Program Definition DayTripleRightSliceN (X : @Ob C)
  : DayParameterF (F X) (DayValuesF G H) ⇒ ((K ∘F π2F T X) ∘F T)
  :=
  {|nt q := _
  |}.
Next Obligation.
  destruct q as [a b].
  unshelve notypeclasses refine
    {|func yzx := β ((X,a),b)
        ((snd yzx,fst (fst yzx)),snd (fst yzx))
    |}.
  intros [[y z] x] [[y' z'] x'] [[Hy Hz] Hx].
  exact (@func_proper _ _ (β ((X,a),b))
    ((x,y),z) ((x',y'),z') ((Hx,Hy),Hz)).
Defined.
Next Obligation.
  destruct X0 as [a b], Y as [a' b'], f as [f g]. intros [[y z] x].
  transitivity (β ((X,a'),b') ((fmap F (@id X) x,fmap G f y),fmap H g z)).
  - exact (@func_proper _ _ (β ((X,a'),b'))
      ((x,fmap G f y),fmap H g z)
      ((fmap F (@id X) x,fmap G f y),fmap H g z)
      ((symmetry (@functor_id C SetCat F X x),reflexivity _),reflexivity _)).
  - exact (nt_naturality β (X := ((X,a),b)) (Y := ((X,a'),b'))
      ((id,f),g) ((x,y),z)).
Defined.

(** Naturality of the ternary operation transports its first parameter. *)

(** 三元操作的自然性运输其第一个参数。 *)

Lemma day_triple_right_slice_change {X X' : @Ob C} (f : Hom X X')
    (q : @Ob (C ×C C)) (yz : DayValuesF G H q) (x : F X)
  : DayTripleRightSliceN X' q (yz,fmap F f x) ≈S
      fmap K (fmap T (X := (X,T q)) (Y := (X',T q)) (f,id))
        (DayTripleRightSliceN X q (yz,x)).
Proof.
  destruct q as [Y Z], yz as [y z].
  transitivity (β ((X',Y),Z)
    ((fmap F f x,fmap G (@id Y) y),fmap H (@id Z) z)).
  - exact (@func_proper _ _ (β ((X',Y),Z))
      ((fmap F f x,y),z)
      ((fmap F f x,fmap G (@id Y) y),fmap H (@id Z) z)
      ((reflexivity _,symmetry (@functor_id C SetCat G Y y)),
        symmetry (@functor_id C SetCat H Z z))).
  - transitivity (fmap K
      (fmap T (X := (X,T (Y,Z))) (Y := (X',T (Y,Z)))
        (f,fmap T (@Cat.Core.id (C ×C C) (Y,Z)))) (β ((X,Y),Z) ((x,y),z))).
    + exact (nt_naturality β (X := ((X,Y),Z)) (Y := ((X',Y),Z))
        ((f,id),id) ((x,y),z)).
    + apply (@functor_fmap_proper C SetCat K). apply functor_fmap_proper.
      split; [reflexivity | apply functor_id].
Defined.

Context `{HGH : !HasDay C T G H}.

(** The same inner descent extends the last pair, retaining the first value. *)

(** 同一个内层下降延拓最后的值对，并保留第一个值。 *)

Program Definition DayTripleRightOperationN
  : DayValuesF F (DayF T G H) ⇒ (K ∘F T)
  :=
  {|nt q := _
  |}.
Next Obligation.
  destruct q as [a b].
  unshelve notypeclasses refine
    {|func xz := DayParameterExtendN T (F a)
        (DayTripleRightSliceN a) b (snd xz,fst xz)
    |}.
  intros [x z] [x' z'] [Hx Hz].
  exact (@func_proper _ _
    (DayParameterExtendN T (F a) (DayTripleRightSliceN a) b)
    (z,x) (z',x') (Hz,Hx)).
Defined.
Next Obligation.
  destruct X as [a b], Y as [a' b'], f as [f g]. intros [x z].
  transitivity (fmap K (fmap T (X := (a',b)) (Y := (a',b')) (id,g))
    (DayParameterExtendN T (F a') (DayTripleRightSliceN a') b
      (z,fmap F f x))).
  - exact (nt_naturality (DayParameterExtendN T (F a')
      (DayTripleRightSliceN a')) g (z,fmap F f x)).
  - transitivity (fmap K (fmap T (X := (a',b)) (Y := (a',b')) (id,g))
      (fmap K (fmap T (X := (a,b)) (Y := (a',b)) (f,id))
        (DayParameterExtendN T (F a) (DayTripleRightSliceN a) b (z,x)))).
    + apply (@func_proper _ _
        (fmap K (fmap T (X := (a',b)) (Y := (a',b')) (id,g)))).
      exact (day_parameter_extend_change T (DayTripleRightSliceN a)
        (DayTripleRightSliceN a') (fmap F f) (K ∘Nl ProductFirstAtN T f)
        (day_triple_right_slice_change f) b z x).
    + transitivity (fmap K
        (fmap T (X := (a',b)) (Y := (a',b')) (id,g) ∘
          fmap T (X := (a,b)) (Y := (a',b)) (f,id))
          (DayParameterExtendN T (F a) (DayTripleRightSliceN a) b (z,x))).
      * symmetry. apply (@functor_comp C SetCat K).
      * apply (@functor_fmap_proper C SetCat K).
        rewrite <- functor_comp. apply functor_fmap_proper.
        split; cbn; carw.
Defined.

Context `{HR : !HasDay C T F (DayF T G H)}.

(** Extend through the right inner coend and then the outer coend. *)

(** 先延拓过右内层 coend，再延拓过外层 coend。 *)

Definition DayTripleRightExtendN
  : DayF T F (DayF T G H) ⇒ K
  := DayExtendN T DayTripleRightOperationN.

(** The right extension has the corresponding ordered weight computation. *)

(** 右侧延拓具有相应的有序权重计算。 *)

Lemma day_triple_right_extend_β {A B D U Z : @Ob C}
    (h : Hom (T (A,U)) Z) (k : Hom (T (B,D)) U)
    (x : F A) (y : G B) (z : H D)
  : DayTripleRightExtendN Z
      (day_inject T F (DayF T G H) (A,U) h
        (x,day_inject T G H (B,D) k (y,z))) ≈S
      fmap K (h ∘ fmap T (X := (A,T (B,D))) (Y := (A,U)) (id,k))
        (β ((A,B),D) ((x,y),z)).
Proof.
  transitivity (fmap K h (DayTripleRightOperationN (A,U)
    (x,day_inject T G H (B,D) k (y,z)))).
  - exact (day_extend_β T DayTripleRightOperationN (A,U) h
      (x,day_inject T G H (B,D) k (y,z))).
  - transitivity (fmap K h
      (fmap K (fmap T (X := (A,T (B,D))) (Y := (A,U)) (id,k))
        (β ((A,B),D) ((x,y),z)))).
    + apply (@func_proper _ _ (fmap K h)).
      exact (day_parameter_extend_β T (F A) (DayTripleRightSliceN A)
        (B,D) k (y,z) x).
    + symmetry. apply (@functor_comp C SetCat K).
Defined.

End RightSlice.

(** ** Left Nested Generators

    Fix only the left inner and outer convolutions. Identity weights give
    a natural ternary generator. Arbitrary nested weights are its images
    under the output functor, so they introduce no further choices. *)

(** ** 左嵌套生成元

    只固定左内层与外层卷积。恒等权重给出自然三元生成元；任意嵌套权重都是
    它在输出函子下的像，因此不再引入选择。 *)

Section LeftGenerators.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C).
Context (F G H : Fct C (SetCat@{u p _ _ _ _ _}))
    `{HFG : !HasDay C T F G} `{HL : !HasDay C T (DayF T F G) H}.

(** Insert both pairs with identity weights. *)

(** 用恒等权重插入两个值对。 *)

Program Definition DayTripleLeftGenN
  : DayTripleValuesF F G H ⇒ (DayF T (DayF T F G) H ∘F TensorLeftF T)
  :=
  {|nt q := _
  |}.
Next Obligation.
  destruct q as [[a b] d].
  unshelve notypeclasses refine
    {|func xyz := day_inject T (DayF T F G) H (T (a,b),d) id
        (day_inject T F G (a,b) id (fst xyz),snd xyz)
    |}.
  intros [xy z] [xy' z'] [Hxy Hz].
  apply (@func_proper _ _ (day_inject T (DayF T F G) H (T (a,b),d) id)).
  split; [apply func_proper; exact Hxy | exact Hz].
Defined.
Next Obligation.
  destruct X as [[a b] d], Y as [[a' b'] d'], f as [[f g] h].
  intros [[x y] z].
  transitivity (day_inject T (DayF T F G) H (T (a',b'),d') id
    (fmap (DayF T F G) (fmap T (X := (a,b)) (Y := (a',b')) (f,g))
      (day_inject T F G (a,b) id (x,y)),fmap H h z)).
  - exact (@func_proper _ _
      (day_inject T (DayF T F G) H (T (a',b'),d') id)
      (day_inject T F G (a',b') id (fmap F f x,fmap G g y),fmap H h z)
      (fmap (DayF T F G) (fmap T (X := (a,b)) (Y := (a',b')) (f,g))
        (day_inject T F G (a,b) id (x,y)),fmap H h z)
      (nt_naturality (DayGenN T F G)
        (X := (a,b)) (Y := (a',b')) (f,g) (x,y),reflexivity _)).
  - exact (nt_naturality (DayGenN T (DayF T F G) H)
      (X := (T (a,b),d)) (Y := (T (a',b'),d'))
      (fmap T (X := (a,b)) (Y := (a',b')) (f,g),h)
      (day_inject T F G (a,b) id (x,y),z)).
Defined.

(** Move both weights into the output action by postcomposition and gluing. *)

(** 由后合成和粘合，将两个权重移入输出作用。 *)

Lemma day_triple_left_inject {A B D U Z : @Ob C}
    (h : Hom (T (U,D)) Z) (k : Hom (T (A,B)) U)
    (x : F A) (y : G B) (z : H D)
  : fmap (DayF T (DayF T F G) H)
      (h ∘ fmap T (X := (T (A,B),D)) (Y := (U,D)) (k,id))
      (DayTripleLeftGenN ((A,B),D) ((x,y),z)) ≈S
      day_inject T (DayF T F G) H (U,D) h
        (day_inject T F G (A,B) k (x,y),z).
Proof.
  pose (v := h ∘ fmap T (X := (T (A,B),D)) (Y := (U,D)) (k,id)).
  transitivity (day_inject T (DayF T F G) H (T (A,B),D) v
    (day_inject T F G (A,B) id (x,y),z)).
  { transitivity (day_inject T (DayF T F G) H (T (A,B),D) (v ∘ id)
      (day_inject T F G (A,B) id (x,y),z)).
    - exact (day_inject_post T (DayF T F G) H (T (A,B),D) v id
        (day_inject T F G (A,B) id (x,y),z)).
    - exact (@day_inject_proper C T (DayF T F G) H HL (T (A,B),D) Z
        _ _ (comp_id_r v) (day_inject T F G (A,B) id (x,y),z)). }
  transitivity (day_inject T (DayF T F G) H (U,D) h
    (fmap (DayValuesF (DayF T F G) H)
      (X := (T (A,B),D)) (Y := (U,D)) (k,id)
      (day_inject T F G (A,B) id (x,y),z))).
  - exact (day_inject_gluing T (DayF T F G) H
      (p := (T (A,B),D)) (q := (U,D)) (k,id) h
      (day_inject T F G (A,B) id (x,y),z)).
  - apply (@func_proper _ _ (day_inject T (DayF T F G) H (U,D) h)).
    split; [| exact (@functor_id C SetCat H D z)].
    transitivity (day_inject T F G (A,B) (k ∘ id) (x,y)).
    + exact (day_inject_post T F G (A,B) k id (x,y)).
    + exact (@day_inject_proper C T F G HFG (A,B) U _ _
        (comp_id_r k) (x,y)).
Defined.

(** Doubly weighted generators distinguish all outgoing maps. *)

(** 双重加权生成元区分全部出射映射。 *)

Lemma day_triple_left_hom_ext {Z : @Ob C} {E : SetC@{u p}}
    (f g : DayF T (DayF T F G) H Z →r E)
    (P : ∀ A B D U (h : Hom (T (U,D)) Z) (k : Hom (T (A,B)) U)
      (x : F A) (y : G B) (z : H D),
      f (day_inject T (DayF T F G) H (U,D) h
        (day_inject T F G (A,B) k (x,y),z)) ≈S
      g (day_inject T (DayF T F G) H (U,D) h
        (day_inject T F G (A,B) k (x,y),z)))
  : f ≈f g.
Proof.
  apply (day_hom_ext T (DayF T F G) H). intros [U D] h.
  apply (@day_parameter_hom_ext C T F G HFG (H D) U E).
  intros [A B] k [x y] z. exact (P A B D U h k x y z).
Defined.

(** Naturality reduces equality of transformations to identity triple values. *)

(** 自然性将变换相等归约到恒等三重值。 *)

Lemma day_triple_left_nat_ext {K : Fct C (SetCat@{u p _ _ _ _ _})}
    (α γ : DayF T (DayF T F G) H ⇒ K)
    (P : ∀ q (xyz : DayTripleValuesF F G H q),
      α (TensorLeftF T q) (DayTripleLeftGenN q xyz) ≈S
      γ (TensorLeftF T q) (DayTripleLeftGenN q xyz))
  : α ≈N γ.
Proof.
  intros Z. apply (@day_triple_left_hom_ext Z (K Z) (α Z) (γ Z)).
  intros A B D U h k x y z.
  pose (w := h ∘ fmap T (X := (T (A,B),D)) (Y := (U,D)) (k,id)).
  transitivity (α Z (fmap (DayF T (DayF T F G) H) w
    (DayTripleLeftGenN ((A,B),D) ((x,y),z)))).
  - apply (@func_proper _ _ (α Z)). symmetry.
    exact (day_triple_left_inject h k x y z).
  - transitivity (fmap K w
      (α (T (T (A,B),D)) (DayTripleLeftGenN ((A,B),D) ((x,y),z)))).
    + exact (nt_naturality α w (DayTripleLeftGenN ((A,B),D) ((x,y),z))).
    + transitivity (fmap K w
        (γ (T (T (A,B),D)) (DayTripleLeftGenN ((A,B),D) ((x,y),z)))).
      * exact (@func_proper _ _ (fmap K w) _ _ (P ((A,B),D) ((x,y),z))).
      * transitivity (γ Z (fmap (DayF T (DayF T F G) H) w
          (DayTripleLeftGenN ((A,B),D) ((x,y),z)))).
        -- symmetry. exact (nt_naturality γ w
             (DayTripleLeftGenN ((A,B),D) ((x,y),z))).
        -- apply (@func_proper _ _ (γ Z)).
           exact (day_triple_left_inject h k x y z).
Defined.

End LeftGenerators.

(** ** Right Nested Generators

    Assume only the right inner and outer convolutions. The analogous
    generator uses the same left-bracketed input triples, so both output
    bracketings can subsequently be compared by natural transformations. *)

(** ** 右嵌套生成元

    只假定右内层与外层卷积。相应生成元仍使用同一个左括号输入三重积，
    以便随后用自然变换比较两个输出括号。 *)

Section RightGenerators.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C).
Context (F G H : Fct C (SetCat@{u p _ _ _ _ _}))
    `{HGH : !HasDay C T G H} `{HR : !HasDay C T F (DayF T G H)}.

(** Nest the second pair inside the first, retaining the same input order. *)

(** 将第二个值对嵌套在第一对之内，保留相同输入顺序。 *)

Program Definition DayTripleRightGenN
  : DayTripleValuesF F G H ⇒ (DayF T F (DayF T G H) ∘F TensorRightF T)
  :=
  {|nt q := _
  |}.
Next Obligation.
  destruct q as [[a b] d].
  unshelve notypeclasses refine
    {|func xyz := day_inject T F (DayF T G H) (a,T (b,d)) id
        (fst (fst xyz),day_inject T G H (b,d) id (snd (fst xyz),snd xyz))
    |}.
  intros [[x y] z] [[x' y'] z'] [[Hx Hy] Hz].
  apply (@func_proper _ _ (day_inject T F (DayF T G H) (a,T (b,d)) id)).
  split; [exact Hx | apply func_proper; split; assumption].
Defined.
Next Obligation.
  destruct X as [[a b] d], Y as [[a' b'] d'], f as [[f g] h].
  intros [[x y] z].
  transitivity (day_inject T F (DayF T G H) (a',T (b',d')) id
    (fmap F f x,fmap (DayF T G H)
      (fmap T (X := (b,d)) (Y := (b',d')) (g,h))
      (day_inject T G H (b,d) id (y,z)))).
  - exact (@func_proper _ _
      (day_inject T F (DayF T G H) (a',T (b',d')) id)
      (fmap F f x,day_inject T G H (b',d') id (fmap G g y,fmap H h z))
      (fmap F f x,fmap (DayF T G H)
        (fmap T (X := (b,d)) (Y := (b',d')) (g,h))
        (day_inject T G H (b,d) id (y,z)))
      (reflexivity _,nt_naturality (DayGenN T G H)
        (X := (b,d)) (Y := (b',d')) (g,h) (y,z))).
  - exact (nt_naturality (DayGenN T F (DayF T G H))
      (X := (a,T (b,d))) (Y := (a',T (b',d')))
      (f,fmap T (X := (b,d)) (Y := (b',d')) (g,h))
      (x,day_inject T G H (b,d) id (y,z))).
Defined.

(** Move right nested weights into the output action by the same gluing laws. *)

(** 用同样的粘合定律将右嵌套权重移入输出作用。 *)

Lemma day_triple_right_inject {A B D U Z : @Ob C}
    (h : Hom (T (A,U)) Z) (k : Hom (T (B,D)) U)
    (x : F A) (y : G B) (z : H D)
  : fmap (DayF T F (DayF T G H))
      (h ∘ fmap T (X := (A,T (B,D))) (Y := (A,U)) (id,k))
      (DayTripleRightGenN ((A,B),D) ((x,y),z)) ≈S
      day_inject T F (DayF T G H) (A,U) h
        (x,day_inject T G H (B,D) k (y,z)).
Proof.
  pose (v := h ∘ fmap T (X := (A,T (B,D))) (Y := (A,U)) (id,k)).
  transitivity (day_inject T F (DayF T G H) (A,T (B,D)) v
    (x,day_inject T G H (B,D) id (y,z))).
  { transitivity (day_inject T F (DayF T G H) (A,T (B,D)) (v ∘ id)
      (x,day_inject T G H (B,D) id (y,z))).
    - exact (day_inject_post T F (DayF T G H) (A,T (B,D)) v id
        (x,day_inject T G H (B,D) id (y,z))).
    - exact (@day_inject_proper C T F (DayF T G H) HR (A,T (B,D)) Z
        _ _ (comp_id_r v) (x,day_inject T G H (B,D) id (y,z))). }
  transitivity (day_inject T F (DayF T G H) (A,U) h
    (fmap (DayValuesF F (DayF T G H))
      (X := (A,T (B,D))) (Y := (A,U)) (id,k)
      (x,day_inject T G H (B,D) id (y,z)))).
  - exact (day_inject_gluing T F (DayF T G H)
      (p := (A,T (B,D))) (q := (A,U)) (id,k) h
      (x,day_inject T G H (B,D) id (y,z))).
  - apply (@func_proper _ _ (day_inject T F (DayF T G H) (A,U) h)).
    split; [exact (@functor_id C SetCat F A x) |].
    transitivity (day_inject T G H (B,D) (k ∘ id) (y,z)).
    + exact (day_inject_post T G H (B,D) k id (y,z)).
    + exact (@day_inject_proper C T G H HGH (B,D) U _ _
        (comp_id_r k) (y,z)).
Defined.

(** Right doubly weighted generators distinguish outgoing maps. *)

(** 右侧双重加权生成元区分出射映射。 *)

Lemma day_triple_right_hom_ext {Z : @Ob C} {E : SetC@{u p}}
    (f g : DayF T F (DayF T G H) Z →r E)
    (P : ∀ A B D U (h : Hom (T (A,U)) Z) (k : Hom (T (B,D)) U)
      (x : F A) (y : G B) (z : H D),
      f (day_inject T F (DayF T G H) (A,U) h
        (x,day_inject T G H (B,D) k (y,z))) ≈S
      g (day_inject T F (DayF T G H) (A,U) h
        (x,day_inject T G H (B,D) k (y,z))))
  : f ≈f g.
Proof.
  apply (day_hom_ext T F (DayF T G H)). intros [A U] h.
  unshelve epose (f' := ({|func zy := f (day_inject T F (DayF T G H)
    (A,U) h (snd zy,fst zy))|} : (DayF T G H U ×S F A) →r E)).
  { intros [z x] [z' x'] [Hz Hx]. apply func_proper.
    apply func_proper. split; assumption. }
  unshelve epose (g' := ({|func zy := g (day_inject T F (DayF T G H)
    (A,U) h (snd zy,fst zy))|} : (DayF T G H U ×S F A) →r E)).
  { intros [z x] [z' x'] [Hz Hx]. apply func_proper.
    apply func_proper. split; assumption. }
  assert (Q : f' ≈f g').
  { apply (@day_parameter_hom_ext C T G H HGH (F A) U E).
    intros [B D] k [y z] x. exact (P A B D U h k x y z). }
  intros [x z]. exact (Q (z,x)).
Defined.

(** Naturality also reduces right transformation equality to identity triples. *)

(** 自然性同样将右侧变换相等归约到恒等三重值。 *)

Lemma day_triple_right_nat_ext {K : Fct C (SetCat@{u p _ _ _ _ _})}
    (α γ : DayF T F (DayF T G H) ⇒ K)
    (P : ∀ q (xyz : DayTripleValuesF F G H q),
      α (TensorRightF T q) (DayTripleRightGenN q xyz) ≈S
      γ (TensorRightF T q) (DayTripleRightGenN q xyz))
  : α ≈N γ.
Proof.
  intros Z. apply (@day_triple_right_hom_ext Z (K Z) (α Z) (γ Z)).
  intros A B D U h k x y z.
  pose (w := h ∘ fmap T (X := (A,T (B,D))) (Y := (A,U)) (id,k)).
  transitivity (α Z (fmap (DayF T F (DayF T G H)) w
    (DayTripleRightGenN ((A,B),D) ((x,y),z)))).
  - apply (@func_proper _ _ (α Z)). symmetry.
    exact (day_triple_right_inject h k x y z).
  - transitivity (fmap K w
      (α (T (A,T (B,D))) (DayTripleRightGenN ((A,B),D) ((x,y),z)))).
    + exact (nt_naturality α w (DayTripleRightGenN ((A,B),D) ((x,y),z))).
    + transitivity (fmap K w
        (γ (T (A,T (B,D))) (DayTripleRightGenN ((A,B),D) ((x,y),z)))).
      * exact (@func_proper _ _ (fmap K w) _ _ (P ((A,B),D) ((x,y),z))).
      * transitivity (γ Z (fmap (DayF T F (DayF T G H)) w
          (DayTripleRightGenN ((A,B),D) ((x,y),z)))).
        -- symmetry. exact (nt_naturality γ w
             (DayTripleRightGenN ((A,B),D) ((x,y),z))).
        -- apply (@func_proper _ _ (γ Z)).
           exact (day_triple_right_inject h k x y z).
Defined.

End RightGenerators.

(** ** Ternary Universal Correspondences

    With the selected convolutions for a bracketing, extension restricts
    back to the given ternary operation on identity generators. Their joint
    distinction then proves uniqueness, without identifying functor records. *)

(** ** 三元泛对应

    给定一种括号所需的选定卷积后，延拓在恒等生成元上恢复原三元操作。
    生成元的联合区分性随后证明唯一性，不认同函子记录。 *)

Section TernaryUniversal.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C).
Context {F G H K : Fct C (SetCat@{u p _ _ _ _ _})}.

(** Restricting a left extension to its ternary generators recovers the input. *)

(** 将左延拓限制到其三元生成元，恢复输入。 *)

Lemma day_triple_left_extend_gen
    `{HFG : !HasDay C T F G} `{HL : !HasDay C T (DayF T F G) H}
    (β : DayTripleValuesF F G H ⇒ (K ∘F TensorLeftF T))
    (q : @Ob ((C ×C C) ×C C)) (xyz : DayTripleValuesF F G H q)
  : DayTripleLeftExtendN T β (TensorLeftF T q)
      (DayTripleLeftGenN T F G H q xyz) ≈S β q xyz.
Proof.
  destruct q as [[a b] d], xyz as [[x y] z].
  transitivity (fmap K
    (id ∘ fmap T (X := (T (a,b),d)) (Y := (T (a,b),d)) (id,id))
      (β ((a,b),d) ((x,y),z))).
  - exact (day_triple_left_extend_β T β id id x y z).
  - transitivity (fmap K (@id (T (T (a,b),d)))
      (β ((a,b),d) ((x,y),z))).
    + apply (@functor_fmap_proper C SetCat K).
      rewrite functor_id, comp_id_l. reflexivity.
    + exact (@functor_id C SetCat K _ (β ((a,b),d) ((x,y),z))).
Defined.

(** The left ternary operation determines its natural extension uniquely. *)

(** 左三元操作唯一决定其自然延拓。 *)

Lemma day_triple_left_extend_unique
    `{HFG : !HasDay C T F G} `{HL : !HasDay C T (DayF T F G) H}
    (β : DayTripleValuesF F G H ⇒ (K ∘F TensorLeftF T))
    (α : DayF T (DayF T F G) H ⇒ K)
    (P : ∀ q (xyz : DayTripleValuesF F G H q),
      α (TensorLeftF T q) (DayTripleLeftGenN T F G H q xyz) ≈S β q xyz)
  : α ≈N DayTripleLeftExtendN T β.
Proof.
  apply (day_triple_left_nat_ext T F G H). intros q xyz.
  transitivity (β q xyz); [exact (P q xyz) |].
  symmetry. exact (day_triple_left_extend_gen β q xyz).
Defined.

(** The right restriction uses the same ordered-weight computation. *)

(** 右限制使用相同的有序权重计算。 *)

Lemma day_triple_right_extend_gen
    `{HGH : !HasDay C T G H} `{HR : !HasDay C T F (DayF T G H)}
    (β : DayTripleValuesF F G H ⇒ (K ∘F TensorRightF T))
    (q : @Ob ((C ×C C) ×C C)) (xyz : DayTripleValuesF F G H q)
  : DayTripleRightExtendN T β (TensorRightF T q)
      (DayTripleRightGenN T F G H q xyz) ≈S β q xyz.
Proof.
  destruct q as [[a b] d], xyz as [[x y] z].
  transitivity (fmap K
    (id ∘ fmap T (X := (a,T (b,d))) (Y := (a,T (b,d))) (id,id))
      (β ((a,b),d) ((x,y),z))).
  - exact (day_triple_right_extend_β T β id id x y z).
  - transitivity (fmap K (@id (T (a,T (b,d))))
      (β ((a,b),d) ((x,y),z))).
    + apply (@functor_fmap_proper C SetCat K).
      rewrite functor_id, comp_id_l. reflexivity.
    + exact (@functor_id C SetCat K _ (β ((a,b),d) ((x,y),z))).
Defined.

(** The right ternary operation also determines its natural extension uniquely. *)

(** 右三元操作也唯一决定其自然延拓。 *)

Lemma day_triple_right_extend_unique
    `{HGH : !HasDay C T G H} `{HR : !HasDay C T F (DayF T G H)}
    (β : DayTripleValuesF F G H ⇒ (K ∘F TensorRightF T))
    (α : DayF T F (DayF T G H) ⇒ K)
    (P : ∀ q (xyz : DayTripleValuesF F G H q),
      α (TensorRightF T q) (DayTripleRightGenN T F G H q xyz) ≈S β q xyz)
  : α ≈N DayTripleRightExtendN T β.
Proof.
  apply (day_triple_right_nat_ext T F G H). intros q xyz.
  transitivity (β q xyz); [exact (P q xyz) |].
  symmetry. exact (day_triple_right_extend_gen β q xyz).
Defined.

End TernaryUniversal.

(** ** Changing the Three Inputs

    Require only the selected convolutions at the two endpoints. The
    existing binary Day map acts twice; its generator law describes the
    result without comparing choices of coends. *)

(** ** 改变三个输入

    只要求两个端点的选定卷积。已有二元 Day 映射作用两次；其生成元定律
    描述所得结果，无需比较 coend 选择。 *)

Section TripleMaps.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C).
Context {F G H F' G' H' : Fct C (SetCat@{u p _ _ _ _ _})}.
Context (α : F ⇒ F') (β : G ⇒ G') (γ : H ⇒ H').

(** The left map first changes the inner pair, then the outer pair. *)

(** 左映射先改变内层值对，再改变外层值对。 *)

Definition DayTripleLeftMapN
    `{HFG : !HasDay C T F G} `{HFG' : !HasDay C T F' G'}
    `{HL : !HasDay C T (DayF T F G) H}
    `{HL' : !HasDay C T (DayF T F' G') H'}
  : DayF T (DayF T F G) H ⇒ DayF T (DayF T F' G') H'
  := DayMapN T (DayMapN T α β) γ.

(** The right map acts on the same inputs in the other nesting order. *)

(** 右映射按另一嵌套次序作用于相同输入。 *)

Definition DayTripleRightMapN
    `{HGH : !HasDay C T G H} `{HGH' : !HasDay C T G' H'}
    `{HR : !HasDay C T F (DayF T G H)}
    `{HR' : !HasDay C T F' (DayF T G' H')}
  : DayF T F (DayF T G H) ⇒ DayF T F' (DayF T G' H')
  := DayMapN T α (DayMapN T β γ).

(** The left map acts componentwise on an identity triple. *)

(** 左映射逐分量作用于恒等三重值。 *)

Lemma day_triple_left_map_gen
    `{HFG : !HasDay C T F G} `{HFG' : !HasDay C T F' G'}
    `{HL : !HasDay C T (DayF T F G) H}
    `{HL' : !HasDay C T (DayF T F' G') H'}
    (A B D : @Ob C) (x : F A) (y : G B) (z : H D)
  : DayTripleLeftMapN (T (T (A,B),D))
      (DayTripleLeftGenN T F G H ((A,B),D) ((x,y),z)) ≈S
      DayTripleLeftGenN T F' G' H' ((A,B),D)
        ((α A x,β B y),γ D z).
Proof.
  transitivity (day_inject T (DayF T F' G') H' (T (A,B),D) id
    (DayMapN T α β (T (A,B)) (day_inject T F G (A,B) id (x,y)),γ D z)).
  - exact (day_map_inject T (DayMapN T α β) γ (T (A,B),D) id
      (day_inject T F G (A,B) id (x,y)) z).
  - exact (@func_proper _ _
      (day_inject T (DayF T F' G') H' (T (A,B),D) id)
      (DayMapN T α β (T (A,B)) (day_inject T F G (A,B) id (x,y)),γ D z)
      (day_inject T F' G' (A,B) id (α A x,β B y),γ D z)
      (day_map_inject T α β (A,B) id x y,reflexivity _)).
Defined.

(** The right map has the same componentwise generator computation. *)

(** 右映射具有同样的逐分量生成元计算。 *)

Lemma day_triple_right_map_gen
    `{HGH : !HasDay C T G H} `{HGH' : !HasDay C T G' H'}
    `{HR : !HasDay C T F (DayF T G H)}
    `{HR' : !HasDay C T F' (DayF T G' H')}
    (A B D : @Ob C) (x : F A) (y : G B) (z : H D)
  : DayTripleRightMapN (T (A,T (B,D)))
      (DayTripleRightGenN T F G H ((A,B),D) ((x,y),z)) ≈S
      DayTripleRightGenN T F' G' H' ((A,B),D)
        ((α A x,β B y),γ D z).
Proof.
  transitivity (day_inject T F' (DayF T G' H') (A,T (B,D)) id
    (α A x,DayMapN T β γ (T (B,D)) (day_inject T G H (B,D) id (y,z)))).
  - exact (day_map_inject T α (DayMapN T β γ) (A,T (B,D)) id
      x (day_inject T G H (B,D) id (y,z))).
  - exact (@func_proper _ _
      (day_inject T F' (DayF T G' H') (A,T (B,D)) id)
      (α A x,DayMapN T β γ (T (B,D)) (day_inject T G H (B,D) id (y,z)))
      (α A x,day_inject T G' H' (B,D) id (β B y,γ D z))
      (reflexivity _,day_map_inject T β γ (B,D) id y z)).
Defined.

End TripleMaps.
