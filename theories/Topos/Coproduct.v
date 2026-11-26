From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Exponential.Functor
  Cat.Exponential.DoubleDual
  Cat.Equalizer
  Cat.EqualizerMorphism
  Cat.Pullback
  Cat.Morphism
  Cat.SubobjectIntersection
  Cat.Limit.Finite
  Cat.Coproduct.Core
  Cat.Coproduct.Finite
  Topos.Sub
  Topos.Representation
  Topos.Conjunction
  Topos.PredicateOrder
  Topos.Disjunction
  Topos.Image
  Topos.Initial.

Import Cats.Cat.Exponential.Core.

(** * Binary Coproducts from Elementary Topos Choices

    Embed both objects in a double power object and classify the join of
    their image predicates. The general double-dual evaluation and the
    classifier's equality test give actual copairs with their universal
    property. Use only the same named finite limits and exponentials. *)

(** * 从初等拓扑斯选择构造二元余积

    将两个对象映入双重幂对象，分类其像谓词的并。一般双对偶求值与分类子的
    相等判据给出实际余配对及其泛性质，仅使用同一具名有限极限与指数。 *)

Section ToposCoproducts.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier HT} `{PB : !HasPullback C}
    `{HP : !HasProduct C} `{HX : !HasExponential HP}.
Let EQ
  : HasEqualizer C
  := @ProductPullbackEqualizer C HP PB.
Local Existing Instance EQ.

(** The equality test is the classifier of the existing equalizer of
    the two product projections, without choosing a new limit. *)

(** 相等测试是既有两个积投影的等化子的分类箭头，不另选极限。 *)

Local Definition coproduct_equality (X : C)
  : Hom (X × X) Ω
  := χ (EqualizerMono (equalizer_universal
      (f := (π1 : Hom (X × X) X)) (g := π2))).

(** Its truth criterion is the original equalizer factor criterion. *)

(** 其为真判据就是原等化子分解判据。 *)

Local Definition coproduct_equality_true {Q X : C} (f g : Hom Q X)
  : coproduct_equality X ∘ ⟨f, g⟩ ≈ truth ∘ ! ↔ f ≈ g.
Proof.
  pose (E := equalizer_universal
    (f := (π1 : Hom (X × X) X)) (g := π2)).
  pose (F := classifier_char_factor (EqualizerMono E) ⟨f, g⟩).
  pose (G := equalizer_factor E ⟨f, g⟩). split.
  - intros H. pose (K := fst G (fst F H)).
    rewrite product_β1, product_β2 in K. exact K.
  - intros H. apply (snd F). apply (snd G).
    rewrite product_β1, product_β2. exact H.
Defined.

(** Singletons are only a local test of double evaluation's monicity. *)

(** 单元素谓词仅用于局部检验双重求值的单态性。 *)

Local Definition coproduct_singleton (X : C)
  : Hom X (Ω ^ X)
  := ƛ (coproduct_equality X).

(** Apply the singleton test by the original currying beta law. *)

(** 用原柯里化 beta 律应用单元素测试。 *)

Local Theorem coproduct_singleton_app {Q X : C} (f g : Hom Q X)
  : app (coproduct_singleton X ∘ f) g
    ≈ coproduct_equality X ∘ ⟨f, g⟩.
Proof.
  unfold coproduct_singleton.
  rewrite <- exp_curry_comp_r, exp_app_β.
  rewrite ?comp_assoc, ?cross_η, ?product_comp_r, ?comp_assoc,
    ?product_β1, ?product_β2, ?comp_id_l, ?comp_id_r.
  reflexivity.
Qed.

(** At the classifier, double-dual evaluation is monic: apply two equal
    evaluations to the same singleton test in their shared context. *)

(** 在分类子处，双对偶求值为单态射：在共同上下文中，将两个相等求值应用于
    同一个单元素测试。 *)

Program Definition ToposDoubleDualMono (X : C)
  : X ↣ (Ω ^ (Ω ^ X))
  :=
  {|mor := ExpDoubleDualUnit Ω X
  |}.
Next Obligation.
  intros Q f g H.
  change (ExpDoubleDualUnit Ω X ∘ f ≈ ExpDoubleDualUnit Ω X ∘ g) in H.
  assert (K : app (ExpDoubleDualUnit Ω X ∘ f) (coproduct_singleton X ∘ g)
    ≈ app (ExpDoubleDualUnit Ω X ∘ g) (coproduct_singleton X ∘ g)).
  { rewrite H. reflexivity. }
  rewrite !exp_double_dual_app, !coproduct_singleton_app in K.
  symmetry. apply (fst (coproduct_equality_true g f)). rewrite K.
  apply (snd (coproduct_equality_true g g)). reflexivity.
Qed.

(** Pairs of predicates give the parameter object for both evaluations. *)

(** 谓词对给出两个求值共同的参数对象。 *)

Definition CoproductPredicates (A B : C)
  : C
  := (Ω ^ A) × (Ω ^ B).

(** Both incoming arrows have this common power object as target. *)

(** 两个进入箭头以此共同幂对象为目标。 *)

Definition CoproductAmbient (A B : C)
  : C
  := Ω ^ CoproductPredicates A B.

(** Evaluate the first predicate on the left object. *)

(** 在左对象上求值第一个谓词。 *)

Definition coproduct_raw_left (A B : C)
  : Hom A (CoproductAmbient A B)
  := exp_dimap
      (π1 : Hom (CoproductPredicates A B) (Ω ^ A))
      (@Cats.Cat.Core.id C Ω) ∘ ExpDoubleDualUnit Ω A.

(** Evaluate the second predicate on the right object. *)

(** 在右对象上求值第二个谓词。 *)

Definition coproduct_raw_right (A B : C)
  : Hom B (CoproductAmbient A B)
  := exp_dimap
      (π2 : Hom (CoproductPredicates A B) (Ω ^ B))
      (@Cats.Cat.Core.id C Ω) ∘ ExpDoubleDualUnit Ω B.

(** Precomposition by a supplied pair sends target predicates to pairs
    of source predicates, using the existing exponential bifunctor. *)

(** 由给定箭头对预合成，将目标谓词送到源谓词对，复用既有指数双函子。 *)

Definition CoproductPredicateMap {A B Z : C} (f : Hom A Z) (g : Hom B Z)
  : Hom (Ω ^ Z) (CoproductPredicates A B)
  := ⟨exp_dimap f (@Cats.Cat.Core.id C Ω),
      exp_dimap g (@Cats.Cat.Core.id C Ω)⟩.

(** Contravariance lifts an arbitrary element of the ambient object to
    the target's double power object. *)

(** 反变性将环境对象的任意元素提升到目标的双重幂对象。 *)

Definition coproduct_lift {A B Z : C} (f : Hom A Z) (g : Hom B Z)
  : Hom (CoproductAmbient A B) (Ω ^ (Ω ^ Z))
  := exp_dimap (CoproductPredicateMap f g) (@Cats.Cat.Core.id C Ω).

(** The lift agrees with target evaluation on the left input. *)

(** 提升在左输入上与目标求值相容。 *)

Theorem coproduct_lift_left {A B Z : C} (f : Hom A Z) (g : Hom B Z)
  : coproduct_lift f g ∘ coproduct_raw_left A B
    ≈ ExpDoubleDualUnit Ω Z ∘ f.
Proof.
  unfold coproduct_lift, coproduct_raw_left.
  rewrite <- comp_assoc.
  pose (H := @exp_dimap_comp C HP HX
    (Ω ^ A) (CoproductPredicates A B) (Ω ^ Z) Ω Ω Ω
    (π1 : Hom (CoproductPredicates A B) (Ω ^ A))
    (CoproductPredicateMap f g) (@Cats.Cat.Core.id C Ω)
    (@Cats.Cat.Core.id C Ω)).
  rewrite <- H, comp_id_l.
  transitivity (exp_dimap
    (exp_dimap f (@Cats.Cat.Core.id C Ω))
    (@Cats.Cat.Core.id C Ω) ∘ ExpDoubleDualUnit Ω A).
  - apply comp_proper; [| reflexivity].
    apply exp_dimap_proper; [| reflexivity].
    exact (@product_β1 C HP (Ω ^ A) (Ω ^ B) (Ω ^ Z)
      (exp_dimap f (@Cats.Cat.Core.id C Ω))
      (exp_dimap g (@Cats.Cat.Core.id C Ω))).
  - apply exp_double_dual_natural.
Qed.

(** The same lift agrees with target evaluation on the right input. *)

(** 同一提升在右输入上与目标求值相容。 *)

Theorem coproduct_lift_right {A B Z : C} (f : Hom A Z) (g : Hom B Z)
  : coproduct_lift f g ∘ coproduct_raw_right A B
    ≈ ExpDoubleDualUnit Ω Z ∘ g.
Proof.
  unfold coproduct_lift, coproduct_raw_right.
  rewrite <- comp_assoc.
  pose (H := @exp_dimap_comp C HP HX
    (Ω ^ B) (CoproductPredicates A B) (Ω ^ Z) Ω Ω Ω
    (π2 : Hom (CoproductPredicates A B) (Ω ^ B))
    (CoproductPredicateMap f g) (@Cats.Cat.Core.id C Ω)
    (@Cats.Cat.Core.id C Ω)).
  rewrite <- H, comp_id_l.
  transitivity (exp_dimap
    (exp_dimap g (@Cats.Cat.Core.id C Ω))
    (@Cats.Cat.Core.id C Ω) ∘ ExpDoubleDualUnit Ω B).
  - apply comp_proper; [| reflexivity].
    apply exp_dimap_proper; [| reflexivity].
    exact (@product_β2 C HP (Ω ^ A) (Ω ^ B) (Ω ^ Z)
      (exp_dimap f (@Cats.Cat.Core.id C Ω))
      (exp_dimap g (@Cats.Cat.Core.id C Ω))).
  - apply exp_double_dual_natural.
Qed.


(** ** The Support of Both Images

    Use the previously constructed image predicates and their existing
    disjunction. Its classified subobject receives both raw evaluations
    and is least among subobjects receiving them. *)

(** ** 两个像的支撑

    使用已构造的像谓词及其既有析取。分类所得子对象接收两侧原求值箭头，
    并在接收它们的子对象中最小。 *)

(** The candidate coproduct is supported by the join of the two images. *)

(** 候选余积由两个像的并支撑。 *)

Definition ToposCoproductSub (A B : C)
  : Sub (CoproductAmbient A B)
  := ClassifiedSub
      ((image_predicate (coproduct_raw_left A B))
        ∨Ω (image_predicate (coproduct_raw_right A B))).

(** Read the ambient object from that selected subobject. *)

(** 从该选定子对象读取环境对象。 *)

Definition ToposCoproduct (A B : C)
  : C
  := sub (ToposCoproductSub A B).

(** The left injection retains the image factor and the disjunction's
    left introduction factor. *)

(** 左注入保留像分解因子与析取的左引入因子。 *)

Definition topos_inl (A B : C)
  : Hom A (ToposCoproduct A B)
  := (predicate_disjunction_left
      (image_predicate (coproduct_raw_left A B))
      (image_predicate (coproduct_raw_right A B))).1
      ∘ topos_image_factor (coproduct_raw_left A B).

(** The right injection uses the same support and right introduction. *)

(** 右注入使用同一支撑及右引入。 *)

Definition topos_inr (A B : C)
  : Hom B (ToposCoproduct A B)
  := (predicate_disjunction_right
      (image_predicate (coproduct_raw_left A B))
      (image_predicate (coproduct_raw_right A B))).1
      ∘ topos_image_factor (coproduct_raw_right A B).

(** Composing the left injection with support recovers raw evaluation. *)

(** 左注入与支撑包含复合后恢复原求值。 *)

Theorem topos_inl_comm (A B : C)
  : ToposCoproductSub A B ∘ topos_inl A B ≈ coproduct_raw_left A B.
Proof.
  pose (H := predicate_disjunction_left
    (image_predicate (coproduct_raw_left A B))
    (image_predicate (coproduct_raw_right A B))).
  change (ToposCoproductSub A B ∘
    (H.1 ∘ topos_image_factor (coproduct_raw_left A B))
      ≈ coproduct_raw_left A B).
  rewrite <- comp_assoc, <- H.2. apply topos_image_factor_comm.
Qed.

(** Composing the right injection with support recovers raw evaluation. *)

(** 右注入与支撑包含复合后恢复原求值。 *)

Theorem topos_inr_comm (A B : C)
  : ToposCoproductSub A B ∘ topos_inr A B ≈ coproduct_raw_right A B.
Proof.
  pose (H := predicate_disjunction_right
    (image_predicate (coproduct_raw_left A B))
    (image_predicate (coproduct_raw_right A B))).
  change (ToposCoproductSub A B ∘
    (H.1 ∘ topos_image_factor (coproduct_raw_right A B))
      ≈ coproduct_raw_right A B).
  rewrite <- comp_assoc, <- H.2. apply topos_image_factor_comm.
Qed.

(** Any subobject containing both raw inputs contains their support.
    The image and disjunction universal properties retain the mediator. *)

(** 包含两侧原输入的任意子对象都包含其支撑；像与析取泛性质保留中介。 *)

Definition topos_coproduct_minimal (A B : C)
    (s : Sub (CoproductAmbient A B))
    (Hl : is_factored_through s (coproduct_raw_left A B))
    (Hr : is_factored_through s (coproduct_raw_right A B))
  : ToposCoproductSub A B ≲Sub s
  := sub_factor_comp
      (snd (predicate_disjunction_universal
        (image_predicate (coproduct_raw_left A B))
        (image_predicate (coproduct_raw_right A B)) (χ (sub_mono _ s)))
        (image_predicate_le (coproduct_raw_left A B) (χ (sub_mono _ s))
          (snd (classifier_char_factor (sub_mono _ s)
            (coproduct_raw_left A B)) Hl),
         image_predicate_le (coproduct_raw_right A B) (χ (sub_mono _ s))
          (snd (classifier_char_factor (sub_mono _ s)
            (coproduct_raw_right A B)) Hr)))
      (fst (classified_char_sub s)).

(** ** Actual Copairing and Its Universal Property

    Lift the supplied arrows into target double evaluation. Both raw
    inputs factor through its monic image, so their support does too.
    Classification retains the resulting actual copair. *)

(** ** 实际余配对及其泛性质

    将给定箭头提升到目标双重求值。两侧原输入均经其单态像分解，故其支撑也
    经此像分解；分类保留所得实际余配对。 *)

(** The lift restricted to support factors through target evaluation. *)

(** 提升限制到支撑后经目标求值分解。 *)

Definition topos_copair_factored {A B Z : C} (f : Hom A Z) (g : Hom B Z)
  : is_factored_through (ToposDoubleDualMono Z)
      (coproduct_lift f g ∘ ToposCoproductSub A B).
Proof.
  pose (m := ToposDoubleDualMono Z).
  pose (r := χ m ∘ coproduct_lift f g).
  assert (Hl : r ∘ coproduct_raw_left A B ≈ truth ∘ !).
  { unfold r. rewrite comp_assoc.
    apply (snd (classifier_char_factor m
      (coproduct_lift f g ∘ coproduct_raw_left A B))).
    exists f. apply coproduct_lift_left. }
  assert (Hr : r ∘ coproduct_raw_right A B ≈ truth ∘ !).
  { unfold r. rewrite comp_assoc.
    apply (snd (classifier_char_factor m
      (coproduct_lift f g ∘ coproduct_raw_right A B))).
    exists g. apply coproduct_lift_right. }
  pose (K := snd (predicate_disjunction_universal
    (image_predicate (coproduct_raw_left A B))
    (image_predicate (coproduct_raw_right A B)) r)
    (image_predicate_le _ r Hl, image_predicate_le _ r Hr)).
  pose (H := fst (predicate_le_truth _ r) K).
  apply (fst (classifier_char_factor m
    (coproduct_lift f g ∘ ToposCoproductSub A B))).
  rewrite <- comp_assoc. exact H.
Defined.

(** Read the copair from that same classifier factor. *)

(** 从同一分类子分解读取余配对。 *)

Definition topos_copair {A B Z : C} (f : Hom A Z) (g : Hom B Z)
  : Hom (ToposCoproduct A B) Z
  := (topos_copair_factored f g).1.

(** Target evaluation detects the retained copair. *)

(** 目标求值检测保留的余配对。 *)

Theorem topos_copair_comm {A B Z : C} (f : Hom A Z) (g : Hom B Z)
  : ToposDoubleDualMono Z ∘ topos_copair f g
    ≈ coproduct_lift f g ∘ ToposCoproductSub A B.
Proof. symmetry. exact (topos_copair_factored f g).2. Qed.

(** The left beta equation follows by cancelling monic evaluation. *)

(** 通过消去单态求值得到左 beta 方程。 *)

Theorem topos_coproduct_β1 {A B Z : C} (f : Hom A Z) (g : Hom B Z)
  : topos_copair f g ∘ topos_inl A B ≈ f.
Proof.
  apply (@mor_mono C Z _ (ToposDoubleDualMono Z) A
    (topos_copair f g ∘ topos_inl A B) f).
  rewrite <- comp_assoc, (topos_copair_comm f g), comp_assoc,
    (topos_inl_comm A B), (coproduct_lift_left f g). reflexivity.
Qed.

(** The right beta equation uses the same monic target evaluation. *)

(** 右 beta 方程使用同一单态目标求值。 *)

Theorem topos_coproduct_β2 {A B Z : C} (f : Hom A Z) (g : Hom B Z)
  : topos_copair f g ∘ topos_inr A B ≈ g.
Proof.
  apply (@mor_mono C Z _ (ToposDoubleDualMono Z) B
    (topos_copair f g ∘ topos_inr A B) g).
  rewrite <- comp_assoc, (topos_copair_comm f g), comp_assoc,
    (topos_inr_comm A B), (coproduct_lift_right f g). reflexivity.
Qed.

(** Support minimality splits an equalizer of maps agreeing on both
    inputs. Its commutativity equation then gives equality of the maps. *)

(** 支撑最小性分裂在两个输入上相等的映射的等化子，其交换方程给出映射相等。 *)

Theorem topos_coproduct_hom_ext {A B Z : C}
    (u v : Hom (ToposCoproduct A B) Z)
    (Hl : u ∘ topos_inl A B ≈ v ∘ topos_inl A B)
    (Hr : u ∘ topos_inr A B ≈ v ∘ topos_inr A B)
  : u ≈ v.
Proof.
  pose (e := @eqι C EQ (ToposCoproduct A B) Z u v).
  pose (E := @equalizer_universal C EQ (ToposCoproduct A B) Z u v).
  pose (s := {|sub := @EqObj C EQ (ToposCoproduct A B) Z u v
             ; sub_mono := Mono_comp (sub_mono _ (ToposCoproductSub A B))
                 (EqualizerMono E)
             |}).
  assert (Hleft : is_factored_through s (coproduct_raw_left A B)).
  { pose (q := @equalize C EQ _ Z A u v (topos_inl A B) Hl).
    exists q. change (coproduct_raw_left A B ≈
      (ToposCoproductSub A B ∘ e) ∘ q).
    rewrite comp_assoc.
    transitivity (ToposCoproductSub A B ∘ topos_inl A B).
    - symmetry. apply topos_inl_comm.
    - apply comp_proper; [reflexivity | symmetry].
      exact (@equalizer_β C EQ _ Z A u v (topos_inl A B) Hl). }
  assert (Hright : is_factored_through s (coproduct_raw_right A B)).
  { pose (q := @equalize C EQ _ Z B u v (topos_inr A B) Hr).
    exists q. change (coproduct_raw_right A B ≈
      (ToposCoproductSub A B ∘ e) ∘ q).
    rewrite comp_assoc.
    transitivity (ToposCoproductSub A B ∘ topos_inr A B).
    - symmetry. apply topos_inr_comm.
    - apply comp_proper; [reflexivity | symmetry].
      exact (@equalizer_β C EQ _ Z B u v (topos_inr A B) Hr). }
  destruct (topos_coproduct_minimal A B s Hleft Hright) as [t Ht].
  assert (Hs : e ∘ t ≈ (@Cats.Cat.Core.id C (ToposCoproduct A B))).
  { apply (@mor_mono C _ _ (sub_mono _ (ToposCoproductSub A B)) _
      (e ∘ t) (@Cats.Cat.Core.id C (ToposCoproduct A B))).
    rewrite <- comp_assoc.
    transitivity (ToposCoproductSub A B :
      Hom (ToposCoproduct A B) (CoproductAmbient A B)).
    - symmetry. exact Ht.
    - symmetry. apply comp_id_r. }
  assert (Hcomm : u ∘ e ≈ v ∘ e) by exact (fst E).
  transitivity (u ∘ (e ∘ t)).
  - rewrite Hs, comp_id_r. reflexivity.
  - rewrite <- comp_assoc, Hcomm, comp_assoc, Hs, comp_id_r. reflexivity.
Qed.

(** The candidate has the original opposite-product coproduct property,
    retaining the constructed copair and its unique mediation. *)

(** 候选满足原反积余积性质，保留构造出的余配对及其唯一中介。 *)

Definition topos_coproduct_universal (A B : C)
  : @is_coproduct C A B (ToposCoproduct A B) (topos_inl A B) (topos_inr A B).
Proof.
  intros Z f g. exists (topos_copair f g). split.
  - split; [exact (topos_coproduct_β1 f g) | exact (topos_coproduct_β2 f g)].
  - intros k [Hk1 Hk2].
    apply (@topos_coproduct_hom_ext A B Z k (topos_copair f g)).
    + rewrite (topos_coproduct_β1 f g). exact Hk1.
    + rewrite (topos_coproduct_β2 f g). exact Hk2.
Defined.

(** Explicitly enable these coproducts through the existing opposite
    product interface. Import does not register any global choice. *)

(** 通过既有反积接口显式启用这些余积；导入不注册全局选择。 *)

Program Definition Topos_HasCoproduct
  : HasCoproduct C
  :=
  {|hasOpProduct :=
      {|Prod A B := ToposCoproduct A B
      ; π1 A B := topos_inl A B
      ; π2 A B := topos_inr A B
      ; product_universal A B := topos_coproduct_universal A B
      |}
  |}.

End ToposCoproducts.

(** ** Finite Discrete Colimits

    Combine the derived initial object with these binary coproducts using
    the existing opposite finite-product construction. No new recursion
    or universal-property proof is introduced here. *)

(** ** 有限离散余极限

    用既有反有限积构造组合推导出的始对象与上述二元余积；此处不另写递归或
    泛性质证明。 *)

Section ToposFiniteCoproducts.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier HT} `{PB : !HasPullback C}
    `{HP : !HasProduct C} `{HX : !HasExponential HP}.

(** Explicitly select all colimits of a finite discrete shape. The empty
    shape uses the derived initial object and successors use the same
    binary coproducts. Importing makes neither choice global. *)

(** 显式选择有限离散形状的全部余极限；空形状用推导的始对象，后继用同一
    二元余积。导入不将任一选择注册为全局实例。 *)

Definition ToposFiniteCoproductColimits (n : nat)
  : HasColimitsOfShape C (DiscreteCat (Fin n))
  := @FiniteCoproductColimits C
      (@Topos_HasInitial C HT HC PB HP HX)
      (@Topos_HasCoproduct C HT HC PB HP HX) n.

End ToposFiniteCoproducts.
