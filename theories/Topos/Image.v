From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Exponential.Core
  Cat.Exponential.Context
  Cat.Image
  Cat.Pullback
  Cat.Morphism
  Cat.SubobjectIntersection
  Cat.Limit.Finite
  Topos.Sub
  Topos.Representation
  Topos.Conjunction
  Topos.PredicateOrder
  Topos.Forall.

Import Cats.Cat.Exponential.Core.

(** * Images from Elementary Topos Choices

    Intersect the internal family of predicates containing an arrow.
    Classification retains an actual factor into the resulting least
    subobject. Its minimality and the existing equalizer construction
    prove that this factor is epimorphic, without a choice principle. *)

(** * 从初等拓扑斯选择构造像

    对包含给定箭头的内部谓词族取交；分类保留进入所得最小子对象的实际因子。
    其最小性与既有等化子构造证明此因子为满态射，不使用选择原理。 *)

Section ToposImages.
Context {C : Cat} `{HT : !HasTerminal C}
    `{HC : !HasSubObjClassifier HT} `{PB : !HasPullback C}
    `{HP : !HasProduct C} `{HE : !HasExponential HP}.

(** Evaluate the variable predicate on the supplied arrow's values. *)

(** 在给定箭头的值上求值可变谓词。 *)

Definition image_containing_body {X Y : C} (f : Hom X Y)
  : Hom ((Ω ^ Y) × X) Ω
  := app π1 (f ∘ π2).

(** A predicate contains the arrow when all those evaluations are true. *)

(** 当所有这些求值均为真时，一个谓词包含该箭头。 *)

Definition image_contains {X Y : C} (f : Hom X Y)
  : Hom (Ω ^ Y) Ω
  := ∀Ω[X] (image_containing_body f).

(** The chosen classified family ranges over exactly these predicates. *)

(** 选定的分类族恰在这些谓词上取值。 *)

Definition ImagePredicates {X Y : C} (f : Hom X Y)
  : Sub (Ω ^ Y)
  := ClassifiedSub (image_contains f).

(** Evaluate a member of that family at the variable target element. *)

(** 在可变目标元素处求值该族的一个成员。 *)

Definition image_body {X Y : C} (f : Hom X Y)
  : Hom (Y × ImagePredicates f) Ω
  := app (ImagePredicates f ∘ π2) π1.

(** The image predicate is the intersection over the classified family. *)

(** 像谓词是对该分类族所取的交。 *)

Definition image_predicate {X Y : C} (f : Hom X Y)
  : Hom Y Ω
  := ∀Ω[ImagePredicates f] (image_body f).

(** Members of the classified family satisfy its defining containment. *)

(** 分类族的成员满足其定义中的包含条件。 *)

Theorem image_predicates_true {X Y : C} (f : Hom X Y)
  : image_contains f ∘ ImagePredicates f ≈ truth ∘ !.
Proof.
  exact (fst (predicate_le_truth (image_contains f) (image_contains f))
    (predicate_le_refl (image_contains f))).
Qed.

(** The intersection is true on every value of the original arrow.
    Swap the two product factors and reuse universal quantifier truth. *)

(** 交在原箭头的每个值处为真；交换两个积因子并复用全称量词为真判据。 *)

Theorem image_predicate_factor {X Y : C} (f : Hom X Y)
  : image_predicate f ∘ f ≈ truth ∘ !.
Proof.
  assert (H : image_containing_body f
    ∘ (ImagePredicates f × (@Cats.Cat.Core.id C X))
    ≈ truth ∘ !).
  { apply (fst (forall_predicate_true X _)).
    rewrite <- forall_predicate_comp. apply image_predicates_true. }
  unfold image_predicate. rewrite forall_predicate_comp.
  apply (snd (forall_predicate_true (ImagePredicates f) _)).
  transitivity ((image_containing_body f
      ∘ (ImagePredicates f × (@Cats.Cat.Core.id C X)))
    ∘ ⟨π2, π1⟩).
  - unfold image_body, image_containing_body.
    rewrite !exp_app_comp, !cross_η, !comp_assoc.
    rewrite !product_comp_r, !comp_assoc,
      !product_β1, !product_β2, !comp_id_l. reflexivity.
  - rewrite H, comp_assoc, term_comp_l. reflexivity.
Qed.

(** Any containing predicate's existing exponential name factors through
    the family, retaining the classifier's actual factor. *)

(** 任何包含谓词的既有指数名称均经该族分解，保留分类子的实际因子。 *)

Definition image_predicates_name {X Y : C} (f : Hom X Y)
    (q : Hom Y Ω) (Hq : q ∘ f ≈ truth ∘ !)
  : is_factored_through (ImagePredicates f) (exp_name q).
Proof.
  apply (fst (classifier_char_factor
    (sub_mono _ (ImagePredicates f)) (exp_name q))).
  unfold ImagePredicates. rewrite classified_sub_char.
  unfold image_contains. rewrite forall_predicate_comp.
  apply (snd (forall_predicate_true X _)).
  unfold image_containing_body.
  rewrite exp_app_comp, cross_η, !comp_assoc,
    product_β1, product_β2, comp_id_l, exp_name_app.
  rewrite <- comp_assoc, Hq, comp_assoc, term_comp_l. reflexivity.
Defined.

(** The intersection entails every containing predicate. Instantiate its
    bound family member by the retained factor of the predicate's name. *)

(** 交蕴含每个包含谓词；用其名称所保留的分解因子实例化族成员。 *)

Definition image_predicate_le {X Y : C} (f : Hom X Y)
    (q : Hom Y Ω) (Hq : q ∘ f ≈ truth ∘ !)
  : image_predicate f ⊢Ω q.
Proof.
  destruct (image_predicates_name f q Hq) as [s Hs].
  pose (H := predicate_forall_instantiate (ImagePredicates f)
    (image_body f) (s ∘ !)).
  assert (K : image_body f ∘ ⟨(@Cats.Cat.Core.id C Y), s ∘ !⟩ ≈ q).
  { unfold image_body.
    rewrite exp_app_comp, !comp_assoc, product_β1, product_β2.
    rewrite <- comp_assoc, <- Hs, exp_name_app, comp_id_r.
    reflexivity. }
  exact (sub_factor_comp H (fst (classified_sub_congr K))).
Defined.

(** Classify that intersection as a chosen image subobject. *)

(** 将该交分类为选定的像子对象。 *)

Definition ToposImage {X Y : C} (f : Hom X Y)
  : Sub Y
  := ClassifiedSub (image_predicate f).

(** Classification supplies the original arrow's factor through its image. *)

(** 分类提供原箭头经其像的分解因子。 *)

Definition topos_image_factored {X Y : C} (f : Hom X Y)
  : is_factored_through (ToposImage f) f.
Proof.
  apply (fst (classifier_char_factor (sub_mono _ (ToposImage f)) f)).
  unfold ToposImage. rewrite classified_sub_char. apply image_predicate_factor.
Defined.

(** Read the actual epimorphic factor from that retained witness. *)

(** 从保留的见证读取实际满分解箭头。 *)

Definition topos_image_factor {X Y : C} (f : Hom X Y)
  : Hom X (ToposImage f)
  := (topos_image_factored f).1.

(** The two factors recover the supplied arrow in specified hom equality. *)

(** 两个因子按指定 Hom 相等恢复给定箭头。 *)

Theorem topos_image_factor_comm {X Y : C} (f : Hom X Y)
  : ToposImage f ∘ topos_image_factor f ≈ f.
Proof. symmetry. exact (topos_image_factored f).2. Qed.

(** The image factors through any subobject through which the arrow
    factors. Reuse its characteristic arrow and classification reflection. *)

(** 若箭头经某子对象分解，则像也经它分解；复用特征箭头与分类反射。 *)

Definition topos_image_minimal {X Y : C} (f : Hom X Y) (s : Sub Y)
    (H : is_factored_through s f)
  : ToposImage f ≲Sub s
  := sub_factor_comp
      (image_predicate_le f (χ (sub_mono _ s))
        (snd (classifier_char_factor (sub_mono _ s) f) H))
      (fst (classified_char_sub s)).

(** This Type-valued correspondence is the image's least-subobject
    universal property, preserving factors in both directions. *)

(** 此 Type 值对应是像的最小子对象泛性质，两个方向均保留因子。 *)

Definition topos_image_universal {X Y : C} (f : Hom X Y) (s : Sub Y)
  : ToposImage f ≲Sub s ↔ is_factored_through s f.
Proof.
  split.
  - intros [h Hh]. exists (h ∘ topos_image_factor f).
    rewrite <- comp_assoc, <- Hh. symmetry. apply topos_image_factor_comm.
  - apply topos_image_minimal.
Defined.

(** Retain the mediator into any containing subobject from minimality. *)

(** 从最小性保留进入任意包含子对象的中介。 *)

Definition topos_image_mediator {X Y : C} (f : Hom X Y) (s : Sub Y)
    (H : is_factored_through s f)
  : Hom (ToposImage f) s
  := (topos_image_minimal f s H).1.

(** Monicity gives the full uniqueness property of that same mediator. *)

(** 单态性给出同一中介的完整唯一性性质。 *)

Theorem topos_image_mediator_unique {X Y : C} (f : Hom X Y) (s : Sub Y)
    (H : is_factored_through s f)
  : is_unique (λ h, s ∘ h ≈ (ToposImage f : Hom (ToposImage f) Y))
      (topos_image_mediator f s H).
Proof.
  split.
  - symmetry. exact (topos_image_minimal f s H).2.
  - intros k Hk.
    apply (@mor_mono C s Y (sub_mono _ s) _ k
      (topos_image_mediator f s H)).
    rewrite Hk. exact (topos_image_minimal f s H).2.
Qed.

(** A monomorphism is already its own least containing subobject. *)

(** 单态射自身已是包含它的最小子对象。 *)

Definition topos_image_mono {X Y : C} (m : X ↣ Y)
  : ToposImage m ~Sub {|sub := X; sub_mono := m|}.
Proof.
  split.
  - apply topos_image_minimal. exists (@Cats.Cat.Core.id C X).
    symmetry. apply comp_id_r.
  - exact (topos_image_factored m).
Defined.

(** Equal arrows have equivalent images with retained mutual factors;
    the internally selected predicate families need not be equal objects. *)

(** 相等箭头的像通过保留的相互因子等价，不要求内部选定谓词族是相等对象。 *)

Definition topos_image_eq {X Y : C} {f g : Hom X Y} (H : f ≈ g)
  : ToposImage f ~Sub ToposImage g.
Proof.
  split.
  - apply topos_image_minimal.
    destruct (topos_image_factored g) as [h Hh]. exists h.
    rewrite H. exact Hh.
  - apply topos_image_minimal.
    destruct (topos_image_factored f) as [h Hh]. exists h.
    rewrite <- H. exact Hh.
Defined.

(** The construction satisfies the general candidate image property,
    retaining its factor and every minimality mediator. *)

(** 此构造满足一般候选像性质，保留其分解因子与各最小性中介。 *)

Definition topos_image_is_image {X Y : C} (f : Hom X Y)
  : is_image f (sub_mono _ (ToposImage f))
  := (topos_image_factored f, topos_image_minimal f).

(** The general image theorem proves the factor epimorphic using the
    equalizers already derived from these same products and pullbacks. *)

(** 一般像定理使用由同一积与拉回推导的等化子，证明分解因子为满态射。 *)

Theorem topos_image_factor_epi {X Y : C} (f : Hom X Y)
  : is_epi (topos_image_factor f).
Proof.
  exact (@image_factor_epi C (@ProductPullbackEqualizer C HP PB)
    X Y (ToposImage f) f (sub_mono _ (ToposImage f))
    (topos_image_is_image f) (topos_image_factor f)
    (topos_image_factor_comm f)).
Qed.

End ToposImages.
