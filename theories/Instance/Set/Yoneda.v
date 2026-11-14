From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Hom
  Instance.Set.Lift.

(** * Representable Set-Valued Functors and the Yoneda Lemma *)

(** * 可表集合值函子与 Yoneda 引理 *)

(** ** Representable Functor *)

(** ** 可表函子 *)

(** A representation is a natural isomorphism from the covariant hom functor. *)

(** 表示是从协变 Hom 函子出发的自然同构。 *)

Definition represents {C : Cat} (F : Fct C SetCat) (X : @Ob C)
  := Hom( X ,-) ≅N F.

Notation "X '⦂' 'Rep' F" := (represents F X)
  (at level 50, no associativity, format "X  ⦂  Rep  F") : cat_scope.

(** Retain a representing object and its natural isomorphism. *)

(** 保留表示对象及其自然同构。 *)

Definition is_representable {C : Cat} (F : Fct C SetCat)
  := ∃ X, X ⦂ Rep F.

(** A covariant hom functor is represented by its source object. *)

(** 协变 Hom 函子由其源对象表示。 *)

Proposition represents_self {C : Cat} {X : @Ob C}
  : X ⦂ Rep Hom(X,-).
Proof. exists idN. intros Y. exists id. cato. Defined.



(** ** Yoneda Lemma *)

(** ** Yoneda 引理 *)

(** The setoid of natural transformations with pointwise component equality. *)

(** 以逐点分量相等比较自然变换的广集。 *)

Program Canonical Nat_SetS {C D : Cat}
  (F G : Fct C D)
  :=
  {|carrier := F ⇒ G
  ; carrier_equiv := NatEq
  |} .

(** ** The Covariant Yoneda Correspondence

    Fix [F : Fct C SetCat]. Evaluation at the identity and the functor
    action give inverse respectful maps, yielding the Yoneda isomorphism. *)

(** ** 协变 Yoneda 对应

    固定 [F : Fct C SetCat]，由恒等态射处的求值及函子作用构造互逆的保相等映射，得到 Yoneda 同构。 *)

Section Yoneda.
Context {C : Cat}.
Context {F : Fct C SetCat}.

(** Evaluate a natural transformation from a representable at the identity. *)

(** 在恒等处求值从可表函子出发的自然变换。 *)

Program Canonical yoneda_func {X}
  : (Hom(X,-) ⇒ F) →r F X
  :=
  {|func α := α X id
  |}.
Next Obligation. intros a a' Ha.
  pose (HaX := Ha X id). cato.
Qed.

(** Send an element to the transformation obtained by applying the functor to
    arrows. *)

(** 将元素送到通过函子作用于箭头得到的自然变换。 *)

Program Canonical yoneda_func_inv {X}
  : F X →r (Hom(X,-) ⇒ F)
  :=
  {|func (x : F X) :=
     {|nt Y :=
    {|func f :=
  (fmap F f) x
    |}
     |}
  |}.
Next Obligation.
  intros f f' Hf.
  assert (H : fmap F f ≈ fmap F f').
  { rewrite Hf. cato. }
  specialize (H x). cato.
Qed.
Next Obligation. intros g.
  assert (H : fmap F (f ∘ g) ≈ fmap F f ∘ fmap F g).
  { rewrite functor_comp. cato. }
  specialize (H x). cato.
Qed.
Next Obligation.
  intros a a' Ha Y. simpl.
  intros f. simpl in f.
  exact (@func_proper _ _ (fmap F f) a a' Ha).
Qed.

(** Reconstruction from identity evaluation recovers the natural
    transformation. *)

(** 由恒等处求值重构后恢复原自然变换。 *)

Theorem yoneda_func_inv_func {X : @Ob C} (α : Hom(X,-) ⇒ F)
  : yoneda_func_inv (yoneda_func α) ≈N α.
Proof.
  intros Y f.
  exact (transitivity (symmetry (nt_naturality α f id))
    (@func_proper _ _ (α Y) (f ∘ id) f (comp_id_r f))).
Defined.

(** Evaluating the reconstructed transformation recovers the original element. *)

(** 求值重构的自然变换后恢复原元素。 *)

Theorem yoneda_func_func_inv {X : @Ob C} (x : F X)
  : yoneda_func (yoneda_func_inv x) ≈S x.
Proof. exact (functor_id C SetCat F x). Defined.

(** Natural transformations can be larger than values of F. Lift both sets
    into a common ambient category without identifying their native sizes. *)

(** 自然变换的大小可能超过 F 的值；把两个广集提升到共同环境范畴，不等同它们原
    有的大小。 *)

Definition yoneda_lemma_iso@{n e +} {X : @Ob C}
  : LiftS@{_ _ n e} (Nat_SetS Hom(X,-) F) ≅[SetCat] LiftS@{_ _ n e} (F X).
Proof.
  exists (yoneda_func^↑S), (yoneda_func_inv^↑S). split.
  - intros [α]. refine {|lower := _
                       |}. apply yoneda_func_inv_func.
  - intros [x]. refine {|lower := _
                       |}. apply yoneda_func_func_inv.
Defined.

End Yoneda.

(** Yoneda evaluation commutes with a transformation of the target functor. *)

(** Yoneda 求值与目标函子的自然变换交换。 *)

Theorem yoneda_func_natural_functor {C : Cat} {F G : Fct C SetCat}
    {X : @Ob C}
    (β : F ⇒ G) (α : Hom(X,-) ⇒ F)
  : yoneda_func (β ∘Nv α) ≈S β X (yoneda_func α).
Proof. reflexivity. Qed.

(** Yoneda evaluation is natural in the representing object. *)

(** Yoneda 求值在表示对象上自然。 *)

Theorem yoneda_func_natural_object {C : Cat} {F : Fct C SetCat}
    {X Y : @Ob C} (f : Hom X Y)
    (α : Hom(X,-) ⇒ F)
  : yoneda_func (α ∘Nv f ^*N) ≈S fmap F f (yoneda_func α).
Proof.
  pose proof (nt_naturality α f) as Hα.
  specialize (Hα id). simpl in Hα. rewrite comp_id_r in Hα.
  simpl. rewrite comp_id_l. exact Hα.
Qed.

(** ** Presheaf Yoneda Correspondence *)

(** ** 预层的 Yoneda 对应 *)

Section PresheafYoneda.
Universes u p.
Context {C : Cat} {P : Fct (C^op) SetCat@{u p _ _ _ _ _}}.

(** Evaluate at the lifted identity. Raising the representable to P's value
    universes allows small domains with larger values; both levels of P
    remain independent of the hom-setoid's native sizes. *)

(** 在提升的恒等处求值。将可表函子提升到 P 的值宇宙，允许小定义域上的较大值；
    P 的两个层级均保持独立于原 Hom 广集的大小。 *)

Program Definition presheaf_yoneda_resp {X : @Ob C}
  : Nat_SetS (LiftF ∘F Hom(-,X)) P →r P X
  :=
  {|func α := α X {|lower := id
                 |}
  |}.
Next Obligation. intros α β H. apply H. Defined.

(** The inverse applies P to the underlying arrow. This is the opposite
    Yoneda construction with explicit size wrappers. *)

(** 逆映射将 P 作用于底层箭头；这是带显式大小包装的反范畴 Yoneda 构造。 *)

Program Definition presheaf_yoneda_inv_resp {X : @Ob C}
  : P X →r Nat_SetS (LiftF ∘F Hom(-,X)) P
  :=
  {|func x :=
    {|nt Y :=
      {|func f := fmap P (lower f) x
      |}
    |}
  |}.
Next Obligation.
  intros [f] [g] [H]. exact (functor_fmap_proper _ _ P _ _ H x).
Defined.
Next Obligation.
  intros [g]. exact (functor_comp _ _ P f g x).
Defined.
Next Obligation.
  intros x y H Y [f]. exact (@func_proper _ _ (fmap P f) x y H).
Defined.

(** Reconstruction after evaluation recovers every transformation. *)

(** 求值后重构恢复每个变换。 *)

Lemma presheaf_yoneda_η {X : @Ob C}
    (α : (LiftF ∘F Hom(-,X)) ⇒ P)
  : presheaf_yoneda_inv_resp (presheaf_yoneda_resp α) ≈N α.
Proof.
  intros Y [f].
  transitivity (α Y {|lower := id ∘ f
                    |}).
  - symmetry. exact (nt_naturality α f {|lower := id
                                       |}).
  - apply func_proper. exact {|lower := comp_id_l f
                             |}.
Defined.

(** Evaluation after reconstruction recovers the element. *)

(** 重构后求值恢复原元素。 *)

Lemma presheaf_yoneda_β {X : @Ob C} (x : P X)
  : presheaf_yoneda_resp (presheaf_yoneda_inv_resp x) ≈S x.
Proof. exact (functor_id _ _ P x). Defined.

(** Package the correspondence as an isomorphism at a common ambient size,
    keeping the native transformation and element universes independent. *)

(** 在共同环境大小中将对应组织为同构，保持变换与元素原有宇宙的独立性。 *)

Definition presheaf_yoneda_iso@{n e +} {X : @Ob C}
  : LiftS@{_ _ n e} (Nat_SetS (LiftF ∘F Hom(-,X)) P) ≅[SetCat]
      LiftS@{_ _ n e} (P X).
Proof.
  exists (presheaf_yoneda_resp^↑S), (presheaf_yoneda_inv_resp^↑S).
  split.
  - intros [α]. refine {|lower := _
                       |}. apply presheaf_yoneda_η.
  - intros [x]. refine {|lower := _
                       |}. apply presheaf_yoneda_β.
Defined.

End PresheafYoneda.

(** Evaluation commutes with maps of presheaves. *)

(** 求值与预层映射交换。 *)

Lemma presheaf_yoneda_natural_presheaf@{u p +} {C : Cat}
    {P Q : Fct (C^op) SetCat@{u p _ _ _ _ _}} {X : @Ob C}
    (β : P ⇒ Q) (α : (LiftF ∘F Hom(-,X)) ⇒ P)
  : presheaf_yoneda_resp (C := C) (P := Q) (X := X) (β ∘Nv α) ≈S
      β X (presheaf_yoneda_resp (C := C) (P := P) (X := X) α).
Proof. reflexivity. Qed.

(** Evaluation is contravariantly natural in the representing object. *)

(** 求值在表示对象上反变自然。 *)

Lemma presheaf_yoneda_natural_object@{u p +} {C : Cat}
    {P : Fct (C^op) SetCat@{u p _ _ _ _ _}} {X Y : @Ob C}
    (f : Hom X Y) (α : (LiftF ∘F Hom(-,Y)) ⇒ P)
  : presheaf_yoneda_resp (C := C) (P := P) (X := X)
      (α ∘Nv (LiftF ∘Nl f _*N)) ≈S
      fmap P f (presheaf_yoneda_resp (C := C) (P := P) (X := Y) α).
Proof.
  change (α X {|lower := f ∘ id
              |} ≈S fmap P f (α Y {|lower := id
                                   |})).
  transitivity (α X {|lower := f
                    |}).
  - apply func_proper. exact {|lower := comp_id_r f
                             |}.
  - transitivity (α X {|lower := id ∘ f
                      |}).
    + apply func_proper. exact {|lower := symmetry (comp_id_l f)
                               |}.
    + exact (nt_naturality α f {|lower := id
                               |}).
Qed.
