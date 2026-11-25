From Cats Require Import
  Cat.Comma.ChangeProduct
  Cat.Diagram.Core
  Cat.Morphism
  Instance.Set.Core
  Instance.Set.Initial
  Instance.Set.Product
  Instance.Set.Terminal.
From CatsGluingTests Require Import
  Gluing.

(** * Supplied Comma Products and Their Images

    Opposite strict profiles keep all six category boundaries separate.
    A supplied tagged cone has a different structural computation from
    the selected product. Its mediator and a change with an empty incoming
    boundary still compute without inspecting square witnesses. *)

(** * 给定逗号积及其像

    相反严格配置分离全部六个范畴边界。给定标签锥的结构计算不同于选定积，
    但其中介及入边界为空的变化仍无需检查方形见证即可计算。 *)

(** ** Independent Native Bounds

    Supply arbitrary cones and only their endpoint/image properties.
    Neither terminal nor globally chosen product structures are assumed. *)

(** ** 独立原生边界

    给出任意锥及其端点／像性质，不假设终对象或全局选定积结构。 *)

Section IndependentProductCone.
Universes o0 h0 e0 l0 o1 h1 e1 l1 o2 h2 e2 l2
  o3 h3 e3 l3 o4 h4 e4 l4 o5 h5 e5 l5.
Constraint h0 < e0, e0 < o0, o0 < l0.
Constraint e1 < h1, h1 < o1, o1 < l1.
Constraint h2 < e2, e2 < o2, o2 < l2.
Constraint e3 < h3, h3 < o3, o3 < l3.
Constraint h4 < e4, e4 < o4, o4 < l4.
Constraint e5 < h5, h5 < o5, o5 < l5.
Constraint l0 < o1, l1 < o2, l2 < o3, l3 < o4, l4 < o5.
Context {A : Cat@{o0 h0 e0 l0 l0}}.
Context {B : Cat@{o1 h1 e1 l1 l1}}.
Context {C : Cat@{o2 h2 e2 l2 l2}}.
Context {A' : Cat@{o3 h3 e3 l3 l3}}.
Context {B' : Cat@{o4 h4 e4 l4 l4}}.
Context {C' : Cat@{o5 h5 e5 l5 l5}}.
Context (F : Fct A C) (G : Fct B C).
Context {F' : Fct A' C'} {G' : Fct B' C'}.
Context (L : Fct A A') (R : Fct B B') (K : Fct C C').
Context (α : (F' ∘F L) ⇒ (K ∘F F))
    (β : (K ∘F G) ⇒ (G' ∘F R)).
Context {X Y P : @Ob (F ↓C G)} (p : Hom P X) (q : Hom P Y).

(** The supplied candidate accepts the original native levels. *)

(** 给定候选接受原有原生层级。 *)

Definition independent_comma_product_cone
    (left : is_product (comma_left_ob X) (comma_left_ob Y)
      (comma_left_ob P) (comma_left p) (comma_left q))
    (right : is_product (comma_right_ob X) (comma_right_ob Y)
      (comma_right_ob P) (comma_right p) (comma_right q))
    (image : is_product (G (comma_right_ob X)) (G (comma_right_ob Y))
      (G (comma_right_ob P)) (fmap G (comma_right p))
      (fmap G (comma_right q)))
  : @is_product (F ↓C G) X Y P p q
  := comma_product_cone F G p q left right image.

(** The image criterion retains all six category boundaries. *)

(** 像判据保留全部六个范畴边界。 *)

Definition independent_comma_change_product_cone
    (left : is_product (L (comma_left_ob X)) (L (comma_left_ob Y))
      (L (comma_left_ob P)) (fmap L (comma_left p))
      (fmap L (comma_left q)))
    (right : is_product (R (comma_right_ob X)) (R (comma_right_ob Y))
      (R (comma_right_ob P)) (fmap R (comma_right p))
      (fmap R (comma_right q)))
    (image : is_product (G' (R (comma_right_ob X)))
      (G' (R (comma_right_ob Y))) (G' (R (comma_right_ob P)))
      (fmap G' (fmap R (comma_right p)))
      (fmap G' (fmap R (comma_right q))))
  : @is_product (F' ↓C G')
      (CommaChangeF L R K α β X) (CommaChangeF L R K α β Y)
      (CommaChangeF L R K α β P)
      (fmap (CommaChangeF L R K α β) p)
      (fmap (CommaChangeF L R K α β) q)
  := comma_change_product_cone L R K α β p q left right image.

End IndependentProductCone.

(** ** Reversed Native Bounds

    Supply arbitrary cones and only their endpoint/image properties.
    Neither terminal nor globally chosen product structures are assumed. *)

(** ** 反向原生边界

    给出任意锥及其端点／像性质，不假设终对象或全局选定积结构。 *)

Section ReversedProductCone.
Universes o0 h0 e0 l0 o1 h1 e1 l1 o2 h2 e2 l2
  o3 h3 e3 l3 o4 h4 e4 l4 o5 h5 e5 l5.
Constraint e0 < h0, h0 < o0, o0 < l0.
Constraint h1 < e1, e1 < o1, o1 < l1.
Constraint e2 < h2, h2 < o2, o2 < l2.
Constraint h3 < e3, e3 < o3, o3 < l3.
Constraint e4 < h4, h4 < o4, o4 < l4.
Constraint h5 < e5, e5 < o5, o5 < l5.
Constraint l5 < o4, l4 < o3, l3 < o2, l2 < o1, l1 < o0.
Context {A : Cat@{o0 h0 e0 l0 l0}}.
Context {B : Cat@{o1 h1 e1 l1 l1}}.
Context {C : Cat@{o2 h2 e2 l2 l2}}.
Context {A' : Cat@{o3 h3 e3 l3 l3}}.
Context {B' : Cat@{o4 h4 e4 l4 l4}}.
Context {C' : Cat@{o5 h5 e5 l5 l5}}.
Context (F : Fct A C) (G : Fct B C).
Context {F' : Fct A' C'} {G' : Fct B' C'}.
Context (L : Fct A A') (R : Fct B B') (K : Fct C C').
Context (α : (F' ∘F L) ⇒ (K ∘F F))
    (β : (K ∘F G) ⇒ (G' ∘F R)).
Context {X Y P : @Ob (F ↓C G)} (p : Hom P X) (q : Hom P Y).

(** The supplied candidate accepts the original native levels. *)

(** 给定候选接受原有原生层级。 *)

Definition reversed_comma_product_cone
    (left : is_product (comma_left_ob X) (comma_left_ob Y)
      (comma_left_ob P) (comma_left p) (comma_left q))
    (right : is_product (comma_right_ob X) (comma_right_ob Y)
      (comma_right_ob P) (comma_right p) (comma_right q))
    (image : is_product (G (comma_right_ob X)) (G (comma_right_ob Y))
      (G (comma_right_ob P)) (fmap G (comma_right p))
      (fmap G (comma_right q)))
  : @is_product (F ↓C G) X Y P p q
  := comma_product_cone F G p q left right image.

(** The image criterion retains all six category boundaries. *)

(** 像判据保留全部六个范畴边界。 *)

Definition reversed_comma_change_product_cone
    (left : is_product (L (comma_left_ob X)) (L (comma_left_ob Y))
      (L (comma_left_ob P)) (fmap L (comma_left p))
      (fmap L (comma_left q)))
    (right : is_product (R (comma_right_ob X)) (R (comma_right_ob Y))
      (R (comma_right_ob P)) (fmap R (comma_right p))
      (fmap R (comma_right q)))
    (image : is_product (G' (R (comma_right_ob X)))
      (G' (R (comma_right_ob Y))) (G' (R (comma_right_ob P)))
      (fmap G' (fmap R (comma_right p)))
      (fmap G' (fmap R (comma_right q))))
  : @is_product (F' ↓C G')
      (CommaChangeF L R K α β X) (CommaChangeF L R K α β Y)
      (CommaChangeF L R K α β P)
      (fmap (CommaChangeF L R K α β) p)
      (fmap (CommaChangeF L R K α β) q)
  := comma_change_product_cone L R K α β p q left right image.

End ReversedProductCone.

(** Importing candidate theorems does not select comma products. *)

(** 导入候选定理不会选取逗号积。 *)

Fail Definition automatic_comma_products
  : HasProduct ((@IdF SetCat) ↓C IdF)
  := ltac:(typeclasses eauto).

(** ** A Noncanonical Structural Arrow

    Choose setoid products locally. The supplied comma cone flips both
    ignored Boolean tags in its structural arrow. Its projections retain
    distinct Boolean square tokens; no native record equality is needed. *)

(** ** 非规范结构箭头

    局部选择广集积。给定逗号锥的结构箭头翻转两个被忽略的布尔标签；两个
    投影保留不同的布尔方形标记，不要求记录原生相等。 *)

Section TaggedCone.
Local Instance cone_set_products
  : HasProduct SetCat
  := SetCat_HasProduct.

(** Keep a supplied structure that changes both ignored tags. *)

(** 保留改变两个被忽略标签的给定结构。 *)

Program Definition SuppliedTaggedProduct
  : (@IdF SetCat) ↓C IdF
  :=
  {|comma_left_ob := (TaggedGluingS × TaggedGluingS)%ob
  ; comma_right_ob := (TaggedGluingS × TaggedGluingS)%ob
  ; comma_arrow := ⟨gluing_toggle ∘r π1, gluing_toggle ∘r π2⟩
  |}.

(** The first projection carries a true commutativity token. *)

(** 第一投影携带真的交换性标记。 *)

Program Definition supplied_tagged_π1
  : Hom SuppliedTaggedProduct TaggedGluingObj
  :=
  {|comma_left := π1
  ; comma_right := π1
  |}.
Next Obligation. intros [[n b] [m c]]. exact (eq_refl, true). Defined.

(** The second projection independently carries a false token. *)

(** 第二投影独立携带假的标记。 *)

Program Definition supplied_tagged_π2
  : Hom SuppliedTaggedProduct TaggedGluingObj
  :=
  {|comma_left := π2
  ; comma_right := π2
  |}.
Next Obligation. intros [[n b] [m c]]. exact (eq_refl, false). Defined.

(** Only endpoint products and the identity image property are used. *)

(** 只使用端点积和恒等函子的像性质。 *)

Definition supplied_tagged_product
  : @is_product ((@IdF SetCat) ↓C IdF)
      TaggedGluingObj TaggedGluingObj SuppliedTaggedProduct
      supplied_tagged_π1 supplied_tagged_π2
  := comma_product_cone IdF IdF supplied_tagged_π1 supplied_tagged_π2
      product_universal product_universal product_universal.

(** The new mediator pairs the actual endpoint inputs. *)

(** 新中介对实际端点输入配对。 *)

Definition supplied_tagged_pair
  : Hom TaggedGluingObj SuppliedTaggedProduct
  := (supplied_tagged_product TaggedGluingObj tagged_gluing_toggle id).1.

(** The supplied structural computation is retained verbatim. *)

(** 给定结构的计算逐字保留。 *)

Example supplied_structure_computes
  : comma_arrow SuppliedTaggedProduct ((3, false), (4, true)) =
      ((3, true), (4, false)).
Proof. reflexivity. Defined.

(** Computing the left mediator does not inspect the arbitrary square. *)

(** 计算左中介不检查任意方形。 *)

Example supplied_left_mediator_computes
  : comma_left supplied_tagged_pair (3, false) =
      ((3, true), (3, false)).
Proof. reflexivity. Defined.

(** The right mediator likewise retains the supplied input tag. *)

(** 右中介同样保留给定输入标签。 *)

Example supplied_right_mediator_computes
  : comma_right supplied_tagged_pair (4, true) =
      ((4, false), (4, true)).
Proof. reflexivity. Defined.

(** Both stored square witnesses are observable Type-valued data. *)

(** 两个保存的方形见证均为可观察的 Type 值数据。 *)

Example supplied_square_tokens_compute
  : (snd (comma_comm supplied_tagged_π1 ((3, false), (4, true))),
      snd (comma_comm supplied_tagged_π2 ((3, false), (4, true)))) =
      (true, false).
Proof. reflexivity. Defined.

(** The mediator respects the designated equality on the input square,
    despite the native difference in Boolean tags. *)

(** 中介保持输入方形的指定相等，尽管布尔标签原生不同。 *)

Example supplied_pair_respects
  : supplied_tagged_pair ≈
      (supplied_tagged_product TaggedGluingObj id id).1.
Proof.
  split; change (@HomEq SetCat _ _ ⟨gluing_toggle, id⟩ ⟨id, id⟩);
    apply product_pair_proper;
    [exact (fst tagged_gluing_toggle_equal) | reflexivity |
     exact (snd tagged_gluing_toggle_equal) | reflexivity].
Defined.

(** ** A Noninvertible Incoming Boundary

    Change the left identity interpretation to the constant empty one.
    The target right functor is still identity and preserves the supplied
    cone. The incoming boundary has no inverse, but products survive. *)

(** ** 不可逆的入边界

    将左恒等解释改为空的常解释。目标右函子仍为恒等并保持给定锥；入边界
    没有逆，但积仍得到保持。 *)

(** The empty source supplies the boundary without a global choice. *)

(** 空源提供此边界，无须全局选择。 *)

Program Definition EmptyIncomingN
  : (@CompF SetCat SetCat SetCat
        (ConstF SetCat EmptyS) (@IdF SetCat)) ⇒
      (@CompF SetCat SetCat SetCat (@IdF SetCat) (@IdF SetCat))
  :=
  {|nt X := {|func x := match x with end
             |}
  |}.
Next Obligation. intros x. destruct x. Defined.
Next Obligation. intros x. destruct x. Defined.

(** Its component at unit cannot have an inverse into the empty setoid. *)

(** 单位处的分量不可能有取值于空广集的逆。 *)

Definition empty_incoming_not_iso
  : is_iso (EmptyIncomingN UnitS) → Empty_set.
Proof. intro H. exact (H.1 tt). Defined.

(** Reuse the general image-cone criterion with this noninvertible input. *)

(** 在此不可逆输入下复用一般像锥判据。 *)

Definition empty_changed_product
  : @is_product ((ConstF SetCat EmptyS) ↓C (@IdF SetCat))
      (CommaChangeF IdF IdF IdF EmptyIncomingN
        (CommaChangeIdRightN IdF) TaggedGluingObj)
      (CommaChangeF IdF IdF IdF EmptyIncomingN
        (CommaChangeIdRightN IdF) TaggedGluingObj)
      (CommaChangeF IdF IdF IdF EmptyIncomingN
        (CommaChangeIdRightN IdF) SuppliedTaggedProduct)
      (fmap (CommaChangeF IdF IdF IdF EmptyIncomingN
        (CommaChangeIdRightN IdF)) supplied_tagged_π1)
      (fmap (CommaChangeF IdF IdF IdF EmptyIncomingN
        (CommaChangeIdRightN IdF)) supplied_tagged_π2)
  := comma_change_product_cone IdF IdF IdF EmptyIncomingN
      (CommaChangeIdRightN IdF) supplied_tagged_π1 supplied_tagged_π2
      product_universal product_universal product_universal.

(** The changed mediator still pairs both mapped side arrows. *)

(** 变化后中介仍对两条映射后的侧边配对。 *)

Example empty_changed_mediator_computes
  : comma_left (empty_changed_product _
      (fmap (CommaChangeF IdF IdF IdF EmptyIncomingN
        (CommaChangeIdRightN IdF)) tagged_gluing_toggle)
      (fmap (CommaChangeF IdF IdF IdF EmptyIncomingN
        (CommaChangeIdRightN IdF)) id)).1 (3, false) =
      ((3, true), (3, false)).
Proof. reflexivity. Defined.

(** The changed right mediator keeps the independent right input value. *)

(** 变化后右中介保留独立的右侧输入值。 *)

Example empty_changed_right_mediator_computes
  : comma_right (empty_changed_product _
      (fmap (CommaChangeF IdF IdF IdF EmptyIncomingN
        (CommaChangeIdRightN IdF)) tagged_gluing_toggle)
      (fmap (CommaChangeF IdF IdF IdF EmptyIncomingN
        (CommaChangeIdRightN IdF)) id)).1 (4, true) =
      ((4, false), (4, true)).
Proof. reflexivity. Defined.

End TaggedCone.
