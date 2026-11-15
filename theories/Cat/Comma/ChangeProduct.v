From Cats Require Export
  Cat.Comma.Change
  Cat.Comma.Product.

(** * Product Cones under a Change of Comma Diagrams

    An image cone is a product when both endpoint image cones are products
    and the target right functor preserves the right image cone. This is a
    candidate criterion: no global product choice, terminal object or
    invertibility of the natural boundaries is required. Merely having a
    compatible diagram change does not supply the three universal
    properties. *)

(** * 逗号图式变化下的积锥

    当两端像锥为积，且目标右函子保持右侧像锥时，像逗号锥为积。这是候选
    判据，不要求全局选定积、终对象或自然边界可逆。只有相容图式变化本身
    并不能提供这三个泛性质。 *)

(** ** A Supplied Image Cone

    Fix a diagram change with its two oriented natural boundaries, and any
    source cone. Supply the endpoint image properties directly; source
    universality is unnecessary for this recognition theorem. Reuse the
    general comma-cone mediator with the unchanged mapped side arrows. *)

(** ** 给定像锥

    固定图式变化及两条有向自然边界，并取任意源锥。直接给出两端像的泛性质；
    此识别定理无须源泛性质。复用一般逗号锥中介，保留映射后的侧边箭头。 *)

Section CommaChangeProduct.
Context {A B C A' B' C' : Cat}.
Context {F : Fct A C} {G : Fct B C}.
Context {F' : Fct A' C'} {G' : Fct B' C'}.
Context (L : Fct A A') (R : Fct B B') (K : Fct C C').
Context (α : (F' ∘F L) ⇒ (K ∘F F))
    (β : (K ∘F G) ⇒ (G' ∘F R)).
Context {X Y P : @Ob (F ↓C G)} (p : Hom P X) (q : Hom P Y).

(** The mapped cone is recognized without replacing its structural arrow
    or identifying commutativity witnesses. The transparent mediator is
    exactly the pair supplied by the two endpoint image products. *)

(** 识别像锥时不替换结构箭头，也不等同交换性见证。透明中介恰为两个端点
    像积所给出的中介之对。 *)

Definition comma_change_product_cone
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
  := comma_product_cone F' G'
      (fmap (CommaChangeF L R K α β) p)
      (fmap (CommaChangeF L R K α β) q) left right image.

End CommaChangeProduct.
