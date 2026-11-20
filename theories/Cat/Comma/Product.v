From Cats Require Export
  Cat.Comma.Core
  Cat.Product.Transport.

(** * Binary Products in Comma Categories

    Products in both endpoint categories lift when the right functor
    preserves the supplied right product cone. The left functor is
    arbitrary. The common target category needs no chosen products.
    Prove the candidate universal property once, then package selected
    products separately. All square and mediator witnesses are retained. *)

(** * 逗号范畴中的二元积

    当右函子保持给定右积锥时，两端范畴中的积提升为逗号范畴中的积。左函子
    任意，共同目标范畴不需要选定积。先一次证明候选泛性质，再单独打包选定
    积。全部方形及中介见证均予保留。 *)

(** ** Recognizing a Supplied Comma Cone

    Fix an arbitrary commuting cone in the comma category. Its endpoint
    cones must be products, and the right functor must preserve this right
    cone. The cone need not be the chosen or constructed comma product.
    Its structure arrow and square witnesses are kept as supplied. *)

(** ** 识别给定逗号锥

    固定逗号范畴中任意给定的交换锥。两端锥须为积，且右函子须保持此右锥。
    不要求它是选定或构造出的逗号积；原结构箭头与方形见证均予保留。 *)

Section SuppliedCommaProduct.
Context {A B C : Cat} (F : Fct A C) (G : Fct B C).
Context {X Y P : @Ob (F ↓C G)} (p : Hom P X) (q : Hom P Y).

(** Endpoint mediators form a square by image-product extensionality.
    Endpoint uniqueness proves comma uniqueness without comparing square
    witnesses. No chosen products or terminal objects are required. *)

(** 由像积的外延性，两端中介组成方形；两端唯一性给出逗号唯一性，无须比较
    方形见证。不要求选定积或终对象。 *)

Definition comma_product_cone
    (left : is_product (comma_left_ob X) (comma_left_ob Y)
      (comma_left_ob P) (comma_left p) (comma_left q))
    (right : is_product (comma_right_ob X) (comma_right_ob Y)
      (comma_right_ob P) (comma_right p) (comma_right q))
    (image : is_product (G (comma_right_ob X)) (G (comma_right_ob Y))
      (G (comma_right_ob P)) (fmap G (comma_right p))
      (fmap G (comma_right q)))
  : @is_product (F ↓C G) X Y P p q.
Proof.
  intros Z f g.
  destruct (left (comma_left_ob Z) (comma_left f) (comma_left g))
    as [l [[l1 l2] lu]].
  destruct (right (comma_right_ob Z) (comma_right f) (comma_right g))
    as [r [[r1 r2] ru]].
  assert (square : fmap G r ∘ comma_arrow Z ≈
      comma_arrow P ∘ fmap F l).
  { apply (product_cone_ext image).
    - rewrite <- comp_assoc, <- fmap_comp, r1, (comma_comm f).
      rewrite <- comp_assoc, (comma_comm p).
      rewrite comp_assoc, <- fmap_comp, l1. reflexivity.
    - rewrite <- comp_assoc, <- fmap_comp, r2, (comma_comm g).
      rewrite <- comp_assoc, (comma_comm q).
      rewrite comp_assoc, <- fmap_comp, l2. reflexivity. }
  unshelve refine (existT _
    {|comma_left := _
    ; comma_right := _
    ; comma_comm := _
    |} _).
  - exact l.
  - exact r.
  - exact square.
  - refine {|this := _
           ; that := _
           |}.
    + exact ((l1, r1), (l2, r2)).
    + intros k [[k1 h1] [k2 h2]]. split; cbn in *.
      * apply lu. exact (k1, k2).
      * apply ru. exact (h1, h2).
Defined.

End SuppliedCommaProduct.

(** ** A Pair of Candidate Product Cones

    Fix two comma objects, a cone on each endpoint pair and preservation
    of the right cone. Its image universal property constructs the glued
    structure arrow and proves the commuting projection squares. *)

(** ** 两个候选积锥

    固定两个逗号对象、两端对象对上的锥，以及右锥的保持性。像锥的泛性质
    构造粘合结构箭头，并证明投影方形交换。 *)

Section CommaProduct.
Context {A B C : Cat} (F : Fct A C) (G : Fct B C).
Context (X Y : @Ob (F ↓C G)).
Context (P : @Ob A) (Q : @Ob B).
Context (p1 : Hom P (comma_left_ob X)) (p2 : Hom P (comma_left_ob Y)).
Context (q1 : Hom Q (comma_right_ob X)) (q2 : Hom Q (comma_right_ob Y)).
Context (image : is_product (G (comma_right_ob X)) (G (comma_right_ob Y))
    (G Q) (fmap G q1) (fmap G q2)).

(** The preserved right cone receives the two structure composites. *)

(** 保持后的右锥接受两条结构复合。 *)

Definition comma_product_arrow
  : Hom (F P) (G Q)
  := (image (F P) (comma_arrow X ∘ fmap F p1)
      (comma_arrow Y ∘ fmap F p2)).1.

(** The underlying object is the pair of supplied cone vertices. *)

(** 底层对象为给定的两个锥顶点。 *)

Program Definition CommaProduct
  : @Ob (F ↓C G)
  :=
  {|comma_left_ob := P
  ; comma_right_ob := Q
  ; comma_arrow := comma_product_arrow
  |}.

(** The first image-product equation is the first commuting square. *)

(** 像积的第一方程就是第一个交换方形。 *)

Program Definition comma_product_π1
  : (@Hom (F ↓C G)) CommaProduct X
  :=
  {|comma_left := p1
  ; comma_right := q1
  |}.
Next Obligation.
  exact (fst (this
    (image (F P) (comma_arrow X ∘ fmap F p1)
      (comma_arrow Y ∘ fmap F p2)).2)).
Defined.

(** The second image-product equation supplies the other square. *)

(** 像积的第二方程提供另一个交换方形。 *)

Program Definition comma_product_π2
  : (@Hom (F ↓C G)) CommaProduct Y
  :=
  {|comma_left := p2
  ; comma_right := q2
  |}.
Next Obligation.
  exact (snd (this
    (image (F P) (comma_arrow X ∘ fmap F p1)
      (comma_arrow Y ∘ fmap F p2)).2)).
Defined.

(** The supplied-cone theorem applies to these constructed projections.
    Its mediator is still the original pair of endpoint mediators. *)

(** 给定锥定理适用于这些构造出的投影；中介仍为原来的两端中介之对。 *)

Definition comma_product_universal
    (left : is_product (comma_left_ob X) (comma_left_ob Y) P p1 p2)
    (right : is_product (comma_right_ob X) (comma_right_ob Y) Q q1 q2)
  : @is_product (F ↓C G) X Y CommaProduct
      comma_product_π1 comma_product_π2.
Proof.
  exact (comma_product_cone F G comma_product_π1 comma_product_π2
    left right image).
Defined.

End CommaProduct.

(** ** Explicitly Chosen Comma Products

    Assume chosen products only in the endpoint categories and supplied
    preservation of the chosen right cones. This wrapper specializes the
    candidate theorem, with no extra terminal or target-product choice. *)

(** ** 显式选定的逗号积

    只假设两端范畴具有选定积，并给出右侧选定锥的保持性。此包装专门化候选
    定理，不额外选择终对象或目标积。 *)

Section ChosenCommaProducts.
Context {A B C : Cat} (F : Fct A C) (G : Fct B C).
Context `{PA : !HasProduct A} `{PB : !HasProduct B}.
Context (preserves : ∀ X Y : @Ob B,
    is_product (G X) (G Y) (G ((X × Y)%ob)) (fmap G π1) (fmap G π2)).

(** Chosen products reuse the same candidate and universal mediator. *)

(** 选定积复用同一候选及泛中介。 *)

Program Definition Comma_HasProduct
  : HasProduct (F ↓C G)
  :=
  {|Prod X Y := CommaProduct F G X Y
      ((comma_left_ob X × comma_left_ob Y)%ob)
      ((comma_right_ob X × comma_right_ob Y)%ob) π1 π2 π1 π2
      (preserves _ _)
  ; π1 X Y := comma_product_π1 F G X Y _ _ π1 π2 π1 π2 (preserves _ _)
  ; π2 X Y := comma_product_π2 F G X Y _ _ π1 π2 π1 π2 (preserves _ _)
  |}.
Next Obligation.
  apply comma_product_universal; apply product_universal.
Defined.

End ChosenCommaProducts.
