From Cats Require Import
  Cat.Core
  Cat.Morphism
  Cat.Preorder
  Cat.Terminal
  Cat.Product.Transport
  Cat.Pullback
  Cat.Subobject.

(** * Finite Intersections of Subobjects

    Factorization witnesses form the arrows of the subobject preorder
    category. Its terminal object needs no limit choices; pullbacks supply
    its binary products. Parallel factors are equivalent in this thin
    category, without identifying their data by native equality. *)

(** * 子对象的有限交

    分解见证组成子对象预序范畴的箭头。其终对象不需要极限选择，拉回给出
    二元积。这个薄范畴中平行分解因子等价，不用原生相等识别其数据。 *)

(** Identity factorization retains its arrow transparently. *)

(** 恒等分解透明保留其箭头。 *)

Definition sub_factor_id {C : Cat} {X : @Ob C} (s : Sub X)
  : s ≲Sub s.
Proof. exists id. symmetry. apply comp_id_r. Defined.

(** Compose retained factorization witnesses by composing their arrows. *)

(** 通过复合箭头来复合所保留的分解见证。 *)

Definition sub_factor_comp {C : Cat} {X : @Ob C} {r s t : Sub X}
    (a : r ≲Sub s) (b : s ≲Sub t)
  : r ≲Sub t.
Proof.
  exists (b.1 ∘ a.1).
  rewrite <- comp_assoc, <- b.2. exact a.2.
Defined.

(** An explicit transparent version of the existing preorder: its ordinary
    instance proofs are opaque, so use these witnesses for categorical
    identity and composition without changing that existing interface. *)

(** 显式给出既有预序的透明版本：通常的实例证明不透明，因此范畴的恒等与
    复合使用这些见证，不修改已有接口。 *)

Program Definition SubFactorPreorder {C : Cat} (X : @Ob C)
  : PreOrder (Sub_le X)
  :=
  {|PreOrder_Reflexive := sub_factor_id
  ; PreOrder_Transitive r s t := sub_factor_comp
  |}.

(** The existing Type-valued subobject preorder as a category. *)

(** 将既有的 Type 值子对象预序视为范畴。 *)

Definition SubCat {C : Cat} (X : @Ob C)
  : Cat
  := @PreorderCat _ (Sub_le X) (SubFactorPreorder X).

(** Every subobject factors through the identity subobject. *)

(** 每个子对象都经过恒等子对象分解。 *)

Definition sub_top {C : Cat} {X : @Ob C} (s : Sub X)
  : s ≲Sub id_Sub.
Proof. exists s. simpl. symmetry. apply comp_id_l. Defined.

(** Explicitly choose the largest subobject as terminal; importing this
    module does not enable the choice as a global instance. *)

(** 显式选择最大子对象为终对象；导入本模块不将此选择启用为全局实例。 *)

Program Definition SubCat_HasTerminal {C : Cat} (X : @Ob C)
  : HasTerminal (SubCat X)
  :=
  {|Term := id_Sub
  |}.
Next Obligation.
  intros s. exists (sub_top s). split; [exact I | intros; exact tt].
Defined.

(** The common composite through the first pullback projection is monic. *)

(** 经过第一拉回投影的公共复合是单态射。 *)

Program Definition SubIntersection {C : Cat} `{HP : !HasPullback C}
    {X : @Ob C} (s t : Sub X)
  : Sub X
  :=
  {|sub := Pb s t
  ; sub_mono := Mono_comp (sub_mono _ s)
      (PullbackMono pullback_universal)
  |}.

Infix "∩Sub" := SubIntersection
  (at level 40, left associativity) : cat_scope.

(** ** Binary Intersections from Pullbacks

    Fix only a named pullback choice in [C]. Intersect two displayed
    subobjects by pulling back their monomorphisms. Keep the selected
    pullback object, projections and mediator as computational data. *)

(** ** 由拉回构造二元交

    仅固定 [C] 中具名的拉回选择，将两个展示单态射的拉回作为交。
    保留选定拉回对象、投影与中介作为计算数据。 *)

Section Intersection.
Context {C : Cat} `{HP : !HasPullback C}.

(** The intersection is contained in its first factor. *)

(** 交包含于第一因子。 *)

Definition sub_intersection_left {X} (s t : Sub X)
  : s ∩Sub t ≲Sub s.
Proof. exists (pb1 s t). reflexivity. Defined.

(** The intersection is contained in its second factor. *)

(** 交包含于第二因子。 *)

Definition sub_intersection_right {X} (s t : Sub X)
  : s ∩Sub t ≲Sub t.
Proof. exists (pb2 s t). apply pullback_comm. Defined.

(** An arbitrary arrow factors through the intersection exactly when it
    factors through both subobjects. The reverse map retains the selected
    pullback mediator; the input arrow need not be monic. *)

(** 任意箭头经过交分解，当且仅当它经过两个子对象分解。反向映射保留选定
    拉回中介，不要求输入箭头为单态射。 *)

Definition sub_intersection_factor {X Q} (s t : Sub X) (f : Hom Q X)
  : is_factored_through (s ∩Sub t) f ↔
      is_factored_through s f ∧ is_factored_through t f.
Proof.
  split.
  - intros [k Hk]. split.
    + exists (pb1 s t ∘ k). rewrite <- comp_assoc. exact Hk.
    + exists (pb2 s t ∘ k).
      rewrite <- comp_assoc, <- pullback_comm. exact Hk.
  - intros [[a Ha] [b Hb]].
    assert (Hcone : s ∘ a ≈ t ∘ b).
    { rewrite <- Ha, <- Hb. reflexivity. }
    exists (pb a b Hcone).
    simpl. rewrite comp_assoc, pb_β1. exact Ha.
Defined.

(** The same universal property for subobjects retains both comparison
    factors, rather than truncating the lower-bound witnesses. *)

(** 将同一泛性质用于子对象，保留两个比较因子，不截断下界见证。 *)

Definition sub_intersection_universal {X} (s t r : Sub X)
  : r ≲Sub s ∩Sub t ↔ r ≲Sub s ∧ r ≲Sub t
  := sub_intersection_factor s t r.

(** Binary intersections are chosen products in the existing preorder
    category. This choice also requires explicit enabling by clients. *)

(** 二元交是既有预序范畴的选定积；此选择也由使用者显式启用。 *)

Program Definition SubCat_HasProduct (X : @Ob C)
  : HasProduct (SubCat X)
  :=
  {|Prod := SubIntersection
  ; π1 s t := sub_intersection_left s t
  ; π2 s t := sub_intersection_right s t
  |}.
Next Obligation.
  intros r a b. exists (snd (sub_intersection_universal X0 Y r) (a, b)).
  split; [split; exact tt | intros; exact tt].
Defined.

(** Replacing either representative by an equivalent subobject leaves the
    intersection equivalent, with transparent comparison factors. *)

(** 将任一代表替换为等价子对象，交仍等价，比较因子保持透明。 *)

Global Instance sub_intersection_proper {X}
  : Proper (Sub_eq X ==> Sub_eq X ==> Sub_eq X) SubIntersection.
Proof.
  intros s s' [Hs Hs'] t t' [Ht Ht']. split.
  - apply (snd (sub_intersection_universal s' t' (s ∩Sub t))). split.
    + exact (sub_factor_comp (sub_intersection_left s t) Hs).
    + exact (sub_factor_comp (sub_intersection_right s t) Ht).
  - apply (snd (sub_intersection_universal s t (s' ∩Sub t'))). split.
    + exact (sub_factor_comp (sub_intersection_left s' t') Hs').
    + exact (sub_factor_comp (sub_intersection_right s' t') Ht').
Defined.

(** Commutativity pairs the swapped product projections in the subobject
    category. Use the transparent pairing directly: the existing general
    product-symmetry theorem stores its comparison data opaquely. *)

(** 交换律在子对象范畴中将积投影交换后配对。直接使用透明配对，因为已有
    一般积交换定理不透明地保存比较数据。 *)

Definition sub_intersection_comm {X} (s t : Sub X)
  : s ∩Sub t ~Sub t ∩Sub s.
Proof.
  exact
    (@pair (SubCat X) (SubCat_HasProduct X) t s (s ∩Sub t)
      (sub_intersection_right s t) (sub_intersection_left s t),
     @pair (SubCat X) (SubCat_HasProduct X) s t (t ∩Sub s)
      (sub_intersection_right t s) (sub_intersection_left t s)).
Defined.

(** Associativity reuses the general product associator, retaining its two
    factorization witnesses. *)

(** 结合律复用一般积的结合同构，保留其两个分解见证。 *)

Definition sub_intersection_assoc {X} (r s t : Sub X)
  : (r ∩Sub s) ∩Sub t ~Sub r ∩Sub (s ∩Sub t).
Proof.
  pose (i := @product_assoc (SubCat X) (SubCat_HasProduct X) r s t).
  exact (i.1, i.2.1).
Defined.

(** Repeating the same subobject does not change its intersection class. *)

(** 同一子对象重复相交不改变其等价类。 *)

Definition sub_intersection_idem {X} (s : Sub X)
  : s ∩Sub s ~Sub s.
Proof.
  split; [apply sub_intersection_left |].
  apply (snd (sub_intersection_universal s s s)).
  split; apply sub_factor_id.
Defined.

(** The largest subobject is the neutral element of binary intersection. *)

(** 最大子对象是二元交的中性元。 *)

Definition sub_intersection_top {X} (s : Sub X)
  : s ∩Sub id_Sub ~Sub s.
Proof.
  split; [apply sub_intersection_left |].
  apply (snd (sub_intersection_universal s id_Sub s)).
  split; [apply sub_factor_id | apply sub_top].
Defined.

End Intersection.
