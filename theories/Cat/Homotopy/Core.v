From Cats Require Export
  Cat.Product.Core
  Cat.Terminal.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.

(** * Elementary Homotopies through a Product Interval

    A homotopy retains an actual map from a product cylinder and its two
    endpoint equations. No reversal, concatenation or equivalence-relation
    law is assumed. Equality between homotopy witnesses compares their
    underlying maps, without comparing endpoint proof fields. *)

(** * 通过积区间的初等同伦

    同伦保留实际的积柱映射及其两个端点方程，不假设反向、拼接或等价关系定律。
    同伦见证之间的相等比较底层映射，不比较端点证明字段。 *)

Section Interval.
Context (C : Cat) `{TC : !HasTerminal C}.

(** An interval is an object with two specified points. It need not have
    an order, a reversal or any chosen filling operation. *)

(** 区间是带有两个指定点的对象，不要求顺序、反向或任何选定填充运算。 *)

Record Interval
  :=
  (** The parameter object supplies the cylinder's second factor. *)

  (** 参数对象给出柱的第二个因子。 *)

  { interval_object : @Ob C
  (** False selects the first point; true selects the second point. *)

  (** false 选取第一个点，true 选取第二个点。 *)

  ; interval_point (b : bool) : Hom (@Term C TC) interval_object
  }.

End Interval.

Arguments interval_object {_ _} _.
Arguments interval_point {_ _} _ _.

(** ** Cylinders and Homotopies

    Fix chosen terminal and binary product structures in [C] and an interval
    [I]. Build the cylinder, its endpoints and homotopies, then study their
    equality and composition operations. *)

(** ** 柱体与同伦

    固定 [C] 的选定终对象、二元积及区间 [I]，构造柱体、端点和同伦，再研究同伦相等及复合操作。 *)

Section Homotopy.
Context {C : Cat} `{TC : !HasTerminal C} `{PC : !HasProduct C}
    (I : Interval C).

(** Fixing the interval factor gives the product-cylinder functor. *)

(** 固定区间因子得到积柱函子。 *)

Definition CylinderF
  : Functor C C
  := (-× (interval_object I)).

(** Each endpoint includes an object into its cylinder. *)

(** 每个端点将对象嵌入其柱。 *)

Program Definition CylinderEndpointN (b : bool)
  : @IdF C ⇒ CylinderF
  :=
  {|nt X := ⟨id, interval_point I b ∘ !⟩
  |}.
Next Obligation.
  change (⟨id, interval_point I b ∘ !⟩ ∘ f ≈
    (f × id) ∘ ⟨id, interval_point I b ∘ !⟩).
  rewrite product_comp_r, product_comp_l, !comp_id_l, comp_id_r,
    comp_assoc, term_comp_l. reflexivity.
Defined.

(** The cylinder projection retracts both endpoint inclusions. *)

(** 柱投影同时回缩两个端点嵌入。 *)

Lemma cylinder_endpoint_projection (b : bool) (X : @Ob C)
  : π1 ∘ CylinderEndpointN b X ≈ id.
Proof. apply product_β1. Defined.

(** A witness has one underlying map and endpoint equations in the
    specified hom equality. No equality of objects or functions is required. *)

(** 见证具有唯一底层映射，端点方程使用指定 Hom 相等，不要求对象或函数相等。 *)

Record Homotopy {X Y : @Ob C} (f g : Hom X Y)
  :=
  (** The unique coercion exposes the actual cylinder map. *)

  (** 唯一强制转换暴露实际柱映射。 *)

  { homotopy_map :> Hom (CylinderF X) Y
  (** Restricting at each endpoint recovers its specified boundary map. *)

  (** 沿每个端点限制，恢复相应的指定边界映射。 *)

  ; homotopy_endpoint (b : bool)
      : homotopy_map ∘ CylinderEndpointN b X ≈ if b then g else f
  }.

Arguments homotopy_map {X Y f g} _.
Arguments homotopy_endpoint {X Y f g} _ _.

(** Homotopy witnesses compare by their maps alone. *)

(** 同伦见证仅按其映射比较。 *)

Definition HomotopyEq {X Y : @Ob C} {f g : Hom X Y}
    (H K : Homotopy f g)
  : Type
  := homotopy_map H ≈ homotopy_map K.

(** Map equality is an equivalence on fixed-boundary homotopy witnesses. *)

(** 映射相等是固定边界同伦见证上的等价关系。 *)

Global Instance HomotopyEq_Equivalence {X Y : @Ob C} {f g : Hom X Y}
  : Equivalence (@HomotopyEq X Y f g).
Proof.
  unfold HomotopyEq. split.
  - intros H. reflexivity.
  - intros H K e. symmetry. exact e.
  - intros H K L e d. transitivity (homotopy_map K); assumption.
Defined.

(** Projection gives a constant homotopy of every map. *)

(** 投影给出每个映射的恒定同伦。 *)

Program Definition ConstantHomotopy {X Y : @Ob C} (f : Hom X Y)
  : Homotopy f f
  :=
  {|homotopy_map := f ∘ π1
  |}.
Next Obligation.
  rewrite comp_assoc, product_β1, comp_id_r.
  destruct b; reflexivity.
Defined.

(** Equal maps give equal constant cylinder maps. Their endpoint expressions
    may differ, so this comparison is stated directly on underlying maps. *)

(** 相等映射给出相等的恒定柱映射。端点表达式可不同，故直接比较底层映射。 *)

Lemma constant_homotopy_map_proper {X Y : @Ob C}
    {f g : Hom X Y} (e : f ≈ g)
  : homotopy_map (ConstantHomotopy f) ≈ homotopy_map (ConstantHomotopy g).
Proof. apply comp_proper; [exact e | reflexivity]. Defined.

(** The interval coordinate is a homotopy between the two constant points. *)

(** 区间坐标给出两个常值端点之间的同伦。 *)

Program Definition IntervalHomotopy (X : @Ob C)
  : Homotopy (interval_point I false ∘ (@term C TC X))
      (interval_point I true ∘ (@term C TC X))
  :=
  {|homotopy_map := π2
  |}.
Next Obligation. rewrite product_β2. destruct b; reflexivity. Defined.

(** Replace the boundary maps by equal ones, keeping the witness map. *)

(** 将边界映射换成相等映射，保留见证映射。 *)

Program Definition HomotopyChangeEndpoints {X Y : @Ob C}
    {f g f' g' : Hom X Y} (H : Homotopy f g)
    (Hf : f ≈ f') (Hg : g ≈ g')
  : Homotopy f' g'
  :=
  {|homotopy_map := homotopy_map H
  |}.
Next Obligation.
  change (homotopy_map H ∘ CylinderEndpointN b X ≈ if b then g' else f').
  rewrite homotopy_endpoint. destruct b; assumption.
Defined.

(** Endpoint replacement respects the fixed-boundary witness comparison. *)

(** 端点替换保持固定边界的见证比较。 *)

Global Instance homotopy_change_endpoints_proper {X Y : @Ob C}
    {f g f' g' : Hom X Y} (Hf : f ≈ f') (Hg : g ≈ g')
  : Proper (@HomotopyEq X Y f g ==> @HomotopyEq X Y f' g')
      (λ H : Homotopy f g, HomotopyChangeEndpoints H Hf Hg).
Proof. intros H K e. exact e. Defined.

(** Precomposition acts through the cylinder functor. *)

(** 预复合通过柱函子作用。 *)

Program Definition PreHomotopy {W X Y : @Ob C} {f g : Hom X Y}
    (H : Homotopy f g) (a : Hom W X)
  : Homotopy (f ∘ a) (g ∘ a)
  :=
  {|homotopy_map := homotopy_map H ∘ fmap CylinderF a
  |}.
Next Obligation.
  change ((homotopy_map H ∘ fmap CylinderF a) ∘ CylinderEndpointN b W ≈
    if b then g ∘ a else f ∘ a).
  rewrite comp_assoc, <- (nt_naturality (CylinderEndpointN b) a),
    <- comp_assoc, homotopy_endpoint. destruct b; reflexivity.
Defined.

(** Postcomposition preserves each endpoint equation. *)

(** 后复合保持每条端点方程。 *)

Program Definition PostHomotopy {X Y Z : @Ob C} {f g : Hom X Y}
    (a : Hom Y Z) (H : Homotopy f g)
  : Homotopy (a ∘ f) (a ∘ g)
  :=
  {|homotopy_map := a ∘ homotopy_map H
  |}.
Next Obligation.
  change ((a ∘ homotopy_map H) ∘ CylinderEndpointN b X ≈
    if b then a ∘ g else a ∘ f).
  rewrite comp_assoc, homotopy_endpoint. destruct b; reflexivity.
Defined.

(** Pairing the witness with its interval coordinate respects endpoints. *)

(** 将见证与其区间坐标配对，保持端点。 *)

Lemma homotopy_graph_endpoint {X Y : @Ob C} {f g : Hom X Y}
    (H : Homotopy f g) (b : bool)
  : ⟨homotopy_map H, π2⟩ ∘ CylinderEndpointN b X ≈
      CylinderEndpointN b Y ∘ (if b then g else f).
Proof.
  rewrite product_comp_r, homotopy_endpoint.
  change (⟨(if b then g else f),
    π2 ∘ ⟨id, interval_point I b ∘ !⟩⟩ ≈
    ⟨id, interval_point I b ∘ !⟩ ∘ (if b then g else f)).
  rewrite product_β2, product_comp_r,
    comp_id_l, comp_assoc, term_comp_l. reflexivity.
Defined.

(** Two homotopies compose horizontally using the same interval coordinate.
    This composes their boundary maps, rather than concatenating paths. *)

(** 两个同伦使用同一区间坐标水平复合，复合的是边界映射，而非路径拼接。 *)

Program Definition CompHomotopy {X Y Z : @Ob C}
    {f g : Hom X Y} {a b : Hom Y Z}
    (K : Homotopy a b) (H : Homotopy f g)
  : Homotopy (a ∘ f) (b ∘ g)
  :=
  {|homotopy_map := homotopy_map K ∘ ⟨homotopy_map H, π2⟩
  |}.
Next Obligation.
  change ((homotopy_map K ∘ ⟨homotopy_map H, π2⟩) ∘
    CylinderEndpointN b0 X ≈ if b0 then b ∘ g else a ∘ f).
  rewrite comp_assoc, (homotopy_graph_endpoint H b0), <- comp_assoc,
    homotopy_endpoint. destruct b0; reflexivity.
Defined.

(** Precomposition respects equality of fixed-boundary homotopy witnesses. *)

(** 预复合保持固定边界同伦见证的相等。 *)

Global Instance pre_homotopy_proper {W X Y : @Ob C} {f g : Hom X Y}
    (a : Hom W X)
  : Proper (@HomotopyEq X Y f g ==>
      @HomotopyEq W Y (f ∘ a) (g ∘ a))
      (λ H : Homotopy f g, PreHomotopy H a).
Proof.
  intros H K e. unfold HomotopyEq; cbn.
  apply comp_proper; [exact e | reflexivity].
Defined.

(** Postcomposition respects the same specified comparisons. *)

(** 后复合保持相同的指定比较。 *)

Global Instance post_homotopy_proper {X Y Z : @Ob C} {f g : Hom X Y}
    (a : Hom Y Z)
  : Proper (@HomotopyEq X Y f g ==>
      @HomotopyEq X Z (a ∘ f) (a ∘ g)) (@PostHomotopy X Y Z f g a).
Proof.
  intros H K d. unfold HomotopyEq; cbn.
  apply comp_proper; [reflexivity | exact d].
Defined.

(** Equal precomposing maps give equal underlying witnesses, even though
    their boundary expressions have different presentations. *)

(** 相等的预复合映射给出相等的底层见证，即使边界表达式具有不同呈现。 *)

Lemma pre_homotopy_map_proper {W X Y : @Ob C} {f g : Hom X Y}
    (H : Homotopy f g) {a a' : Hom W X} (e : a ≈ a')
  : homotopy_map (PreHomotopy H a) ≈ homotopy_map (PreHomotopy H a').
Proof.
  apply comp_proper; [reflexivity | apply functor_fmap_proper; exact e].
Defined.

(** Equal postcomposing maps likewise preserve the underlying comparison. *)

(** 相等的后复合映射同样保持底层比较。 *)

Lemma post_homotopy_map_proper {X Y Z : @Ob C} {f g : Hom X Y}
    (H : Homotopy f g) {a a' : Hom Y Z} (e : a ≈ a')
  : homotopy_map (PostHomotopy a H) ≈ homotopy_map (PostHomotopy a' H).
Proof. apply comp_proper; [exact e | reflexivity]. Defined.

(** Horizontal composition respects equality of both homotopies. *)

(** 水平复合保持两个同伦的相等。 *)

Global Instance comp_homotopy_proper {X Y Z : @Ob C}
    {f g : Hom X Y} {a b : Hom Y Z}
  : Proper (@HomotopyEq Y Z a b ==> @HomotopyEq X Y f g ==>
      @HomotopyEq X Z (a ∘ f) (b ∘ g))
      (@CompHomotopy X Y Z f g a b).
Proof.
  intros K K' e H H' d. unfold HomotopyEq; cbn.
  apply comp_proper; [exact e |]. apply product_pair_proper;
    [exact d | reflexivity].
Defined.

End Homotopy.

Arguments homotopy_map {_ _ _ _ _ _ _ _} _.
Arguments homotopy_endpoint {_ _ _ _ _ _ _ _} _ _.
Arguments HomotopyEq {_ _ _ _ _ _ _ _} _ _.
Arguments HomotopyChangeEndpoints {_ _ _ _ _ _ _ _ _ _} _ _ _.
Arguments PreHomotopy {_ _ _ _ _ _ _ _ _} _ _.
Arguments PostHomotopy {_ _ _ _ _ _ _ _ _} _ _.
Arguments CompHomotopy {_ _ _ _ _ _ _ _ _ _ _} _ _.

Notation "f '∼[' I ']' g" := (Homotopy I f g)
  (at level 70, no associativity) : type_scope.
