From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.Product
  Cat.Diagram.Core
  Cat.Natural
  Cat.Coend.Core
  Instance.Set.Core
  Instance.Set.Product
  Instance.Set.CoendProduct.
From Cats Require Export
  Cat.Day.Universal.

(** * Day Extension with a Fixed Parameter *)

(** * 带固定参数的 Day 延拓 *)

(** A parameter remains an external setoid, rather than an internal
    function object. Selected coends suffice at the original carrier and
    equality levels, with no additional comparison between those levels. *)

(** 参数保持为外部广集，而非内部函数对象。原载体与相等层级上的选定 coend
    已充分，不额外要求这两个层级之间的大小关系。 *)

(** ** Parameterized Binary Operations

    Fix a binary functor, two setoid-valued inputs and a parameter setoid.
    Slice a natural parameterized operation at each parameter, then use the
    integrated product/coend descent to keep that parameter external. *)

(** ** 带参数的二元操作

    固定二元函子、两个广集值输入与参数广集。在每个参数处切片自然操作，
    再复用已集成的积／coend 下降，使参数保持外部形式。 *)

Section ParameterExtension.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C).
Context {F G K : Fct C (SetCat@{u p _ _ _ _ _})} (W : SetC@{u p}).

(** Pair every value of a diagram with the fixed parameter. *)

(** 将图式的每个值与固定参数配对。 *)

Definition DayParameterF {J : Cat} (D : Fct J (SetCat@{u p _ _ _ _ _}))
  : Fct J SetCat
  := @PointwiseProductF J SetCat SetCat_HasProduct D
      (@ConstF J SetCat W).

Context (β : DayParameterF (DayValuesF F G) ⇒ (K ∘F T)).

(** Fixing a parameter recovers an ordinary natural binary operation. *)

(** 固定参数恢复通常的自然二元操作。 *)

Program Definition DayParameterSliceN (w : W)
  : DayValuesF F G ⇒ (K ∘F T)
  :=
  {|nt q := {|func xy := β q (xy,w)|}
  |}.
Next Obligation.
  intros xy xy' H.
  exact (@func_proper _ _ (β q) (xy,w) (xy',w) (H, reflexivity w)).
Defined.
Next Obligation.
  intros xy. exact (nt_naturality β f (xy,w)).
Defined.

(** The weighted cowedges form a respectful family in the parameter. *)

(** 加权余楔组成保持参数相等的族。 *)

Global Instance day_parameter_cowedge_proper (Z : @Ob C)
  : Proper ([≈S] ==> CowedgeEq)
      (λ w, DayExtendCowedge T (DayParameterSliceN w) Z).
Proof.
  intros w w' H q [[h] xy].
  apply (@func_proper _ _ (fmap K h)).
  exact (@func_proper _ _ (β q) (xy,w) (xy,w') (reflexivity xy, H)).
Defined.

Context `{HD : !HasDay C T F G}.

(** Keep the parameter beside the convolution while descending the slices. *)

(** 在切片下降时，将参数保留在卷积旁边。 *)

Definition day_parameter_extend (Z : @Ob C)
  : (DayF T F G Z ×S W) →r K Z
  := coend_parameter_desc
      (λ w, DayExtendCowedge T (DayParameterSliceN w) Z)
      (day_parameter_cowedge_proper Z).

(** The existing natural extensions give naturality in the output object. *)

(** 已有自然延拓给出关于输出对象的自然性。 *)

Program Definition DayParameterExtendN
  : DayParameterF (DayF T F G) ⇒ K
  :=
  {|nt Z := day_parameter_extend Z
  |}.
Next Obligation.
  intros [z w].
  exact (nt_naturality (DayExtendN T (DayParameterSliceN w)) f z).
Defined.

(** Extension evaluates each weighted pair and leaves its parameter fixed. *)

(** 延拓求值每个加权对并保持其参数固定。 *)

Lemma day_parameter_extend_β {Z : @Ob C} (q : @Ob (C ×C C))
    (h : Hom (T q) Z) (xy : DayValuesF F G q) (w : W)
  : DayParameterExtendN Z (day_inject T F G q h xy,w) ≈S
      fmap K h (β q (xy,w)).
Proof.
  exact (day_extend_β T (DayParameterSliceN w) q h xy).
Defined.

End ParameterExtension.

(** ** Distinguishing Parameterized Maps

    Only the indicated convolution and a fixed parameter are assumed.
    The product/coend distinction law reduces equality to weighted Day
    generators, also when the indexing category is larger than the output. *)

(** ** 区分带参数映射

    只假定指定卷积及固定参数。积／coend 区分律将相等归约到加权 Day 生成元；
    即使指标范畴大于输出层级，也保持相同存在条件。 *)

Section ParameterDistinction.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C).
Context (F G : Fct C (SetCat@{u p _ _ _ _ _}))
    `{HD : !HasDay C T F G}.
Context (W : SetC@{u p}) {Z : @Ob C} {E : SetC@{u p}}.

(** A map out of the parameterized convolution is determined on generators. *)

(** 从带参数卷积出发的映射由其在生成元上的值决定。 *)

Lemma day_parameter_hom_ext (f g : (DayF T F G Z ×S W) →r E)
    (H : ∀ q (h : Hom (T q) Z) (xy : DayValuesF F G q) (w : W),
      f (day_inject T F G q h xy,w) ≈S
      g (day_inject T F G q h xy,w))
  : f ≈f g.
Proof.
  apply (@coend_parameter_hom_ext (C ×C C) (DayKernel T F G Z)
    (hasDayCoend Z) W E f g).
  intros q [[h] xy] w. exact (H q h xy w).
Defined.

End ParameterDistinction.

(** ** Uniqueness and Equality of Parameterized Extensions

    Keep only the required chosen convolution. Restriction to identity
    weights determines the natural extension, and pointwise equal input
    operations give pointwise equal results. *)

(** ** 带参数延拓的唯一性及相等

    仍只要求所需的选定卷积。限制到恒等权重即可决定自然延拓；
    逐点相等的输入操作给出逐点相等的结果。 *)

Section ParameterUniqueness.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C).
Context {F G K : Fct C (SetCat@{u p _ _ _ _ _})}
    `{HD : !HasDay C T F G} (W : SetC@{u p}).

(** Identity-generator values uniquely determine a natural transformation. *)

(** 恒等生成元上的值唯一决定自然变换。 *)

Lemma day_parameter_extend_unique
    (β : DayParameterF W (DayValuesF F G) ⇒ (K ∘F T))
    (α : DayParameterF W (DayF T F G) ⇒ K)
    (H : ∀ q (xy : DayValuesF F G q) (w : W),
      α (T q) (day_inject T F G q id xy,w) ≈S β q (xy,w))
  : α ≈N DayParameterExtendN T W β.
Proof.
  intros Z.
  apply (@day_parameter_hom_ext C T F G HD W Z (K Z)).
  intros q h xy w.
  transitivity (fmap K h (α (T q) (day_inject T F G q id xy,w))).
  - transitivity (α Z
      (fmap (DayF T F G) h (day_inject T F G q id xy),w)).
    + apply (@func_proper _ _ (α Z)). split; [| reflexivity].
      transitivity (day_inject T F G q (h ∘ id) xy).
      * apply (@day_inject_proper C T F G HD q Z).
        symmetry. apply comp_id_r.
      * symmetry. exact (day_inject_post T F G q h id xy).
    + exact (nt_naturality α h (day_inject T F G q id xy,w)).
  - transitivity (fmap K h (β q (xy,w))).
    + exact (@func_proper _ _ (fmap K h) _ _ (H q xy w)).
    + symmetry. exact (day_parameter_extend_β T W β q h xy w).
Defined.

(** Pointwise equality of operations is sufficient; law witnesses are ignored. *)

(** 操作逐点相等已充分，不比较定律见证。 *)

Lemma day_parameter_extend_proper
    (β γ : DayParameterF W (DayValuesF F G) ⇒ (K ∘F T))
    (H : β ≈N γ)
  : DayParameterExtendN T W β ≈N DayParameterExtendN T W γ.
Proof.
  intros Z. apply (@day_parameter_hom_ext C T F G HD W Z (K Z)).
  intros q h xy w.
  transitivity (fmap K h (β q (xy,w))).
  - exact (day_parameter_extend_β T W β q h xy w).
  - transitivity (fmap K h (γ q (xy,w))).
    + exact (@func_proper _ _ (fmap K h) _ _ (H q (xy,w))).
    + symmetry. exact (day_parameter_extend_β T W γ q h xy w).
Defined.

End ParameterUniqueness.

(** ** Changing the Parameter and Output

    A respectful parameter map and a natural output comparison transport
    an operation square. Uniqueness transports that same square through
    extension, without forming a setoid of all parameter functions. *)

(** ** 改变参数及输出

    保相等参数映射与自然输出比较运输操作方块；唯一性将同一个方块运输过
    延拓，无需形成包含全部参数函数的内部广集。 *)

Section ParameterChange.
Universes u p.
Context {C : Cat} (T : Fct (C ×C C) C).
Context {F G K L : Fct C (SetCat@{u p _ _ _ _ _})}
    `{HD : !HasDay C T F G}.
Context {W V : SetC@{u p}}
    (β : DayParameterF W (DayValuesF F G) ⇒ (K ∘F T))
    (γ : DayParameterF V (DayValuesF F G) ⇒ (L ∘F T))
    (k : W →r V) (ψ : K ⇒ L).

(** Commuting on binary generators is sufficient for all convolution values. *)

(** 在二元生成元上交换已足以推出全部卷积值上的交换。 *)

Lemma day_parameter_extend_change
    (H : ∀ q (xy : DayValuesF F G q) (w : W),
      γ q (xy,k w) ≈S ψ (T q) (β q (xy,w)))
    (Z : @Ob C) (z : DayF T F G Z) (w : W)
  : DayParameterExtendN T V γ Z (z,k w) ≈S
      ψ Z (DayParameterExtendN T W β Z (z,w)).
Proof.
  pose (α := ψ ∘Nv DayExtendN T (DayParameterSliceN T W β w)).
  assert (HE : α ≈N DayExtendN T (DayParameterSliceN T V γ (k w))).
  { apply (day_extend_unique T (DayParameterSliceN T V γ (k w)) α).
    intros q xy.
    transitivity (ψ (T q) (β q (xy,w))).
    - exact (@func_proper _ _ (ψ (T q)) _ _
        (day_restrict_extend T (DayParameterSliceN T W β w) q xy)).
    - symmetry. exact (H q xy w). }
  symmetry. exact (HE Z z).
Defined.

End ParameterChange.
