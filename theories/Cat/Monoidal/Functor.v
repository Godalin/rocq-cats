From Cats Require Export
  Cat.Monoidal.Monoidal.

Local Open Scope monoidal_scope.
Local Open Scope ob_scope.

(** * Lax Monoidal Functors

    The unit comparison and tensorator point into the image of the source
    unit and tensor. Neither comparison is required to be invertible.
    Tensorial strength is separate structure, not implied by laxness.
    All coherence laws use the target category's designated equality. *)

(** * Lax Monoidal 函子

    单位比较及 tensorator 指向来源单位及张量的像，不要求任何比较可逆。
    张量强度是独立结构，不由 lax 性推出。全部相干律使用目标范畴的指定相等。 *)

(** A lax structure on the fixed functor [F] selects a unit comparison
    and a natural tensorator for [MC] and [MD]. The three diagrams express
    compatibility with the chosen unitors and associators. *)

(** 固定函子 [F] 上的 lax 结构为 [MC] 和 [MD] 选定单位比较与自然张量子。
    三个交换图表达它们与选定的单位子和结合子的相容性。 *)

Minks.Mixin HasLaxMonoidalF {C D : Cat}
    `{MC : HasMonoidal C} `{MD : HasMonoidal D}
    (F : Fct C D)
  :=
  (** The unit comparison points into the source unit's image. *)

  (** 单位比较指向来源单位对象的像。 *)

  { lax_unit : Hom 𝐈 (F 𝐈)

  (** The tensorator retains its component maps and their naturality. *)

  (** 张量子保留分量映射及其自然性。 *)

  ; lax_tensorN
    : (tensorF ∘F (F ×F F)) ⇒ (F ∘F tensorF)

  (** Left-unit coherence uses the supplied source and target unitors. *)

  (** 左单位相干律使用给定的来源及目标单位子。 *)

  ; lax_unit_l (X : C)
    : fmap F λ[X] ∘ lax_tensorN (𝐈, X)
          ∘ (lax_unit ⊗ id)
        ≈ λ[F X]

  (** Right-unit coherence uses those same named monoidal structures. *)

  (** 右单位相干律使用同一对具名幺半结构。 *)

  ; lax_unit_r (X : C)
    : fmap F ρ[X] ∘ lax_tensorN (X, 𝐈)
          ∘ (id ⊗ lax_unit)
        ≈ ρ[F X]

  (** Associativity coherence retains the selected associators. *)

  (** 结合相干律保留选定的结合子。 *)

  ; lax_assoc (X Y Z : C)
    : fmap F α[X; Y; Z] ∘ lax_tensorN (X ⊗ Y, Z)
          ∘ (lax_tensorN (X, Y) ⊗ id)
        ≈ lax_tensorN (X, Y ⊗ Z) ∘
          (id ⊗ lax_tensorN (Y, Z)) ∘
            α[F X; F Y; F Z]
  }.

Arguments lax_unit {_ _ _ _ _} _.
Arguments lax_tensorN {_ _ _ _ _} _.
Arguments lax_unit_l {_ _ _ _ _} _ _.
Arguments lax_unit_r {_ _ _ _ _} _ _.
Arguments lax_assoc {_ _ _ _ _} _ _ _ _.

(** Bundle the functor with its chosen comparisons and coherence. *)

(** 将函子与选定的比较映射和相干律打包。 *)

Minks.Struct LaxMonoidalFct (C D : Cat)
    `{MC : HasMonoidal C} `{MD : HasMonoidal D}
  extends Fct C D
  with  hasLaxMonoidalF as hasLaxMonoidalF
        : HasLaxMonoidalF [C, D, MC, MD, carrier].

Arguments MakeLaxMonoidalFct {_ _ _ _} _ _.
Arguments LaxMonoidalFctToFct {_ _ _ _} _.
Arguments hasLaxMonoidalF {_ _ _ _} _.

Notation "'φ₀[' L ']'"
  := (lax_unit (hasLaxMonoidalF L))
  (at level 0)
  : monoidal_scope.
Notation "'φ₂[' L ';' X ';' Y ']'"
  := (lax_tensorN (hasLaxMonoidalF L) (X, Y))
  (at level 0)
  : monoidal_scope.

(** Naturality of the tensorator, expressed using the source and target
    tensors of the given lax functor. *)

(** 用给定 lax 函子的来源和目标张量表达张量子的自然性。 *)

Lemma lax_tensor_natural {C D : Cat}
    `{MC : HasMonoidal C} `{MD : HasMonoidal D}
    (L : LaxMonoidalFct C D)
    {X X' Y Y' : C} (f : Hom X X') (g : Hom Y Y')
  : φ₂[L; X'; Y'] ∘ (fmap L f ⊗ fmap L g) ≈
      fmap L (f ⊗ g)%hom ∘ φ₂[L; X; Y].
Proof.
  exact (nat_naturality (lax_tensorN (hasLaxMonoidalF L)) (f, g)).
Qed.

(** The identity tensorator has identity components even though its source
    and target functor records need not be equal. *)

(** 恒等 tensorator 的分量为恒等态射，不要求来源与目标函子记录相等。 *)

Program Definition IdLaxTensorN {C : Cat} `{MC : HasMonoidal C}
  : (tensorF (C := C) ∘F (IdF ×F IdF)) ⇒ (IdF ∘F tensorF)
  :=
  {|nt p := _
  |}.
Next Obligation. destruct p as [X Y]. exact id. Defined.
Next Obligation.
  destruct X as [x y], Y as [x' y'],
    f as [f g]; cbn.
  rewrite comp_id_l, comp_id_r. reflexivity.
Qed.

(** Every monoidal structure gives an explicitly selected lax identity
    functor. Importing this module does not enable a chosen structure. *)

(** 每个幺半结构都给出须显式选择的 lax 恒等函子；导入本模块不会启用选定结构。 *)

Program Definition IdLaxMonoidalF {C : Cat}
    `{MC : HasMonoidal C}
  : LaxMonoidalFct C C
  := MakeLaxMonoidalFct IdF
    {|lax_unit := id
    ; lax_tensorN := IdLaxTensorN
    |}.
Next Obligation.
  rewrite tensor_map_id, !comp_id_r. reflexivity.
Qed.
Next Obligation.
  rewrite tensor_map_id, !comp_id_r. reflexivity.
Qed.
Next Obligation.
  rewrite !tensor_map_id, !comp_id_r, !comp_id_l. reflexivity.
Qed.


(** ** Monoidal Functors

    Here an unqualified monoidal functor means a strong monoidal functor.
    Fix the same named source and target monoidal structures as for lax
    functors. Add chosen inverses to the existing comparisons; their forward
    maps, naturality and coherence are inherited from one lax parent.
    This is distinct from a functor equipped with tensorial strength. *)

(** ** 幺半函子

    本库中不加限定的幺半函子指 strong monoidal functor。固定与 lax 函子
    相同的具名来源及目标幺半结构，为已有比较补充选定的逆；正向映射、自然性
    及相干律均继承自唯一 lax 父结构。这与带张量强度的函子是不同概念。 *)

Minks.Mixin IsStrongMonoidalF {C D : Cat}
    `{MC : HasMonoidal C} `{MD : HasMonoidal D}
    (F : Fct C D)
  extends @HasLaxMonoidalF C D MC MD F
  :=
  (** The unit witness inverts the parent's exact unit comparison. *)

  (** 单位见证为父结构原有的单位比较提供逆。 *)

  { monoidal_unit_iso
    : is_iso (lax_unit (F := F) _)

  (** Tensorator inverses retain Type-valued inverse equations. Their
      naturality follows from the parent's natural transformation. *)

  (** 张量子之逆保留 Type 值互逆方程；其自然性由父结构的自然变换推出。 *)

  ; monoidal_tensor_iso (X Y : C)
    : is_iso (lax_tensorN _ (X, Y))
  }.

Arguments monoidal_unit_iso {_ _ _ _} _ {_ _}.
Arguments monoidal_tensor_iso {_ _ _ _} _ {_ _} _ _.

(** Extend the lax functor by invertibility of its own comparisons. *)

(** 在 lax 函子的两份比较映射上加入可逆性。 *)

Minks.Struct MonoidalFct (C D : Cat)
    `{MC : HasMonoidal C} `{MD : HasMonoidal D}
  extends @LaxMonoidalFct C D MC MD
  with  isStrongMonoidalF
        : IsStrongMonoidalF
          [C, D, MC, MD, carrier, hasLaxMonoidalF].

Arguments MonoidalFctOfLaxMonoidalFct {_ _ _ _} _ _.
Arguments MonoidalFctToLaxMonoidalFct {_ _ _ _} _.

(** The unit isomorphism exposes the stored forward map and inverse. *)

(** 单位同构暴露保存的正向映射及逆。 *)

Definition MonoidalUnitIso {C D : Cat}
    `{MC : HasMonoidal C} `{MD : HasMonoidal D}
    (F : MonoidalFct C D)
  : 𝐈 ≅ F 𝐈
  := (φ₀[F]; monoidal_unit_iso F).

(** The natural isomorphism is a transparent view of the parent's tensorator
    and the supplied component inverses. *)

(** 自然同构是父结构张量子及给定分量之逆的透明视图。 *)

Definition MonoidalTensorIso {C D : Cat}
    `{MC : HasMonoidal C} `{MD : HasMonoidal D}
    (F : MonoidalFct C D)
  : (tensorF ∘F (F ×F F)) ≅N (F ∘F tensorF).
Proof.
  exists (lax_tensorN (hasLaxMonoidalF F)). intros [X Y].
  exact (monoidal_tensor_iso F X Y).
Defined.

(** The inverse tensorator reuses general inverse naturality, without
    requiring another naturality field or any additional coherence. *)

(** 逆张量子复用一般的逆自然性，无须额外的自然性字段或相干要求。 *)

Definition MonoidalTensorInvN {C D : Cat}
    `{MC : HasMonoidal C} `{MD : HasMonoidal D}
    (F : MonoidalFct C D)
  : (F ∘F tensorF) ⇒ (tensorF ∘F (F ×F F))
  := (MonoidalTensorIso F).1 ^-1N (MonoidalTensorIso F).2.

(** The monoidal identity extends the exact lax identity with identity
    inverses; clients select this construction explicitly. *)

(** 幺半恒等函子为原有 lax 恒等函子补充恒等逆；由客户端显式选择此构造。 *)

Program Definition IdMonoidalF {C : Cat} `{MC : HasMonoidal C}
  : MonoidalFct C C
  := MonoidalFctOfLaxMonoidalFct IdLaxMonoidalF
    {|monoidal_unit_iso := _; monoidal_tensor_iso := _|}.
Next Obligation. exists id. split; apply comp_id_l. Defined.
Next Obligation. exists id. split; apply comp_id_l. Defined.
