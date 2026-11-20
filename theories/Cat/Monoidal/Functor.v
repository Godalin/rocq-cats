From Cats Require Export
  Cat.Monoidal.Monoidal.

Local Open Scope monoidal_scope.

(** * Lax Monoidal Functors

    The unit comparison and tensorator point into the image of the source
    unit and tensor. Neither comparison is required to be invertible.
    Tensorial strength is separate structure, not implied by laxness.
    All coherence laws use the target category's designated equality. *)

(** * Lax Monoidal 函子

    单位比较及 tensorator 指向来源单位及张量的像，不要求任何比较可逆。
    张量强度是独立结构，不由 lax 性推出。全部相干律使用目标范畴的指定相等。 *)

(** A functor bundled with a lax structure, relative to the named monoidal
    structures [MC] and [MD]. Its unique coercion exposes the underlying
    functor, so clients can write [L X] and [fmap L f]. A natural
    transformation supplies the tensorator's naturality in both arguments.
    The three remaining
    diagrams retain the chosen associators and unitors explicitly.
    [MonoidalFct] below additionally requires invertible comparisons;
    an oplax structure reverses both comparison maps. *)

(** 函子及其相对于具名幺半结构 [MC]、[MD] 的 lax 结构打包在一起；唯一的
    强制转换暴露底层函子，客户端可写 [L X]、[fmap L f]。
    自然变换提供 tensorator 在两个变量上的自然性，另外三幅交换图显式保留
    选定的结合子及单位子。下文的 [MonoidalFct] 还要求比较可逆；
    oplax 结构则将两个比较映射反向。 *)

Record LaxMonoidalFct {C D : Cat}
    (MC : HasMonoidal C) (MD : HasMonoidal D)
  := LaxMonoidalFctOfFct

  (** Store the supplied functor once as the unique underlying view. *)

  (** 将给定函子保存一次，作为唯一底层视图。 *)

  { LaxMonoidalFctToFct :> Fct C D

  (** The unit comparison points into the source unit's image. *)

  (** 单位比较指向来源单位对象的像。 *)

  ; lax_unit : Hom (𝐈[MD]) (LaxMonoidalFctToFct (𝐈[MC]))

  (** The tensorator retains its component maps and their naturality. *)

  (** 张量子保留分量映射及其自然性。 *)

  ; lax_tensorN
    : (tensorF (isMagmoidal MD) ∘F
        (LaxMonoidalFctToFct ×F LaxMonoidalFctToFct)) ⇒
      (LaxMonoidalFctToFct ∘F tensorF (isMagmoidal MC))

  (** Left-unit coherence uses the supplied source and target unitors. *)

  (** 左单位相干律使用给定的来源及目标单位子。 *)

  ; lax_unit_l (X : @Ob C)
    : fmap LaxMonoidalFctToFct (tensor_unitor_l (HasUnitors := MC) X).1 ∘
        lax_tensorN (𝐈[MC], X) ∘
        (tensor_map (IM := isMagmoidal MD) lax_unit id) ≈
        (tensor_unitor_l (HasUnitors := MD)
          (LaxMonoidalFctToFct X)).1

  (** Right-unit coherence uses those same named monoidal structures. *)

  (** 右单位相干律使用同一对具名幺半结构。 *)

  ; lax_unit_r (X : @Ob C)
    : fmap LaxMonoidalFctToFct (tensor_unitor_r (HasUnitors := MC) X).1 ∘
        lax_tensorN (X, 𝐈[MC]) ∘
        (tensor_map (IM := isMagmoidal MD) id lax_unit) ≈
        (tensor_unitor_r (HasUnitors := MD)
          (LaxMonoidalFctToFct X)).1

  (** Associativity coherence retains the selected associators. *)

  (** 结合相干律保留选定的结合子。 *)

  ; lax_assoc (X Y Z : @Ob C)
    : fmap LaxMonoidalFctToFct (tensor_assoc (HasAssoc := MC) X Y Z).1 ∘
        lax_tensorN (tensor (HasBinoidal := MC) X Y, Z) ∘
        (tensor_map (IM := isMagmoidal MD) (lax_tensorN (X, Y)) id) ≈
        lax_tensorN (X, tensor (HasBinoidal := MC) Y Z) ∘
        (tensor_map (IM := isMagmoidal MD) id (lax_tensorN (Y, Z))) ∘
        (tensor_assoc (HasAssoc := MD)
          (LaxMonoidalFctToFct X) (LaxMonoidalFctToFct Y)
          (LaxMonoidalFctToFct Z)).1
  }.

(** The direct constructor keeps the supplied functor, comparisons and
    coherence witnesses; no chosen lax structure is enabled by import. *)

(** 直接构造器保留给定函子、比较及相干见证；导入不启用选定 lax 结构。 *)

Arguments LaxMonoidalFctOfFct {_ _ _ _} _ _ _ _ _ _.
Arguments LaxMonoidalFctToFct {_ _ _ _} _.
Arguments lax_unit {_ _ _ _} _.
Arguments lax_tensorN {_ _ _ _} _.
Arguments lax_unit_l {_ _ _ _} _ _.
Arguments lax_unit_r {_ _ _ _} _ _.
Arguments lax_assoc {_ _ _ _} _ _ _ _.

Notation "'φ₀[' L ']'" := (lax_unit L) : monoidal_scope.
Notation "'φ₂[' L ';' X ';' Y ']'" := (lax_tensorN L (X, Y))
  : monoidal_scope.

(** Naturality of the tensorator as an operation-level rewrite. Explicit
    structures avoid ambiguity when [C] and [D] coincide. *)

(** 将 tensorator 的自然性写为运算层面的重写律；显式结构避免 [C] 与 [D]
    相同时的歧义。 *)

Lemma lax_tensor_natural {C D : Cat}
    {MC : HasMonoidal C} {MD : HasMonoidal D}
    (L : LaxMonoidalFct MC MD)
    {X X' Y Y' : @Ob C} (f : Hom X X') (g : Hom Y Y')
  : φ₂[L; X'; Y'] ∘ (tensor_map (IM := isMagmoidal MD) (fmap L f) (fmap L g)) ≈
      fmap L (tensor_map (IM := isMagmoidal MC) f g) ∘ φ₂[L; X; Y].
Proof.
  exact (nat_naturality (lax_tensorN L)
    (X := (X, Y)) (Y := (X', Y')) (f, g)).
Qed.

(** The identity tensorator has identity components even though its source
    and target functor records need not be equal. *)

(** 恒等 tensorator 的分量为恒等态射，不要求来源与目标函子记录相等。 *)

Program Definition IdLaxTensorN {C : Cat} (MC : HasMonoidal C)
  : (tensorF (isMagmoidal MC) ∘F (IdF ×F IdF)) ⇒ (IdF ∘F tensorF (isMagmoidal MC))
  :=
  {|nt p := _
  |}.
Next Obligation. destruct p as [X Y]. exact id. Defined.
Next Obligation.
  destruct X as [x y], Y as [x' y'], f as [f g]; cbn.
  rewrite comp_id_l, comp_id_r. reflexivity.
Qed.

(** Every monoidal structure gives an explicitly selected lax identity
    functor. Importing this module does not enable a chosen structure. *)

(** 每个幺半结构都给出须显式选择的 lax 恒等函子；导入本模块不会启用选定结构。 *)

Program Definition IdLaxMonoidalF {C : Cat}
    (MC : HasMonoidal C)
  : LaxMonoidalFct MC MC
  :=
  {|LaxMonoidalFctToFct := IdF
  ; lax_unit := id
  ; lax_tensorN := IdLaxTensorN MC
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

Record MonoidalFct {C D : Cat}
    (MC : HasMonoidal C) (MD : HasMonoidal D)
  := MonoidalFctOfLaxMonoidalFct

  (** Inherit the functor and both comparisons through this single parent. *)

  (** 通过唯一父结构继承函子及两个比较。 *)

  { MonoidalFctToLaxMonoidalFct :> LaxMonoidalFct MC MD

  (** The unit witness inverts the parent's exact unit comparison. *)

  (** 单位见证为父结构原有的单位比较提供逆。 *)

  ; monoidal_unit_iso : is_iso φ₀[MonoidalFctToLaxMonoidalFct]

  (** Tensorator inverses retain Type-valued inverse equations. Their
      naturality follows from the parent's natural transformation. *)

  (** 张量子之逆保留 Type 值互逆方程；其自然性由父结构的自然变换推出。 *)

  ; monoidal_tensor_iso (X Y : @Ob C)
    : is_iso φ₂[MonoidalFctToLaxMonoidalFct; X; Y]
  }.

Arguments MonoidalFctOfLaxMonoidalFct {_ _ _ _} _ _ _.
Arguments MonoidalFctToLaxMonoidalFct {_ _ _ _} _.
Arguments monoidal_unit_iso {_ _ _ _} _.
Arguments monoidal_tensor_iso {_ _ _ _} _ _ _.

(** The unit isomorphism exposes the stored forward map and inverse. *)

(** 单位同构暴露保存的正向映射及逆。 *)

Definition MonoidalUnitIso {C D : Cat}
    {MC : HasMonoidal C} {MD : HasMonoidal D} (F : MonoidalFct MC MD)
  : 𝐈[MD] ≅ F (𝐈[MC])
  := (φ₀[F]; monoidal_unit_iso F).

(** The natural isomorphism is a transparent view of the parent's tensorator
    and the supplied component inverses. *)

(** 自然同构是父结构张量子及给定分量之逆的透明视图。 *)

Definition MonoidalTensorIso {C D : Cat}
    {MC : HasMonoidal C} {MD : HasMonoidal D} (F : MonoidalFct MC MD)
  : (tensorF (isMagmoidal MD) ∘F (F ×F F)) ≅N (F ∘F tensorF (isMagmoidal MC)).
Proof.
  exists (lax_tensorN F). intros [X Y].
  exact (monoidal_tensor_iso F X Y).
Defined.

(** The inverse tensorator reuses general inverse naturality, without
    requiring another naturality field or any additional coherence. *)

(** 逆张量子复用一般的逆自然性，无须额外的自然性字段或相干要求。 *)

Definition MonoidalTensorInvN {C D : Cat}
    {MC : HasMonoidal C} {MD : HasMonoidal D} (F : MonoidalFct MC MD)
  : (F ∘F tensorF (isMagmoidal MC)) ⇒ (tensorF (isMagmoidal MD) ∘F (F ×F F))
  := (MonoidalTensorIso F).1 ^-1N (MonoidalTensorIso F).2.

(** The monoidal identity extends the exact lax identity with identity
    inverses; clients select this construction explicitly. *)

(** 幺半恒等函子为原有 lax 恒等函子补充恒等逆；由客户端显式选择此构造。 *)

Program Definition IdMonoidalF {C : Cat} (MC : HasMonoidal C)
  : MonoidalFct MC MC
  :=
  {|MonoidalFctToLaxMonoidalFct := IdLaxMonoidalF MC
  |}.
Next Obligation. exists id. split; apply comp_id_l. Defined.
Next Obligation. exists id. split; apply comp_id_l. Defined.
