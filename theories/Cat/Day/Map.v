From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Functor.Product
  Cat.Natural
  Cat.Coend.Core
  Instance.Set.Core
  Instance.Set.Product.
From Cats Require Export
  Cat.Day.Core.

(** * Natural Maps of Day Convolutions *)

(** * Day 卷积的自然映射 *)

(** Transform the two value coordinates while retaining the Hom weight.
    This uses the existing pointwise product of natural transformations. *)

(** 在保留 Hom 权重的同时变换两个值坐标；此处使用已有的自然变换逐点积。 *)

Definition DayInputN@{u p +} {C : Cat} (T : Functor (C ×C C) C)
    {F F' G G' : Functor C (SetCat@{u p _ _ _ _ _})} (α : F ⇒ F') (β : G ⇒ G')
    (Z : @Ob C)
  : DayKernel T F G Z ⇒ DayKernel T F' G' Z
  := @PointwiseProductN _ SetCat SetCat_HasProduct _ _ _ _ idN
      ((@PointwiseProductN _ SetCat SetCat_HasProduct _ _ _ _
        (α ∘Nr FstF C C) (β ∘Nr SndF C C))
        ∘Nr SndF ((C ×C C)^op) (C ×C C)).

(** ** Kernel Map Laws

    Fix a binary functor. Input transformations preserve identities and
    composition, and commute with changes of the output parameter. *)

(** ** 核映射定律

    固定二元函子，输入变换保持恒等与复合，并与输出参数的改变交换。 *)

Section InputLaws.
Universes u p.
Context {C : Cat} (T : Functor (C ×C C) C).

(** Equal input transformations give equal maps of kernels. *)

(** 相等的输入自然变换给出相等的核映射。 *)

Global Instance day_input_proper {F F' G G' : Functor C (SetCat@{u p _ _ _ _ _})}
    (Z : @Ob C)
  : Proper (NatEq ==> NatEq ==> NatEq)
      (λ (α : F ⇒ F') (β : G ⇒ G'), DayInputN T α β Z).
Proof.
  intros α α' H β β' K [[X Y] [X' Y']] [h [x y]].
  split; [reflexivity | split; [exact (H X' x) | exact (K Y' y)]].
Defined.

(** Identity input maps act identically on every coordinate. *)

(** 输入恒等映射在每个坐标上恒等作用。 *)

Lemma day_input_id (F G : Functor C (SetCat@{u p _ _ _ _ _})) (Z : @Ob C)
  : DayInputN T (idN (F := F)) (idN (F := G)) Z ≈N idN.
Proof. intros [[X Y] [X' Y']] [h [x y]]. repeat split; reflexivity. Defined.

(** Input composition agrees with vertical composition of kernel maps. *)

(** 输入复合与核映射的垂直复合一致。 *)

Lemma day_input_comp {F F' F'' G G' G'' : Functor C (SetCat@{u p _ _ _ _ _})}
    (α' : F' ⇒ F'') (α : F ⇒ F')
    (β' : G' ⇒ G'') (β : G ⇒ G') (Z : @Ob C)
  : DayInputN T (α' ∘Nv α) (β' ∘Nv β) Z ≈N
      (DayInputN T α' β' Z ∘Nv DayInputN T α β Z).
Proof. intros [[X Y] [X' Y']] [h [x y]]. repeat split; reflexivity. Defined.

(** Independent changes of values and Hom targets commute. *)

(** 值与 Hom 目标的独立改变彼此交换。 *)

Lemma day_input_post {F F' G G' : Functor C (SetCat@{u p _ _ _ _ _})}
    (α : F ⇒ F') (β : G ⇒ G') {Z Z' : @Ob C} (f : Hom Z Z')
  : (DayInputN T α β Z' ∘Nv DayPostN T f) ≈N
      (DayPostN T f ∘Nv DayInputN T α β Z).
Proof. intros [[X Y] [X' Y']] [h [x y]]. repeat split; reflexivity. Defined.

End InputLaws.

(** Only the two endpoint convolution choices are required. Naturality
    follows from the commuting kernel square and coend functoriality. *)

(** 只需两个端点的卷积选择；自然性由核交换方块及 coend 函子性得到。 *)

Program Definition DayMapN@{u p +} {C : Cat} (T : Functor (C ×C C) C)
    {F F' G G' : Functor C (SetCat@{u p _ _ _ _ _})}
    `{HD : !HasDay C T F G} `{HD' : !HasDay C T F' G'}
    (α : F ⇒ F') (β : G ⇒ G')
  : DayF T F G ⇒ DayF T F' G'
  :=
  {|nt Z := coend_map (DayInputN T α β Z)
  |}.
Next Obligation.
  transitivity (coend_map (DayInputN T α β Y ∘Nv DayPostN T f)).
  - symmetry. apply (@coend_map_comp (C ×C C) SetCat).
  - transitivity (coend_map (DayPostN T f ∘Nv DayInputN T α β X)).
    + apply (@coend_map_proper (C ×C C) SetCat). apply day_input_post.
    + apply (@coend_map_comp (C ×C C) SetCat).
Defined.

(** ** Maps between Chosen Convolutions

    Work with the explicit choices at the endpoints. The laws are inherited
    from kernel transformations and the general coend map laws. *)

(** ** 选定卷积之间的映射

    使用端点处的显式选择；定律继承自核变换和一般 coend 映射定律。 *)

Section MapLaws.
Universes u p.
Context {C : Cat} (T : Functor (C ×C C) C).

(** Convolution maps respect equality of both input transformations. *)

(** 卷积映射保持两路输入自然变换的相等。 *)

Global Instance day_map_proper {F F' G G' : Functor C (SetCat@{u p _ _ _ _ _})}
    `{HD : !HasDay C T F G} `{HD' : !HasDay C T F' G'}
  : Proper (NatEq ==> NatEq ==> NatEq)
      (λ (α : F ⇒ F') (β : G ⇒ G'), DayMapN T α β).
Proof.
  intros α α' H β β' K Z.
  apply (@coend_map_proper (C ×C C) SetCat).
  exact (@day_input_proper C T F F' G G' Z α α' H β β' K).
Defined.

(** Identity input transformations give the identity convolution map. *)

(** 输入恒等自然变换给出恒等卷积映射。 *)

Lemma day_map_id (F G : Functor C (SetCat@{u p _ _ _ _ _})) `{HD : !HasDay C T F G}
  : DayMapN T (idN (F := F)) (idN (F := G)) ≈N idN.
Proof.
  intros Z. change (coend_map (DayInputN T idN idN Z) ≈ id).
  transitivity (coend_map (idN (F := DayKernel T F G Z))).
  - apply (@coend_map_proper (C ×C C) SetCat). apply day_input_id.
  - apply (@coend_map_id (C ×C C) SetCat).
Defined.

(** Composition is preserved with only the three endpoint choices. *)

(** 只需三个端点选择就可保持复合。 *)

Lemma day_map_comp {F F' F'' G G' G'' : Functor C (SetCat@{u p _ _ _ _ _})}
    `{HD : !HasDay C T F G} `{HD' : !HasDay C T F' G'}
    `{HD'' : !HasDay C T F'' G''}
    (α' : F' ⇒ F'') (α : F ⇒ F')
    (β' : G' ⇒ G'') (β : G ⇒ G')
  : DayMapN T (α' ∘Nv α) (β' ∘Nv β) ≈N
      (DayMapN T α' β' ∘Nv DayMapN T α β).
Proof.
  intros Z.
  change (coend_map (DayInputN T (α' ∘Nv α) (β' ∘Nv β) Z) ≈
    coend_map (DayInputN T α' β' Z) ∘ coend_map (DayInputN T α β Z)).
  transitivity (coend_map
    (DayInputN T α' β' Z ∘Nv DayInputN T α β Z)).
  - apply (@coend_map_proper (C ×C C) SetCat). apply day_input_comp.
  - apply (@coend_map_comp (C ×C C) SetCat).
Defined.

End MapLaws.

(** Uniformly selected convolution pairs give the tensor bifunctor on the
    functor category. This is only a bifunctor: monoidal units, associators
    and coherence still require separate proofs. The choice family is an
    explicit argument and installs no global instances. *)

(** 统一选取卷积对得到函子范畴上的张量双函子。这只给出双函子：幺半单位、
    结合子及相干性仍须单独证明。选择族是显式参数，不安装全局实例。 *)

Program Definition DayTensorF@{u p +} {C : Cat}
    (T : Functor (C ×C C) C)
    (HD : ∀ F G : Functor C (SetCat@{u p _ _ _ _ _}), HasDay C T F G)
  : Functor (Fct C SetCat ×C Fct C SetCat) (Fct C SetCat)
  :=
  {|F0 q := @DayF C T (fst q) (snd q) (HD (fst q) (snd q))
  ; F1 q q' α := @DayMapN C T (fst q) (fst q') (snd q) (snd q')
      (HD (fst q) (snd q)) (HD (fst q') (snd q')) (fst α) (snd α)
  |}.
Next Obligation.
  intros [α β] [α' β'] [H K].
  exact (@day_map_proper C T _ _ _ _ _ _ α α' H β β' K).
Defined.
Next Obligation. destruct X as [F G]. apply day_map_id. Defined.
Next Obligation.
  destruct X as [F G], Y as [F' G'], Z as [F'' G''],
    f as [α' β'], g as [α β].
  apply day_map_comp.
Defined.
