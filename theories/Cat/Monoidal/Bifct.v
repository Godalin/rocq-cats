From Cats Require Export
  Cat.Monoidal.Monoidal.

Local Open Scope monoidal_scope.
Local Open Scope ob_scope.

(** * Bifunctors and Separate Tensoring *)

(** * 双函子与分别张量 *)

(** The pentagon for a specified joint associator on a tensor bifunctor. *)

(** 给定张量双函子和联合结合子的五边形。 *)

Definition is_tensor_pentagon {C : Cat}
    (T : Fct (C ×C C) C) (A : Tensor3LF T ≅N Tensor3RF T)
  : Type
  := ∀ W X Y Z : C,
    A.1 ((W, X), T (Y, Z)) ∘ A.1 ((T (W, X), Y), Z)
    ≈ fmap (AtLF T W) (A.1 ((X, Y), Z))
      ∘ (A.1 ((W, T (X, Y)), Z)
          ∘ fmap (AtRF T Z) (A.1 ((W, X), Y))).

Arguments is_tensor_pentagon {_} _ _.

(** ** Separate Actions from a Bifunctor

    Fix a tensor bifunctor on a category. Recover its two separate actions
    and compare their assembled map with the supplied bifunctor action. *)

(** ** 从双函子得到分别作用

    固定范畴上的张量双函子，恢复两个分别作用，并将组装映射与原双函子作用比较。 *)

Section TensorAssembly.
Context {C : Cat} (T : Fct (C ×C C) C).

(** Reuse the same object tensor, fixing one identity arrow at a time. *)

(** 复用同一对象张量，每次固定一侧恒等态射。 *)

Program Definition BifctHasBinoidal
  : HasBinoidal C
  :=
  {|tensor X Y := T (X, Y)
  ; tensor_l X Y Z f
    := fmap T (X := (Z, X)) (Y := (Z, Y)) (id, f)
  ; tensor_r X Y Z f
    := fmap T (X := (X, Z)) (Y := (Y, Z)) (f, id)
  ; isBinoidalL Z :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  ; isBinoidalR Z :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation.
  intros f g H. apply fmap_proper.
  split; [reflexivity | exact H].
Qed.
Next Obligation.
  exact (fmap_id (IsFct := isFct T) (X := (Z, X))).
Qed.
Next Obligation.
  rewrite <- fmap_comp. apply fmap_proper.
  split; [symmetry; apply comp_id_l | reflexivity].
Qed.
Next Obligation.
  intros f g H. apply fmap_proper. split; [exact H | reflexivity].
Qed.
Next Obligation.
  exact (fmap_id (IsFct := isFct T) (X := (X, Z))).
Qed.
Next Obligation.
  rewrite <- fmap_comp. apply fmap_proper.
  split; [reflexivity | symmetry; apply comp_id_l].
Qed.

(** The complete bundle retains this exact category and chosen extension. *)

(** 完整打包保留同一范畴及选定扩展。 *)

Definition BifctBinoidal
  : BinoidalCat
  := MakeBinoidalCat C BifctHasBinoidal.

(** Both execution orders agree by bifunctoriality alone. *)

(** 仅由双函子性，两种执行次序相等。 *)

Definition bifct_arrow_central {X Y : C} (f : Hom X Y)
  : @is_central C BifctHasBinoidal X Y f.
Proof.
  intros Z W g. split.
  - change (fmap T (X := (X, W)) (Y := (Y, W)) (f, id) ∘
      fmap T (X := (X, Z)) (Y := (X, W)) (id, g) ≈
      fmap T (X := (Y, Z)) (Y := (Y, W)) (id, g) ∘
      fmap T (X := (X, Z)) (Y := (Y, Z)) (f, id)).
    rewrite <- !fmap_comp.
    apply fmap_proper. split; rewrite comp_id_l, comp_id_r;
      reflexivity.
  - change (fmap T (X := (W, X)) (Y := (W, Y)) (id, f) ∘
      fmap T (X := (Z, X)) (Y := (W, X)) (g, id) ≈
      fmap T (X := (Z, Y)) (Y := (W, Y)) (g, id) ∘
      fmap T (X := (Z, X)) (Y := (Z, Y)) (id, f)).
    rewrite <- !fmap_comp.
    apply fmap_proper. split; rewrite comp_id_l, comp_id_r;
      reflexivity.
Qed.

(** Ordered context actions recover the given bifunctor's arrow map
    in specified hom equality, without equality of functor records. *)

(** 有序上下文作用在指定 Hom 相等下恢复给定双函子的态射映射，不比较函子记录。 *)

Lemma bifct_sequence {X X' Y Y' : C}
    (f : Hom X X') (g : Hom Y Y')
  : @tensor_sequence C BifctHasBinoidal X X' Y Y' f g ≈
      fmap T (X := (X, Y)) (Y := (X', Y')) (f, g).
Proof.
  change (fmap T (X := (X', Y)) (Y := (X', Y')) (id, g) ∘
    fmap T (X := (X, Y)) (Y := (X', Y)) (f, id) ≈
    fmap T (X := (X, Y)) (Y := (X', Y')) (f, g)).
  rewrite <- fmap_comp. apply fmap_proper.
  split; [apply comp_id_l | apply comp_id_r].
Qed.

(** ** Recovering Interchange from a Bifunctor

    Use the separate actions of a supplied tensor bifunctor. Its
    functoriality gives their interchange and compares the recovered
    bifunctor with the original. *)

(** ** 从双函子恢复交换律

    使用给定张量双函子的分别作用。函子性给出其交换律，并将恢复的双函子与原双函子比较。 *)

(** The interchange witness belongs to the actions extracted from [T]. *)

(** 交换律见证属于从 [T] 提取的张量作用。 *)

Definition BifctTensorInterchange
  : @IsMagmoidal C BifctHasBinoidal
  :=
  {|tensor_interchange X X' Y Y' f g :=
      fst (bifct_arrow_central f Y Y' g)
  |}.

(** Pack the tensor actions and their interchange. *)

(** 打包张量作用及其交换律。 *)

Definition BifctMagmoidal
  : MagmoidalCat
  := MagmoidalCatOfBinoidalCat BifctBinoidal BifctTensorInterchange.

(** Compare the reconstructed tensor functor with the supplied one by
    identity components, rather than equality of their records. *)

(** 用恒等分量比较重建张量函子与给定函子，不要求其记录相等。 *)

Program Definition BifctTensorN
  : tensorF BifctTensorInterchange ⇒ T
  :=
  {|nt p := _
  |}.
Next Obligation. destruct p as [X Y]. exact id. Defined.
Next Obligation.
  destruct X as [X1 X2], Y as [Y1 Y2], f as [f g].
  rewrite comp_id_l, comp_id_r. apply bifct_sequence.
Qed.

(** Both comparison directions compute to identities on each object pair. *)

(** 对每个对象对，两个比较方向都计算为恒等。 *)

Definition bifct_tensor_iso
  : tensorF BifctTensorInterchange ≅N T.
Proof.
  exists BifctTensorN. intros [X Y].
  exists id. split; apply comp_id_l.
Defined.

(** ** Associativity without a Unit

    Fix a joint associator and its pentagon. Naturality in each position
    follows by holding the other two arrows at their identities. *)

(** ** 不带单位的结合性

    固定联合结合子及其五边形。将另两条态射固定为恒等，即得各位置的自然性。 *)

Section Associativity.
Context (A : Tensor3LF T ≅N Tensor3RF T)
  (Hp : is_tensor_pentagon T A).

(** The last-variable family stores the original maps and inverses.
    The remaining directions constrain these same components. *)

(** 最后变量族保存原映射及逆，其他方向约束同一组分量。 *)

Program Definition BifctHasAssoc
  : @HasTensorAssoc C BifctHasBinoidal
  :=
  {|TensorAssocRIso X Y :=
      ({|nt Z := A.1 ((X, Y), Z)|}; λ Z, A.2 ((X, Y), Z))
  ; isTensorAssoc :=
      {|assoc_natural_l Y Z := {|nat_iso_naturality X X' f := _|}
      ; assoc_natural_m X Z := {|nat_iso_naturality Y Y' g := _|}
      ; assoc_central X Y Z := bifct_arrow_central _
      ; assoc_pentagon := Hp
      |}
  |}.
Next Obligation.
  pose proof (nat_naturality A.1
    (X := ((X, Y), X0)) (Y := ((X, Y), Y0)) ((id, id), f)) as H.
  cbn in H. etransitivity; [| exact H].
  apply comp_proper; [reflexivity |].
  apply fmap_proper. split;
    [symmetry; exact (@fmap_id _ _ _ _ (isFct T) (X, Y)) | reflexivity].
Qed.
Next Obligation.
  pose proof (nat_naturality A.1
    (X := ((X, Y), Z)) (Y := ((X', Y), Z)) ((f, id), id)) as H.
  cbn in H. etransitivity; [exact H |].
  apply comp_proper; [| reflexivity].
  apply fmap_proper. split;
    [reflexivity | exact (@fmap_id _ _ _ _ (isFct T) (Y, Z))].
Qed.
Next Obligation.
  exact (nat_naturality A.1
    (X := ((X, Y), Z)) (Y := ((X, Y'), Z)) ((id, g), id)).
Qed.

(** Add the chosen associator to the magmoidal tensor. *)

(** 为带交换律的张量加入选定的结合子。 *)

Definition BifctSemigroupal
  : SemigroupalCat
  := SemigroupalCatOfMagmoidalCat BifctMagmoidal BifctHasAssoc.

End Associativity.

(** * Structural Choices from a Tensor Bifunctor

    Restrict joint natural isomorphisms to the separate tensor actions.
    Associativity and unitors can be constructed independently. Their
    combination uses only the triangle connecting the supplied choices. *)

(** * 从张量双函子得到结构选择

    将联合自然同构限制到分别张量作用上。结合性与单位子可独立构造；组合时
    只使用连接给定选择的三角形。 *)

(** ** Unit Choices without an Associator

    Fix one unit and two joint unitors. Repackage their components at the
    derived action functors, retaining the supplied inverse witnesses. *)

(** ** 不带结合子的单位选择

    固定唯一单位及两个联合单位子。按导出的作用函子重新打包分量，保留给定
    的逆见证。 *)

Section Unit.
Context (I : C) (L : AtLF T I ≅N IdF) (R : AtRF T I ≅N IdF).

(** No associativity or coherence with an associator is needed here. *)

(** 此处无需结合性或与结合子的相干性。 *)

Program Definition BifctHasUnitors
  : @HasTensorUnitors C BifctHasBinoidal
  :=
  {|tensor_unit := I
  ; TensorUnitorLIso :=
      ({|nt X := L.1 X|}; L.2)
  ; TensorUnitorRIso :=
      ({|nt X := R.1 X|}; R.2)
  ; isTensorUnitors :=
      {|unitor_l_central X := bifct_arrow_central _
      ; unitor_r_central X := bifct_arrow_central _
      |}
  |}.
Next Obligation. exact (nat_naturality L.1 f). Qed.
Next Obligation. exact (nat_naturality R.1 f). Qed.

End Unit.

(** ** Compatible Choices

    The independently built choices share exactly [BifctHasBinoidal]. Only their
    triangle remains when constructing the premonoidal extension. *)

(** ** 相容选择

    独立构造的选择共享恰好同一 [BifctHasBinoidal]；构造预幺半扩展时只剩三角形条件。 *)

Section Compatibility.
Context (I : C) (A : Tensor3LF T ≅N Tensor3RF T)
    (L : AtLF T I ≅N IdF) (R : AtRF T I ≅N IdF)
    (Hp : is_tensor_pentagon T A)
    (Ht : ∀ X Y : C,
      fmap (AtLF T X) (L.1 Y) ∘ A.1 ((X, I), Y) ≈ fmap (AtRF T Y) (R.1 X)).

(** Check the triangle on the associator and unitors extracted from [T]. *)

(** 检查从 [T] 提取的结合子和单位子的三角形。 *)

Program Definition BifctIsPremonoidal
  : @IsPremonoidal C BifctHasBinoidal (BifctHasAssoc A Hp) (BifctHasUnitors I L R)
  :=
  {|tensor_triangle := _|}.
Next Obligation. exact (Ht X Y). Qed.

(** * Assembly from a Tensor Bifunctor

    Existing models may supply one bifunctor and natural structural
    isomorphisms. This constructor obtains interchange and associativity
    in the semigroupal parent, then adds the supplied unitors and triangle. *)

(** * 从张量双函子装配

    已有模型可以提供一个双函子及自然结构同构。本构造在半群张量父结构中
    提取交换律和结合子，再加入给定单位子及三角形。 *)

(** Retain every supplied object and structural inverse. Only derived
    action laws, centrality and separate naturality are reconstructed. *)

(** 保留给定的全部对象与结构逆；仅重建导出的作用定律、中心性及分别自然性。 *)

Definition BifctMonoidal
  : MonoidalCat
  := MonoidalCatOfSemigroupalCat (BifctSemigroupal A Hp)
       (BifctHasUnitors I L R) BifctIsPremonoidal.

(** Read the same structure on the original fixed category. *)

(** 在原固定范畴上读取同一结构。 *)

Definition BifctHasMonoidal
  : HasMonoidal C
  := MonoidalCatToHasMonoidal BifctMonoidal.

End Compatibility.
End TensorAssembly.
