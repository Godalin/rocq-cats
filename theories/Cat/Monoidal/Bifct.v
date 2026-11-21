From Cats Require Export
  Cat.Monoidal.Monoidal.

Local Open Scope monoidal_scope.
Local Open Scope ob_scope.

(** * Bifunctors and Separate Tensoring *)

(** * 双函子与分别张量 *)

(** The left bracketing of a tensor on triples. *)

(** 三个对象上的左括号张量函子。 *)

Definition Tensor3LF {C : Cat} (T : Fct (C ×C C) C)
  : Fct ((C ×C C) ×C C) C
  := T ∘F (T ×F IdF).

(** The right bracketing, on the same triple-product source. *)

(** 在同一个三重乘积来源上的右括号张量函子。 *)

Program Definition Tensor3RF {C : Cat} (T : Fct (C ×C C) C)
  : Fct ((C ×C C) ×C C) C
  :=
  {|fobj p := T (fst (fst p), T (snd (fst p), snd p))
  ; fmap p q f := fmap T
      (X := (fst (fst p), T (snd (fst p), snd p)))
      (Y := (fst (fst q), T (snd (fst q), snd q)))
      (fst (fst f), fmap T
        (X := (snd (fst p), snd p)) (Y := (snd (fst q), snd q))
        (snd (fst f), snd f))
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation.
  intros [[f g] h] [[f' g'] h'] [[Hf Hg] Hh]. cbn.
  apply fmap_proper. split; [exact Hf |].
  exact (@fmap_proper _ _ _ _ (isFct T)
    (snd (fst X), snd X) (snd (fst Y), snd Y)
    (g, h) (g', h') (Hg, Hh)).
Qed.
Next Obligation.
  transitivity (fmap T
    (X := (fst (fst X), T (snd (fst X), snd X)))
    (Y := (fst (fst X), T (snd (fst X), snd X))) (id, id)).
  - apply fmap_proper. split; [reflexivity |].
    exact (@fmap_id _ _ _ _ (isFct T) (snd (fst X), snd X)).
  - exact (fmap_id (IsFct := isFct T)
      (X := (fst (fst X), T (snd (fst X), snd X)))).
Qed.
Next Obligation.
  etransitivity; [| apply fmap_comp].
  apply fmap_proper. split; [reflexivity |].
  exact (@fmap_comp _ _ _ _ (isFct T)
    (snd (fst X), snd X) (snd (fst Y), snd Y) (snd (fst Z), snd Z)
    (snd (fst f), snd f) (snd (fst g), snd g)).
Qed.

(** Display the two bracketings when the object argument is a triple.
    Use application precedence to preserve grouping inside larger terms. *)

(** 当对象参数是三元组时显示两种括号排列。采用函数应用的优先级，
    使它们作为更大表达式的参数时保留括号。 *)

#[warnings="-postfix-notation-not-level-1"]
Notation "T ( T ( X , Y ) , Z )" := (fobj (Tensor3LF T) ((X, Y), Z))
  (at level 10, T at level 9, only printing,
    format "T  ( T  ( X ,  Y ) ,  Z )")
  : monoidal_scope.
#[warnings="-postfix-notation-not-level-1"]
Notation "T ( X , T ( Y , Z ) )" := (fobj (Tensor3RF T) ((X, Y), Z))
  (at level 10, T at level 9, only printing,
    format "T  ( X ,  T  ( Y ,  Z ) )")
  : monoidal_scope.

(** ** Separate Actions from a Bifunctor

    Fix a tensor bifunctor on a category. Recover its two separate actions
    and compare their assembled map with the supplied bifunctor action. *)

(** ** 从双函子得到分别作用

    固定范畴上的张量双函子，恢复两个分别作用，并将组装映射与原双函子作用比较。 *)

Section BinoidalAssembly.
Context {C : Cat} (T : Fct (C ×C C) C).

(** Reuse the same object tensor, fixing one identity arrow at a time. *)

(** 复用同一对象张量，每次固定一侧恒等态射。 *)

Program Definition BifctHasBinoidal
  : HasBinoidal C
  :=
  {|tensor X Y := T (X, Y)
  ; tensor_l X Y Z f := fmap T (X := (Z, X)) (Y := (Z, Y)) (id, f)
  ; tensor_r X Y Z f := fmap T (X := (X, Z)) (Y := (Y, Z)) (f, id)
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
  intros f g H. apply fmap_proper. split; [reflexivity | exact H].
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

End BinoidalAssembly.

(** ** Recovering Interchange from a Bifunctor

    Use the separate actions of a supplied tensor bifunctor. Its
    functoriality gives their interchange and compares the recovered
    bifunctor with the original. *)

(** ** 从双函子恢复交换律

    使用给定张量双函子的分别作用。函子性给出其交换律，并将恢复的双函子与原双函子比较。 *)

Section FromBifct.
Context {C : Cat} (T : Fct (C ×C C) C).

(** The interchange witness belongs to the actions extracted from [T]. *)

(** 交换律见证属于从 [T] 提取的张量作用。 *)

Definition BifctTensorInterchange
  : @IsMagmoidal C (BifctHasBinoidal T)
  :=
  {|tensor_interchange X X' Y Y' f g :=
      fst (bifct_arrow_central T f Y Y' g)
  |}.

(** Pack the tensor actions and their interchange. *)

(** 打包张量作用及其交换律。 *)

Definition BifctMagmoidal
  : MagmoidalCat
  := MagmoidalCatOfBinoidalCat (BifctBinoidal T) BifctTensorInterchange.

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

End FromBifct.

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

(** ** Associativity without a Unit

    Fix a joint associator and its pentagon. Naturality in each position
    follows by holding the other two arrows at their identities. *)

(** ** 不带单位的结合性

    固定联合结合子及其五边形。将另两条态射固定为恒等，即得各位置的自然性。 *)

Section Associativity.
Context {C : Cat} (T : Fct (C ×C C) C)
  (A : Tensor3LF T ≅N Tensor3RF T)
  (Hp : is_tensor_pentagon T A).

(** The last-variable family stores the original maps and inverses.
    The remaining directions constrain these same components. *)

(** 最后变量族保存原映射及逆，其他方向约束同一组分量。 *)

Program Definition BifctHasAssoc
  : @HasTensorAssoc C (BifctHasBinoidal T)
  :=
  {|TensorAssocRIso X Y :=
      ({|nt Z := A.1 ((X, Y), Z)|}; λ Z, A.2 ((X, Y), Z))
  ; isTensorAssoc :=
      {|assoc_natural_l Y Z := {|nat_iso_naturality X X' f := _|}
      ; assoc_natural_m X Z := {|nat_iso_naturality Y Y' g := _|}
      ; assoc_central X Y Z := bifct_arrow_central T _
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
  := SemigroupalCatOfMagmoidalCat (BifctMagmoidal T) BifctHasAssoc.

End Associativity.

(** * Structural Choices from a Tensor Bifunctor

    Restrict joint natural isomorphisms to the separate tensor actions.
    Associativity and unitors can be constructed independently. Their
    combination uses only the triangle connecting the supplied choices. *)

(** * 从张量双函子得到结构选择

    将联合自然同构限制到分别张量作用上。结合性与单位子可独立构造；组合时
    只使用连接给定选择的三角形。 *)

Section PremonoidalAssembly.
Context {C : Cat} (T : Fct (C ×C C) C).

Let BC
  : HasBinoidal C
  := BifctHasBinoidal T.

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
  : @HasTensorUnitors C BC
  :=
  {|tensor_unit := I
  ; TensorUnitorLIso :=
      ({|nt X := L.1 X|}; L.2)
  ; TensorUnitorRIso :=
      ({|nt X := R.1 X|}; R.2)
  ; isTensorUnitors :=
      {|unitor_l_central X := bifct_arrow_central T _
      ; unitor_r_central X := bifct_arrow_central T _
      |}
  |}.
Next Obligation. exact (nat_naturality L.1 f). Qed.
Next Obligation. exact (nat_naturality R.1 f). Qed.

End Unit.

(** ** Compatible Choices

    The independently built choices share exactly [BC]. Only their
    triangle remains when constructing the premonoidal extension. *)

(** ** 相容选择

    独立构造的选择共享恰好同一 [BC]；构造预幺半扩展时只剩三角形条件。 *)

Section Compatibility.
Context (I : C) (A : Tensor3LF T ≅N Tensor3RF T)
    (L : AtLF T I ≅N IdF) (R : AtRF T I ≅N IdF)
    (Hp : is_tensor_pentagon T A)
    (Ht : ∀ X Y : C,
      fmap (AtLF T X) (L.1 Y) ∘ A.1 ((X, I), Y) ≈ fmap (AtRF T Y) (R.1 X)).

(** Check the triangle on the associator and unitors extracted from [T]. *)

(** 检查从 [T] 提取的结合子和单位子的三角形。 *)

Program Definition BifctIsPremonoidal
  : @IsPremonoidal C BC (BifctHasAssoc T A Hp) (BifctHasUnitors I L R)
  :=
  {|tensor_triangle := _|}.
Next Obligation. exact (Ht X Y). Qed.

End Compatibility.
End PremonoidalAssembly.

(** * Assembly from a Tensor Bifunctor

    Existing models may supply one bifunctor and natural structural
    isomorphisms. This constructor obtains interchange and associativity
    in the semigroupal parent, then adds the supplied unitors and triangle. *)

(** * 从张量双函子装配

    已有模型可以提供一个双函子及自然结构同构。本构造在半群张量父结构中
    提取交换律和结合子，再加入给定单位子及三角形。 *)

Section MonoidalAssembly.
Context {C : Cat} (T : Fct (C ×C C) C) (I : C)
  (A : Tensor3LF T ≅N Tensor3RF T)
  (L : AtLF T I ≅N IdF) (R : AtRF T I ≅N IdF).

Context
  (Hp : is_tensor_pentagon T A)
  (Ht : ∀ X Y : @Ob C,
    fmap (AtLF T X) (L.1 Y) ∘ A.1 ((X, I), Y)
      ≈ fmap (AtRF T Y) (R.1 X)).

(** Retain every supplied object and structural inverse. Only derived
    action laws, centrality and separate naturality are reconstructed. *)

(** 保留给定的全部对象与结构逆；仅重建导出的作用定律、中心性及分别自然性。 *)

Definition BifctMonoidal
  : MonoidalCat
  := MonoidalCatOfSemigroupalCat (BifctSemigroupal T A Hp)
       (BifctHasUnitors T I L R) (BifctIsPremonoidal T I A L R Hp Ht).

(** Read the same structure on the original fixed category. *)

(** 在原固定范畴上读取同一结构。 *)

Definition BifctHasMonoidal
  : HasMonoidal C
  := MonoidalCatToHasMonoidal BifctMonoidal.

End MonoidalAssembly.

(** * The Joint Associator

    Fix the tensor actions, interchange and an associator. Regard the
    same components and inverses as a natural isomorphism between the
    two bracketings of the joint tensor bifunctor. *)

(** * 联合结合子

    固定张量作用、交换律及结合子。将同一组分量及逆读作联合张量双函子的
    两种括号排列之间的自然同构。 *)

Section JointAssociativity.
Context {C : Cat}
  `{BC : !HasBinoidal C} `{IM : !@IsMagmoidal C BC}
  `{AC : !@HasTensorAssoc C BC}.

(** Package derived joint naturality with the inherited associator. *)

(** 将导出的联合自然性与继承结合子打包。 *)

Local Program Definition TensorAssociatorN
  : Tensor3LF (tensorF IM) ⇒ Tensor3RF (tensorF IM)
  :=
  {|nt p := α[fst (fst p); snd (fst p); snd p]
  |}.
Next Obligation.
  destruct X as [[x y] z], Y as [[x' y'] z'], f as [[f g] h].
  apply tensor_assoc_sequence_natural.
Qed.

(** The natural isomorphism retains the same component inverses. *)

(** 自然同构保留相同的分量逆。 *)

Definition TensorAssocIsoN
  : Tensor3LF (tensorF IM) ≅N Tensor3RF (tensorF IM)
  := (TensorAssociatorN;
      λ p, (tensor_assoc (fst (fst p)) (snd (fst p)) (snd p)).2).

End JointAssociativity.
