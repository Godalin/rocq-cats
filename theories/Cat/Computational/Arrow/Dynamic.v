From Cats Require Export
  Cat.Computational.Arrow.Apply
  Cat.Computational.Arrow.Global
  Cat.Computational.Arrow.Kleisli
  Cat.Monad.Extension
  Cat.Applicative.Morphism.
From Cats Require Import
  Cat.Adjunction
  Cat.Induced
  Cat.Isomorphism
  Cat.Functor.FullyFaithful
  Cat.Monoidal.Cartesian
  Cat.Monad.Adjunction
  Cat.Computational.Arrow.Applicative
  Instance.Set.Cartesian
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Hom
  Instance.Set.Monoid
  Instance.Set.Strength
  Instance.Set.Arrow
  Instance.Set.KleisliApply.
From Cats.Set Require Import
  Constant.
Import Cats.Cat.Core Cats.Cat.Product.Core.

Local Open Scope set_scope.
Local Open Scope computation_scope.
Local Open Scope monad_scope.
Local Open Scope monoidal_scope.
Local Open Scope applicative_scope.

(** The pairing proofs use the cartesian laws. Keep rewriting from unfolding
    the monoidal structure on setoids during proof search. *)

(** 配对证明使用笛卡尔定律。重写搜索时保持广集上的幺半结构不展开。 *)

Local Opaque CartHasMonoidal.

(** * Naming Input-Indexed Computations

    Fix a cartesian Arrow over setoids, with the native computation hom
    carrier/equality levels matched to the base. Name a computation by
    its pure-input substitutions. Only this naming direction and its
    naturality require an ordinary Arrow, not dynamic application. *)

(** * 命名按输入索引的计算

    固定广集上的笛卡尔 Arrow，将原生计算 Hom 载体／相等层级对应到基底。
    以纯输入代入命名计算；命名方向及其自然性仅要求通常 Arrow，不要求
    动态应用。 *)

Section Naming.
Universes o u p.
Context {K : Cat@{o u p _ _}}
    (A : Arrow (SetCat@{u p _ _ _ _ _}) K).

(** Substitute each ordinary input purely into the computation. *)

(** 将每个通常输入纯地代入计算。 *)

Program Definition arrow_dynamic_name {X Y : SetC@{u p}}
    (f : Hom (A X) (A Y))
  : X →r ArrowGlobalF A Y
  :=
  {|func x := f ∘ arr[A; const[UnitS] x]
  |}.
Next Obligation.
  intros x x' H. apply comp_proper; [reflexivity |].
  apply fmap_proper. intros z. exact H.
Qed.

(** Naming respects native computation equality. *)

(** 命名保持原生计算相等。 *)

Global Instance arrow_dynamic_name_proper {X Y : SetC@{u p}}
  : Proper (HomEq ==> @HomEq SetCat X (ArrowGlobalF A Y))
      (@arrow_dynamic_name X Y).
Proof. intros f g H x. cbn. rewrite H. reflexivity. Qed.

(** Pure input substitution is ordinary precomposition of the name. *)

(** 纯输入代入就是命名的通常预合成。 *)

Lemma arrow_dynamic_name_pre {X X' Y : SetC@{u p}}
    (f : Hom (A X) (A Y)) (h : X' →r X)
  : arrow_dynamic_name (f ∘ arr[A; h])
    ≈f (arrow_dynamic_name f ∘r h).
Proof.
  intros x. change ((f ∘ arr[A; h]) ∘ arr[A; const[UnitS] x]
    ≈ f ∘ arr[A; const[UnitS] (h x)]).
  rewrite comp_assoc, <- fmap_comp. apply comp_proper;
    [reflexivity |]. apply fmap_proper. intros []. reflexivity.
Qed.

(** An arbitrary following computation postcomposes every named value. *)

(** 任意后续计算后合成每个命名值。 *)

Lemma arrow_dynamic_name_post {X Y Z : SetC@{u p}}
    (f : Hom (A X) (A Y)) (k : Hom (A Y) (A Z))
  : arrow_dynamic_name (k ∘ f)
    ≈f (k _* ∘r arrow_dynamic_name f).
Proof. intros x. apply comp_assoc. Qed.

(** Package naming as a native Hom-setoid map. Its two setoids may have
    different native sizes; no common-bound identification is imposed. *)

(** 将命名打包为原生 Hom 广集映射；两侧广集可以具有不同原生大小，不施加共同
    界的同一化。 *)

Program Definition arrow_dynamic_name_resp (X Y : SetC@{u p})
  : HomSet (A X) (A Y) →r (X →S ArrowGlobalF A Y)
  :=
  {|func := arrow_dynamic_name
  |}.

(** Naming a terminal-input computation and evaluating its name at the
    singleton leaves that computation unchanged. Only an ordinary Arrow
    and the uniqueness of the terminal input are used. *)

(** 命名终输入计算后，在单元素处求值命名，保持原计算不变。只使用通常 Arrow
    及终输入的唯一性。 *)

Lemma arrow_dynamic_name_global {Y : SetC@{u p}}
    (f : Hom (A UnitS) (A Y))
  : arrow_dynamic_name f tt ≈ f.
Proof.
  change (f ∘ arr[A; @const_resp UnitS UnitS tt] ≈ f).
  transitivity (f ∘ arr[A; (id_resp (X := UnitS))]).
  - apply comp_proper; [reflexivity|].
    apply fmap_proper. intros []. exact tt.
  - rewrite arrow_arr_id, comp_id_r. reflexivity.
Qed.

(** Naming a computation with ordinary context pairs the fixed context
    with its named result. Invert the pure unit-context square; only an
    ordinary Arrow is needed, with no dynamic application or Monad. *)

(** 命名带通常上下文的计算，等于将固定上下文配到命名结果旁。对纯单位上下文
    方块取逆即可证明，仅要求通常 Arrow，不使用动态应用或 Monad。 *)

Lemma arrow_dynamic_name_context {X Y : SetC@{u p}} (Z : SetC@{u p})
    (f : Hom (A X) (A Y)) (z : Z) (x : X)
  : arrow_dynamic_name (context[A; Z; f]) (z,x)
    ≈ fmap (ArrowGlobalF A) ⟨const[Y] z, id⟩ (arrow_dynamic_name f x).
Proof.
  change (second[A; f; Z] ∘ arr[A; const[UnitS] (z,x)]
    ≈ arr[A; ⟨const[Y] z, id⟩]
      ∘ (f ∘ arr[A; const[UnitS] x])).
  pose proof (iso_square_inv
    (arr[A; (π2 : UnitS ×S X →r X)];
      fct_is_iso A _ (CartUnitorLIso.2 X))
    (arr[A; (π2 : UnitS ×S Y →r Y)];
      fct_is_iso A _ (CartUnitorLIso.2 Y))
    (second[A; f; UnitS]) f (arrow_context_unit A f)) as Hu.
  change (arr[A; (⟨!,id⟩ : Y →r UnitS ×S Y)] ∘ f
    ≈ second[A; f; UnitS] ∘ arr[A; (⟨!,id⟩ : X →r UnitS ×S X)]) in Hu.
  transitivity (arr[A; const[UnitS] z × (id_resp (X := Y))]
    ∘ (second[A; f; UnitS] ∘ arr[A; (⟨!,id⟩ : X →r UnitS ×S X)])
      ∘ arr[A; const[UnitS] x]).
  - symmetry. rewrite <- !comp_assoc, (arrow_second_natural (HC := CartCatToHasCartesian SetCat_Cart)), !comp_assoc,
      <- !fmap_comp. apply comp_proper; [reflexivity|].
    apply fmap_proper. intros []. split; reflexivity.
  - rewrite <- Hu, <- !comp_assoc, <- fmap_comp, !comp_assoc.
    apply comp_proper; [|reflexivity]. apply fmap_proper.
    intros y. split; reflexivity.
Qed.

End Naming.

(** * Evaluating Dynamic Names

    Add ArrowApply on the same native setoid base. Apply the chosen
    terminal-input computation to the singleton input, and prove both
    reconstruction laws. Computation equality remains native Hom equality;
    no independent pointwise extensionality assumption is introduced. *)

(** * 求值动态命名

    在同样原生广集基底上增加 ArrowApply，将选出的终输入计算应用于单元素
    输入，并证明两个重建律。计算相等保留原生 Hom 相等，不附加独立逐点外延性
    假设。 *)

Section DynamicReconstruction.
Universes o u p.
Context {K : Cat@{o u p _ _}} (AA : ArrowApply K).

(** A following computation may run after pairing or inside the
    dynamically supplied arrow. *)

(** 后续计算可在配对后运行，也可位于动态提供的箭头内部。 *)

Lemma arrow_apply_pair_post {X Y Z : SetC@{u p}}
    (k : Hom (AA (X ×S Y)) (AA Z))
  : apply[AA; Y; Z] ∘ arr[AA;
      (k _* ∘r arrow_apply_pair AA X Y) × id_resp] ≈ k.
Proof.
  transitivity ((apply[AA; Y; Z]
    ∘ arr[AA; k _* × id_resp])
      ∘ arr[AA; arrow_apply_pair AA X Y × id_resp]).
  - rewrite comp_assoc, <- fmap_comp. apply comp_proper;
      [reflexivity |]. apply fmap_proper. intros [x y].
    split; reflexivity.
  - rewrite arrow_apply_post, comp_assoc, arrow_apply_pair_id, comp_id_r.
    reflexivity.
Qed.

(** Run the terminal-input computation selected by the ordinary input. *)

(** 运行由通常输入选出的终输入计算。 *)

Definition arrow_dynamic_eval {X Y : SetC@{u p}}
    (f : X →r ArrowGlobalF AA Y)
  : Hom (AA X) (AA Y)
  := apply[AA; UnitS; Y] ∘ arr[AA; ⟨f, !⟩].

(** Evaluation respects pointwise equality of respectful names. *)

(** 求值保持保相等命名的逐点相等。 *)

Global Instance arrow_dynamic_eval_proper
    {X Y : SetC@{u p}}
  : Proper (@HomEq SetCat X (ArrowGlobalF AA Y)
        ==> HomEq)
      (@arrow_dynamic_eval X Y).
Proof.
  intros f g H. unfold arrow_dynamic_eval.
  apply comp_proper;
    [reflexivity |]. apply fmap_proper.
  intros x. split; [exact (H x)|exact tt].
Qed.

(** Evaluating the name reconstructs the original computation. *)

(** 求值命名重建原计算。 *)

Lemma arrow_dynamic_eval_name {X Y : SetC@{u p}}
    (f : Hom (AA X) (AA Y))
  : arrow_dynamic_eval (arrow_dynamic_name AA f) ≈ f.
Proof.
  pose (j := (⟨id, !⟩ : X →r (X ×S UnitS))).
  pose (q := (π1 : (X ×S UnitS) →r X)).
  pose (k := f ∘ arr[AA; q]).
  transitivity ((apply[AA; UnitS; Y] ∘ arr[AA;
    (k _* ∘r arrow_apply_pair AA X UnitS) × id_resp])
      ∘ arr[AA; j]).
  - unfold arrow_dynamic_eval.
    rewrite comp_assoc, <- fmap_comp. apply comp_proper;
      [reflexivity |]. apply fmap_proper. intros x. split.
    + change (f ∘ arr[AA; const[UnitS] x]
        ≈ (f ∘ arr[AA; q]) ∘ arr[AA; ⟨const[UnitS] x, id⟩]).
      rewrite comp_assoc, <- fmap_comp. apply comp_proper;
        [reflexivity |]. apply fmap_proper. intros []. reflexivity.
    + exact tt.
  - rewrite arrow_apply_pair_post. unfold k.
    rewrite comp_assoc, <- fmap_comp.
    transitivity (f ∘ arr[AA; id_resp (X := X)]).
    + apply comp_proper; [reflexivity |]. apply fmap_proper.
      intros x. reflexivity.
    + rewrite fmap_id, comp_id_r. reflexivity.
Qed.

(** Naming the evaluated computation returns the supplied name pointwise. *)

(** 命名求值后的计算，逐点返回所给命名。 *)

Lemma arrow_dynamic_name_eval {X Y : SetC@{u p}}
    (f : X →r ArrowGlobalF AA Y)
  : arrow_dynamic_name AA (arrow_dynamic_eval f) ≈f f.
Proof.
  intros x. unfold arrow_dynamic_name, arrow_dynamic_eval. cbn [func].
  rewrite comp_assoc, <- fmap_comp.
  transitivity (arrow_apply_const AA (f x)).
  - unfold arrow_apply_const. apply comp_proper; [reflexivity |].
    apply fmap_proper. intros []. split; [reflexivity|exact tt].
  - apply arrow_apply_const_value.
Qed.

(** Package evaluation as the reverse native Hom-setoid map. All
    computational operations remain transparent. *)

(** 将求值打包为反向原生 Hom 广集映射；全部计算运算保持透明。 *)

Program Definition arrow_dynamic_eval_resp (X Y : SetC@{u p})
  : (X →S ArrowGlobalF AA Y) →r HomSet (AA X) (AA Y)
  :=
  {|func := arrow_dynamic_eval
  |}.

(** * The Monad of a Dynamic Arrow

    Fix an ArrowApply on native setoids, with independent carrier and
    equality levels. Its pure inclusion into the indexed computation
    category is left adjoint to taking computations from the terminal
    input. Reuse the general adjunction-to-Monad construction; no closed
    structure or new proof of the three Monad laws is needed. *)

(** * 动态 Arrow 的 Monad

    固定原生广集上的 ArrowApply，载体与相等层级保持独立。纯计算到索引计算
    范畴的包含左伴随于取终端输入的计算。复用一般伴随到 Monad 的构造，
    不需要闭结构，也不重新证明三条 Monad 定律。 *)

(** The dynamic Hom correspondence supplies the adjunction. The existing
    constructor handles size bounds without identifying native Hom levels. *)

(** 动态 Hom 对应给出伴随；已有构造处理大小界，不将原生 Hom 层级等同。 *)

Program Definition ArrowApplyAdj
  : InducedF AA ⊣ (@ℎ1F (ComputationCat AA) UnitS)
  := AdjOfHom (InducedF AA) (@ℎ1F (ComputationCat AA) UnitS)
      (arrow_dynamic_name_resp AA) (arrow_dynamic_eval_resp) _ _ _ _.
Next Obligation. exact (arrow_dynamic_eval_name f). Qed.
Next Obligation. exact (arrow_dynamic_name_eval g). Qed.
Next Obligation. exact (arrow_dynamic_name_pre AA f h). Qed.
Next Obligation. exact (arrow_dynamic_name_post AA f k). Qed.

(** Forward transposition names the supplied computation. *)

(** 正向转置命名所给计算。 *)

Lemma arrow_apply_adjunct {X Y : SetC@{u p}} (f : Hom (AA X) (AA Y))
  : f^♯[ArrowApplyAdj] ≈f arrow_dynamic_name AA f.
Proof. reflexivity. Qed.

(** Inverse transposition dynamically evaluates a value-indexed computation. *)

(** 逆转置动态求值由值索引的计算。 *)

Lemma arrow_apply_unadjunct {X Y : SetC@{u p}}
    (f : X →r ArrowGlobalF AA Y)
  : f^♭[ArrowApplyAdj] ≈ arrow_dynamic_eval f.
Proof. reflexivity. Qed.

(** The induced Monad stores exactly the global computations of the Arrow. *)

(** 诱导的 Monad 存储恰好该 Arrow 的全局计算。 *)

Definition ArrowMonad
  : Monad (SetCat@{u p _ _ _ _ _})
  := AdjMonad ArrowApplyAdj.

(** Identity components compare the underlying functor with [ArrowGlobalF],
    without requiring equality of functor structures or their law fields. *)

(** 恒等分量将底层函子与 [ArrowGlobalF] 比较，不要求函子结构或定律字段相等。 *)

Program Definition ArrowMonadUnderlyingIso
  : (ArrowMonad : Fct SetCat SetCat) ≅N ArrowGlobalF AA
  := ({|nt X := id_resp
      |}; _).
Next Obligation. intros m. reflexivity. Qed.
Next Obligation.
  intros X. exists id_resp. split; intros m; reflexivity.
Defined.

(** The induced unit agrees with the existing pure global computation. *)

(** 诱导的单位与已有纯全局计算一致。 *)

Lemma arrow_monad_unit (X : SetC@{u p}) (x : X)
  : η[ArrowMonad] X x ≈ arrow_value_pure K AA X x.
Proof. exact (@comp_id_l K _ _ (arr[AA; const[UnitS] x])). Qed.

(** Multiplication runs the dynamically returned global computation. *)

(** 乘法运行动态返回的全局计算。 *)

Lemma arrow_monad_mul (X : SetC@{u p})
  : μ[ArrowMonad] X
    ≈f comp_l_resp (C := K) (f := arrow_dynamic_eval
        (id_resp (X := ArrowGlobalF AA X))).
Proof. reflexivity. Qed.

(** Extension first runs the input computation, then dynamically evaluates
    the continuation selected by its result. *)

(** 扩张先运行输入计算，再动态求值由其结果选定的续延。 *)

Lemma arrow_monad_extend {X Y : SetC@{u p}}
    (f : X →r ArrowGlobalF AA Y)
  : kleisli_extend ArrowMonad f
    ≈f comp_l_resp (C := K) (f := arrow_dynamic_eval f).
Proof.
  intros m.
  change (arrow_dynamic_eval (id_resp (X := ArrowGlobalF AA Y))
    ∘ (arr[AA; f] ∘ m) ≈ arrow_dynamic_eval f ∘ m).
  rewrite <- comp_assoc. apply comp_proper; [|reflexivity].
  symmetry. exact (unadjunct_counit ArrowApplyAdj f).
Qed.

(** * Dynamic Arrow Reconstruction through Kleisli Computations

    Fix an ArrowApply on native setoids, keeping computation-object,
    Hom carrier and equality levels independent. Give its recovered Monad
    canonical setoid strength, reuse the general Kleisli comparison and
    its full-faithful inverse, and compare both composites with identity.
    Both directions preserve pure arrows, sequencing and ordinary context.
    The computation category is indexed by value objects; no representatives
    of other ambient objects are selected. *)

(** * 经 Kleisli 计算重建动态 Arrow

    固定原生广集上的 ArrowApply，保持计算对象、Hom 载体及相等层级独立。
    为回收 Monad 赋予规范广集强度，复用一般 Kleisli 比较及全忠实逆，并将
    两个复合与恒等函子比较。双向保持纯箭头、顺序组合及通常上下文。
    计算范畴按值对象索引，不选择其他环境对象的代表。 *)

(** Give the recovered Monad canonical strength, retaining exactly
    [ArrowMonad] as its underlying Monad. *)

(** 为回收 Monad 赋予规范强度，底层恰好保留 [ArrowMonad]。 *)

Definition ArrowStrongM
  : StrongMonad (SetCat@{u p _ _ _ _ _})
  := SetStrongM ArrowMonad.

(** Rebuild the Arrow using the existing strong-Monad construction. *)

(** 使用已有强 Monad 构造重建 Arrow。 *)

Definition ArrowKleisli
  : Arrow (SetCat@{u p _ _ _ _ _})
      (KleisliCat ArrowMonad)
  := KleisliArrow ArrowStrongM.

(** The general adjunction comparison evaluates dynamic names. Its object
    map is identity on value indices. *)

(** 一般伴随比较求值动态命名，在值索引上的对象映射为恒等。 *)

Definition DynamicEvaluationF
  : Fct (KleisliCat ArrowMonad) (ComputationCat AA)
  := AdjKleisliF ArrowApplyAdj.

(** Reuse the general comparison theorem with computational transpose
    preimages; no native Hom sizes are identified. *)

(** 复用带可计算转置原像的一般比较定理，不等同原生 Hom 大小。 *)

Definition dynamic_evaluation_fully_faithful
  : is_fully_faithful DynamicEvaluationF
  := adj_kleisli_fully_faithful ArrowApplyAdj.

(** Name original computations as reconstructed Kleisli arrows. Both
    functor laws are inherited from the general full-faithful inverse. *)

(** 将原计算命名为重建后的 Kleisli 箭头，两条函子律均继承自一般全忠实逆。 *)

Program Definition DynamicNamingF
  : Fct (ComputationCat AA) (KleisliCat ArrowMonad)
  :=
  {|fobj X := X
  ; fmap X Y f := arrow_dynamic_name AA f
  ; isFct :=
      {|fmap_proper X Y := arrow_dynamic_name_proper AA
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation.
  exact (fmap_id (IsFct := isFct (FullyFaithfulInverseF DynamicEvaluationF
    dynamic_evaluation_fully_faithful)) (X := X)).
Qed.

Next Obligation.
  exact (fmap_comp (IsFct := isFct (FullyFaithfulInverseF DynamicEvaluationF
    dynamic_evaluation_fully_faithful)) f g).
Qed.

(** Evaluation after naming is naturally isomorphic to the original
    indexed computation category identity, with transparent identity maps. *)

(** 先命名再求值自然同构于原索引计算范畴的恒等，比较为透明恒等映射。 *)

Program Definition DynamicEvaluationNamingIso
  : (DynamicEvaluationF ∘F DynamicNamingF) ≅N (@IdF (ComputationCat AA))
  := ({|nt X := id
      |}; _).
Next Obligation.
  change (id ∘ arrow_dynamic_eval (arrow_dynamic_name AA f) ≈ f ∘ id).
  rewrite comp_id_l, comp_id_r. exact (arrow_dynamic_eval_name f).
Qed.

Next Obligation.
  intros X. exists id. split;
    exact (@comp_id_l (ComputationCat AA) _ _ id).
Defined.

(** Naming after evaluation is naturally isomorphic to the Kleisli
    identity. Identity components are the recovered Monad units. *)

(** 先求值再命名自然同构于 Kleisli 恒等，恒等分量是回收 Monad 的单位。 *)

Program Definition DynamicNamingEvaluationIso
  : (DynamicNamingF ∘F DynamicEvaluationF) ≅N
    (@IdF (KleisliCat ArrowMonad))
  := ({|nt X := id
      |}; _).
Next Obligation.
  transitivity (arrow_dynamic_name AA (arrow_dynamic_eval f)).
  - exact (@kleisli_comp_id_l SetCat ArrowMonad X Y
      (arrow_dynamic_name AA (arrow_dynamic_eval f))).
  - transitivity f; [exact (arrow_dynamic_name_eval f)|].
    symmetry. exact (@kleisli_comp_id_r SetCat ArrowMonad X Y f).
Qed.

Next Obligation.
  intros X. exists id. split;
    exact (@comp_id_l (KleisliCat ArrowMonad) _ _ id).
Defined.

(** Naming sends an original pure arrow to reconstructed Monad return. *)

(** 命名将原纯箭头送到重建后的 Monad 返回。 *)

Lemma dynamic_naming_pure {X Y : SetC@{u p}} (f : X →r Y)
  : arrow_dynamic_name AA arr[AA; f] ≈f return[ArrowMonad; f].
Proof.
  intros x. transitivity (arrow_value_pure K AA Y (f x)).
  - change (arr[AA; f] ∘ arr[AA; const[UnitS] x]
      ≈ arr[AA; const[UnitS] (f x)]).
    rewrite <- fmap_comp. apply fmap_proper. intros []. reflexivity.
  - symmetry. exact (arrow_monad_unit Y (f x)).
Qed.

(** Naming preserves left ordinary context by the weaker ordinary-Arrow
    naming law and the canonical strength formula. *)

(** 由较弱的通常 Arrow 命名定律及规范强度公式，命名保持左侧通常上下文。 *)

Lemma dynamic_naming_context {X Y : SetC@{u p}} (Z : SetC@{u p})
    (f : Hom (AA X) (AA Y))
  : arrow_dynamic_name AA (context[AA; Z; f])
    ≈f context[ArrowKleisli; Z; arrow_dynamic_name AA f].
Proof.
  intros [z x]. exact (arrow_dynamic_name_context AA Z f z x).
Qed.

(** Naming preserves sequencing as Kleisli composition, with the original
    execution order. *)

(** 命名将顺序组合保持为 Kleisli 复合，保留原执行次序。 *)

Lemma dynamic_naming_comp {X Y Z : SetC@{u p}}
    (g : Hom (AA Y) (AA Z)) (f : Hom (AA X) (AA Y))
  : arrow_dynamic_name AA (g ∘ f)
    ≈f arrow_dynamic_name AA g ∘K[ArrowMonad] arrow_dynamic_name AA f.
Proof.
  exact (fmap_comp (IsFct := isFct DynamicNamingF) g f).
Qed.

(** Ordinary input substitution commutes with dynamic evaluation. *)

(** 通常输入代入与动态求值交换。 *)

Lemma dynamic_evaluation_pre {X Y Z : SetC@{u p}}
    (f : Y →r ArrowMonad Z) (h : X →r Y)
  : arrow_dynamic_eval (f ∘r h) ≈ arrow_dynamic_eval f ∘ arr[AA; h].
Proof. exact (unadjunct_comp_r ArrowApplyAdj f h). Qed.

(** Evaluation recovers the original pure arrow from reconstructed return. *)

(** 求值从重建后的返回恢复原纯箭头。 *)

Lemma dynamic_evaluation_pure {X Y : SetC@{u p}} (f : X →r Y)
  : arrow_dynamic_eval return[ArrowMonad; f] ≈ arr[AA; f].
Proof.
  transitivity (arrow_dynamic_eval (arrow_dynamic_name AA arr[AA; f])).
  - apply arrow_dynamic_eval_proper. symmetry. exact (dynamic_naming_pure f).
  - exact (arrow_dynamic_eval_name arr[AA; f]).
Qed.

(** Evaluation preserves Kleisli sequencing as original computation
    composition, reusing the comparison functor law. *)

(** 求值将 Kleisli 顺序组合保持为原计算复合，复用比较函子定律。 *)

Lemma dynamic_evaluation_comp {X Y Z : SetC@{u p}}
    (g : Y →r ArrowMonad Z) (f : X →r ArrowMonad Y)
  : arrow_dynamic_eval (g ∘K[ArrowMonad] f)
    ≈ arrow_dynamic_eval g ∘ arrow_dynamic_eval f.
Proof.
  exact (fmap_comp (IsFct := isFct DynamicEvaluationF) g f).
Qed.

(** The inverse comparison also preserves the original ordinary context
    action, by naming preservation and the two reconstruction laws. *)

(** 由命名保持性及两条重建律，逆向比较也保持原通常上下文作用。 *)

Lemma dynamic_evaluation_context {X Y : SetC@{u p}} (Z : SetC@{u p})
    (f : X →r ArrowMonad Y)
  : arrow_dynamic_eval (context[ArrowKleisli; Z; f])
    ≈ context[AA; Z; arrow_dynamic_eval f].
Proof.
  transitivity (arrow_dynamic_eval (arrow_dynamic_name AA
    (context[AA; Z; arrow_dynamic_eval f]))).
  - apply arrow_dynamic_eval_proper. symmetry.
    transitivity (context[ArrowKleisli; Z;
      arrow_dynamic_name AA (arrow_dynamic_eval f)]).
    + exact (dynamic_naming_context Z (arrow_dynamic_eval f)).
    + apply (arrow_context_proper ArrowKleisli Z).
      exact (arrow_dynamic_name_eval f).
  - exact (arrow_dynamic_eval_name _).
Qed.

End DynamicReconstruction.

(** * Preservation of Dynamic Application

    Use a common native carrier/equality bound, as required for the
    reconstructed Kleisli Hom setoids to be input values. Reuse its existing
    ArrowApply model on the exact same strong Monad. The application
    comparisons reindex supplied computations through naming or evaluation;
    both equations use native computation equality. *)

(** * 动态应用的保持性

    使用共同原生载体／相等界，使重建后的 Kleisli Hom 广集能够作为输入值。
    在恰好同一个强 Monad 上复用已有 ArrowApply 模型。应用比较通过命名或求值
    重索引所给计算，两个方程均使用原生计算相等。 *)

Section Application.
Universes o u.
Context {K : Cat@{o u u _ _}} (AA : ArrowApply K).

(** Extend the same reconstructed Arrow by the existing Kleisli application
    model; no second strength or parent Arrow is stored. *)

(** 通过已有 Kleisli 应用模型扩充同一重建 Arrow，不另存强度或父 Arrow。 *)

Definition ArrowKleisliApply
  : ArrowApply (KleisliCat (ArrowMonad AA))
  := KleisliArrowApply (ArrowStrongM AA).

(** Naming preserves application after naming the supplied computation
    value. The ordinary input is retained. *)

(** 命名在命名所给计算值后保持应用，保留通常输入。 *)

Lemma dynamic_naming_apply (X Y : SetC@{u u})
  : arrow_dynamic_name AA apply[AA; X; Y]
    ≈f (apply[ArrowKleisliApply; X; Y] ∘r
      (arrow_dynamic_name_resp AA X Y × id_resp)).
Proof.
  intros [f x].
  change (apply[AA; X; Y] ∘ arr[AA; const[UnitS] (f,x)]
    ≈ f ∘ arr[AA; const[UnitS] x]).
  transitivity (arrow_apply_const AA f ∘ arr[AA; const[UnitS] x]).
  - unfold arrow_apply_const. rewrite comp_assoc, <- fmap_comp.
    apply comp_proper; [reflexivity|].
    apply fmap_proper. intros []. split; reflexivity.
  - rewrite arrow_apply_const_value. reflexivity.
Qed.

(** Evaluation preserves reconstructed application after evaluating the
    supplied computation value, using native Hom equality. *)

(** 求值在求值所给计算值后保持重建应用，使用原生 Hom 相等。 *)

Lemma dynamic_evaluation_apply (X Y : SetC@{u u})
  : arrow_dynamic_eval AA apply[ArrowKleisliApply; X; Y]
    ≈ apply[AA; X; Y] ∘ arr[AA;
      arrow_dynamic_eval_resp AA X Y × id_resp].
Proof.
  transitivity (arrow_dynamic_eval AA
    (arrow_dynamic_name AA apply[AA; X; Y] ∘r
      (arrow_dynamic_eval_resp AA X Y × id_resp))).
  - apply arrow_dynamic_eval_proper. intros [f x].
    change (f x ≈ arrow_dynamic_name AA apply[AA; X; Y]
      (arrow_dynamic_eval AA f,x)).
    symmetry. transitivity (arrow_dynamic_name AA (arrow_dynamic_eval AA f) x).
    + exact (dynamic_naming_apply X Y (arrow_dynamic_eval AA f,x)).
    + exact (arrow_dynamic_name_eval AA f x).
  - transitivity (arrow_dynamic_eval AA
      (arrow_dynamic_name AA apply[AA; X; Y])
        ∘ arr[AA; arrow_dynamic_eval_resp AA X Y × id_resp]).
    + exact (dynamic_evaluation_pre AA _ _).
    + apply comp_proper; [exact (arrow_dynamic_eval_name AA _)|reflexivity].
Qed.

End Application.

(** * Applicative Compatibility of Dynamic Reconstruction

    Fix a native-setoid ArrowApply with independent computation-object,
    Hom carrier and equality levels. Naming preserves the derived ordered
    operations by its already proved pure, composition and context laws.
    Its terminal-input specialization identifies the Monad-derived
    Applicative pairing with the original Arrow pairing. The existing
    underlying natural isomorphism preserves Applicative operations in
    both directions; no closed structure or common native size is needed. *)

(** * 动态重建的 Applicative 相容性

    固定原生广集上的 ArrowApply，保持计算对象、Hom 载体与相等层级独立。
    命名通过已有纯箭头、复合及上下文律保持导出的有序运算。其终输入特化将
    Monad 导出的 Applicative 配对与原 Arrow 配对相识别。已有底层自然同构
    双向保持 Applicative 运算，不需要闭结构或共同原生大小。 *)

Section ApplicativeComparison.
Universes o u p.
Context {K : Cat@{o u p _ _}} (AA : ArrowApply K).

(** Naming preserves right context, since exchange is a pure arrow. *)

(** 交换为纯箭头，因此命名保持右上下文。 *)

Lemma dynamic_naming_first {X Y : SetC@{u p}} (Z : SetC@{u p})
    (f : Hom (AA X) (AA Y))
  : arrow_dynamic_name AA first[AA; f; Z]
    ≈f first[ArrowKleisli AA; arrow_dynamic_name AA f; Z].
Proof.
  change (@HomEq (KleisliCat (ArrowMonad AA)) (X ×S Z) (Y ×S Z)
    (fmap (DynamicNamingF AA) first[AA; f; Z])
    first[ArrowKleisli AA; arrow_dynamic_name AA f; Z]).
  unfold arrow_first, arrow_second.
  etransitivity.
  - exact (fmap_comp (IsFct := isFct (DynamicNamingF AA)) _ _).
  - apply (@comp_proper (KleisliCat (ArrowMonad AA))
      (X ×S Z) (Z ×S X) (Y ×S Z)).
    + etransitivity.
      * exact (fmap_comp (IsFct := isFct (DynamicNamingF AA)) _ _).
      * apply (@comp_proper (KleisliCat (ArrowMonad AA))
          (Z ×S X) (Z ×S Y) (Y ×S Z)).
        -- exact (dynamic_naming_pure AA _).
        -- exact (dynamic_naming_context AA Z f).
    + exact (dynamic_naming_pure AA _).
Qed.

(** Ordered splitting is preserved without exchanging its two effects. *)

(** 保持有序 split，不交换其中两个效应。 *)

Lemma dynamic_naming_split {X Y X' Y' : SetC@{u p}}
    (f : Hom (AA X) (AA Y)) (g : Hom (AA X') (AA Y'))
  : arrow_dynamic_name AA (f ***[AA] g)
    ≈f (arrow_dynamic_name AA f ***[ArrowKleisli AA] arrow_dynamic_name AA g).
Proof.
  change (@HomEq (KleisliCat (ArrowMonad AA)) (X ×S X') (Y ×S Y')
    (fmap (DynamicNamingF AA) (f ***[AA] g))
    (arrow_dynamic_name AA f ***[ArrowKleisli AA] arrow_dynamic_name AA g)).
  unfold arrow_split, arrow_second.
  etransitivity.
  - exact (fmap_comp (IsFct := isFct (DynamicNamingF AA)) _ _).
  - apply (@comp_proper (KleisliCat (ArrowMonad AA))
      (X ×S X') (Y ×S X') (Y ×S Y')).
    + exact (dynamic_naming_context AA Y g).
    + exact (dynamic_naming_first X' f).
Qed.

(** Pure copying and ordered splitting give the fanout comparison in every
    shared ordinary input, not only at terminal input. *)

(** 纯复制与有序 split 在每个共同通常输入处给出 fanout 比较，不限于终输入。 *)

Lemma dynamic_naming_fanout {W X Y : SetC@{u p}}
    (f : Hom (AA W) (AA X)) (g : Hom (AA W) (AA Y))
  : arrow_dynamic_name AA (f &&&[AA] g)
    ≈f (arrow_dynamic_name AA f &&&[ArrowKleisli AA] arrow_dynamic_name AA g).
Proof.
  change (@HomEq (KleisliCat (ArrowMonad AA)) W (X ×S Y)
    (fmap (DynamicNamingF AA) (f &&&[AA] g))
    (arrow_dynamic_name AA f &&&[ArrowKleisli AA] arrow_dynamic_name AA g)).
  unfold arrow_fanout.
  etransitivity.
  - exact (fmap_comp (IsFct := isFct (DynamicNamingF AA)) _ _).
  - apply (@comp_proper (KleisliCat (ArrowMonad AA)) W (W ×S W) (X ×S Y)).
    + exact (dynamic_naming_split f g).
    + exact (dynamic_naming_pure AA _).
Qed.

(** Both Applicatives have the same global-computation values. Reuse the
    identity-component comparison of the recovered Monad's functor. *)

(** 两个 Applicative 具有相同全局计算值；复用回收 Monad 函子的恒等分量比较。 *)

Definition DynamicApplicativeIso
  : MonadA (ArrowStrongM AA) ≅N ArrowA K AA
  := ArrowMonadUnderlyingIso AA.

(** Use the operation laws while leaving their computations abstract;
    transparency is restored before exposing clients. *)

(** 使用运算定律，同时保持其计算抽象；暴露客户端前恢复透明性。 *)

Local Opaque monad_pair arrow_fanout.

(** Pair abstract global computations before specializing to computations
    stored inside lifted products. Specialize the general Kleisli fanout
    comparison and cancel naming at terminal input. *)

(** 先配对抽象全局计算，再特化到存于提升积中的计算。特化一般 Kleisli fanout
    比较，并消去终输入处的命名。 *)

Lemma dynamic_applicative_pair (X Y : SetC@{u p})
    (f : ArrowGlobalF AA X) (g : ArrowGlobalF AA Y)
  : φ₂[MonadA (ArrowStrongM AA); X; Y] (f,g)
    ≈S φ₂[ArrowA K AA; X; Y] (f,g).
Proof.
  symmetry.
  pose (nf := @arrow_dynamic_name K AA UnitS X f).
  pose (ng := @arrow_dynamic_name K AA UnitS Y g).
  transitivity (@arrow_dynamic_name K AA UnitS (X ×S Y)
    (f &&&[AA] g) tt).
  + symmetry. exact (@arrow_dynamic_name_global K AA (X ×S Y) _).
  + transitivity ((nf &&&[ArrowKleisli AA] ng) tt).
    * exact (@dynamic_naming_fanout UnitS X Y f g tt).
    * transitivity (monad_pair (ArrowStrongM AA) (nf tt,ng tt)).
      -- exact (@kleisli_arrow_fanout SetCat (CartCatToHasCartesian SetCat_Cart)
           (ArrowStrongM AA) UnitS X Y nf ng tt).
      -- apply func_proper. split;
           [exact (@arrow_dynamic_name_global K AA X f)|
            exact (@arrow_dynamic_name_global K AA Y g)].
Qed.

(** The direct and recovered routes preserve pure and ordered pairing,
    using the preceding abstract-value comparison. *)

(** 直接路径与回收路径通过前面的抽象值比较，保持纯值与有序配对。 *)

Lemma dynamic_applicative_hom
  : is_applicative_hom (MonadA (ArrowStrongM AA)) (ArrowA K AA)
      DynamicApplicativeIso.1.
Proof.
  split.
  - intros X x. exact (arrow_monad_unit AA X x).
  - intros X Y.
    change (@HomEq SetCat (ArrowGlobalF AA X ×S ArrowGlobalF AA Y)
      (ArrowGlobalF AA (X ×S Y))
      (id_resp ∘r φ₂[MonadA (ArrowStrongM AA); X; Y])
      (φ₂[ArrowA K AA; X; Y] ∘r
        (id[ArrowGlobalF AA X] × id[ArrowGlobalF AA Y]))).
    rewrite (@comp_id_l SetCat), cross_id,
      (@comp_id_r SetCat).
    intros [f g]. exact (dynamic_applicative_pair X Y f g).
Qed.

(** The same chosen natural inverse preserves both operations by the
    general inverse theorem, without another calculation of Monad pairing. *)

(** 同一个选定自然逆由一般求逆定理保持两种运算，无需再次计算 Monad 配对。 *)

Lemma dynamic_applicative_inverse_hom
  : is_applicative_hom (ArrowA K AA) (MonadA (ArrowStrongM AA))
      (DynamicApplicativeIso.1 ^-1N DynamicApplicativeIso.2).
Proof.
  exact (applicative_hom_inverse _ _ _ dynamic_applicative_hom
    DynamicApplicativeIso.2).
Qed.

Local Transparent monad_pair arrow_fanout.

End ApplicativeComparison.

Local Transparent CartHasMonoidal.
