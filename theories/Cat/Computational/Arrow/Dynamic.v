From Cats Require Export
  Cat.Computational.Arrow.Apply
  Cat.Computational.Arrow.Global.
From Cats Require Import
  Cat.Isomorphism
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product.
From Cats.Set Require Import
  Constant.
Import Cats.Cat.Core Cats.Cat.Product.Core.

Local Open Scope computation_scope.
Local Existing Instance SetCat_HasTerminal.
Local Existing Instance SetCat_HasProduct.

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
    (A : Arrow (SetCat@{u p _ _ _ _ _}) K
      (@CartesianMonoidal SetCat SetCat_HasTerminal SetCat_HasProduct)).

(** Substitute each ordinary input purely into the computation. *)

(** 将每个通常输入纯地代入计算。 *)

Program Definition arrow_dynamic_name {X Y : SetC@{u p}}
    (f : Hom (A X) (A Y))
  : X →r ArrowGlobalF A Y
  :=
  {|func x := f ∘ arr[A; const_resp UnitS x]
  |}.
Next Obligation.
  intros x x' H. apply comp_proper; [reflexivity |].
  apply functor_fmap_proper. intros z. exact H.
Defined.

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
  : arrow_dynamic_name (f ∘ arr[A; h]) ≈f
      (arrow_dynamic_name f ∘r h).
Proof.
  intros x. change ((f ∘ arr[A; h]) ∘ arr[A; const_resp UnitS x] ≈
    f ∘ arr[A; const_resp UnitS (h x)]).
  rewrite comp_assoc, <- functor_comp. apply comp_proper;
    [reflexivity |]. apply functor_fmap_proper. intros []. reflexivity.
Qed.

(** An arbitrary following computation postcomposes every named value. *)

(** 任意后续计算后合成每个命名值。 *)

Lemma arrow_dynamic_name_post {X Y Z : SetC@{u p}}
    (f : Hom (A X) (A Y)) (k : Hom (A Y) (A Z))
  : arrow_dynamic_name (k ∘ f) ≈f
      (comp_l_resp (f := k) ∘r arrow_dynamic_name f).
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

(** Naming a computation with ordinary context pairs the fixed context
    with its named result. Invert the pure unit-context square; only an
    ordinary Arrow is needed, with no dynamic application or Monad. *)

(** 命名带通常上下文的计算，等于将固定上下文配到命名结果旁。对纯单位上下文
    方块取逆即可证明，仅要求通常 Arrow，不使用动态应用或 Monad。 *)

Lemma arrow_dynamic_name_context {X Y : SetC@{u p}} (Z : SetC@{u p})
    (f : Hom (A X) (A Y)) (z : Z) (x : X)
  : arrow_dynamic_name (context[A; Z; f]) (z,x) ≈
    fmap (ArrowGlobalF A) ⟨const_resp Y z, id⟩ (arrow_dynamic_name f x).
Proof.
  change (second[A; f; Z] ∘ arr[A; const_resp UnitS (z,x)] ≈
    arr[A; ⟨const_resp Y z, id⟩] ∘
      (f ∘ arr[A; const_resp UnitS x])).
  pose proof (iso_square_inv
    (arr[A; (π2 : UnitS ×S X →r X)];
      functor_is_iso A _ (@tensor_unit_l_iso SetCat
        (@CartesianMonoidal SetCat SetCat_HasTerminal SetCat_HasProduct) X))
    (arr[A; (π2 : UnitS ×S Y →r Y)];
      functor_is_iso A _ (@tensor_unit_l_iso SetCat
        (@CartesianMonoidal SetCat SetCat_HasTerminal SetCat_HasProduct) Y))
    (second[A; f; UnitS]) f (arrow_context_unit A f)) as Hu.
  change (arr[A; (⟨!,id⟩ : Y →r UnitS ×S Y)] ∘ f ≈
    second[A; f; UnitS] ∘ arr[A; (⟨!,id⟩ : X →r UnitS ×S X)]) in Hu.
  transitivity (arr[A; const_resp UnitS z × (id_resp (X := Y))] ∘
    (second[A; f; UnitS] ∘ arr[A; (⟨!,id⟩ : X →r UnitS ×S X)]) ∘
      arr[A; const_resp UnitS x]).
  - symmetry. rewrite <- !comp_assoc, arrow_second_natural, !comp_assoc,
      <- !functor_comp. apply comp_proper; [reflexivity|].
    apply functor_fmap_proper. intros []. split; reflexivity.
  - rewrite <- Hu, <- !comp_assoc, <- functor_comp, !comp_assoc.
    apply comp_proper; [|reflexivity]. apply functor_fmap_proper.
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

Section Evaluation.
Universes o u p.
Context {K : Cat@{o u p _ _}} (AA : ArrowApply K).

(** A following computation may run after pairing or inside the
    dynamically supplied arrow. *)

(** 后续计算可在配对后运行，也可位于动态提供的箭头内部。 *)

Lemma arrow_apply_pair_post {X Y Z : SetC@{u p}}
    (k : Hom (AA (X ×S Y)) (AA Z))
  : apply[AA; Y; Z] ∘ arr[AA;
      (comp_l_resp (f := k) ∘r arrow_apply_pair AA X Y) × id_resp] ≈ k.
Proof.
  transitivity ((apply[AA; Y; Z] ∘
    arr[AA; comp_l_resp (f := k) × id_resp]) ∘
      arr[AA; arrow_apply_pair AA X Y × id_resp]).
  - rewrite comp_assoc, <- functor_comp. apply comp_proper;
      [reflexivity |]. apply functor_fmap_proper. intros [x y].
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

Global Instance arrow_dynamic_eval_proper {X Y : SetC@{u p}}
  : Proper (@HomEq SetCat X (ArrowGlobalF AA Y) ==> HomEq)
      (@arrow_dynamic_eval X Y).
Proof.
  intros f g H. unfold arrow_dynamic_eval. apply comp_proper;
    [reflexivity |]. apply functor_fmap_proper. intros x.
  split; [exact (H x)|exact tt].
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
    (comp_l_resp (f := k) ∘r arrow_apply_pair AA X UnitS) × id_resp]) ∘
      arr[AA; j]).
  - unfold arrow_dynamic_eval.
    rewrite comp_assoc, <- functor_comp. apply comp_proper;
      [reflexivity |]. apply functor_fmap_proper. intros x. split.
    + change (f ∘ arr[AA; const_resp UnitS x] ≈
        (f ∘ arr[AA; q]) ∘ arr[AA; ⟨const_resp UnitS x, id⟩]).
      rewrite comp_assoc, <- functor_comp. apply comp_proper;
        [reflexivity |]. apply functor_fmap_proper. intros []. reflexivity.
    + exact tt.
  - rewrite arrow_apply_pair_post. unfold k.
    rewrite comp_assoc, <- functor_comp.
    transitivity (f ∘ arr[AA; id_resp (X := X)]).
    + apply comp_proper; [reflexivity |]. apply functor_fmap_proper.
      intros x. reflexivity.
    + rewrite functor_id, comp_id_r. reflexivity.
Qed.

(** Naming the evaluated computation returns the supplied name pointwise. *)

(** 命名求值后的计算，逐点返回所给命名。 *)

Lemma arrow_dynamic_name_eval {X Y : SetC@{u p}}
    (f : X →r ArrowGlobalF AA Y)
  : arrow_dynamic_name AA (arrow_dynamic_eval f) ≈f f.
Proof.
  intros x. unfold arrow_dynamic_name, arrow_dynamic_eval. cbn [func].
  rewrite comp_assoc, <- functor_comp.
  transitivity (arrow_apply_const AA (f x)).
  - unfold arrow_apply_const. apply comp_proper; [reflexivity |].
    apply functor_fmap_proper. intros []. split; [reflexivity|exact tt].
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

End Evaluation.
