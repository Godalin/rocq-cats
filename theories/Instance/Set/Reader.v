From Cats Require Import
  Cat.Applicative.Core
  Instance.Set.Core
  Instance.Set.Terminal
  Instance.Set.Product
  Instance.Set.Monoid.

(** * The Reader Applicative on Setoids

    Postcomposition of respectful maps reads one shared environment.
    Pure values ignore it, and binary combination uses it in both inputs.
    All structures are explicitly selected and all maps remain transparent. *)

(** * 广集上的 Reader Applicative

    保相等映射的后合成读取同一个环境。纯值忽略环境，二元组合将同一环境用于
    两个输入。所有结构均须显式选择，全部映射保持透明。 *)

Local Open Scope monoidal_scope.

(** Postcomposition reuses respectful-map composition and its existing
    laws. The environment's equality level remains separate; the ambient
    carrier may be strictly larger than its equality-witness universe. *)

(** 后合成复用保相等映射复合及其已有定律。环境的相等层级单独保留，所在广集的
    载体宇宙可严格大于相等见证宇宙。 *)

Program Definition ReaderF@{r e u p +} (R : SetC@{r e})
  : Functor (SetCat@{u p _ _ _ _ _}) (SetCat@{u p _ _ _ _ _})
  :=
  {|F0 X := R →S X
  ; F1 X Y f := {|func g := f ∘r g|}
  |}.
Next Obligation.
  intros g g' H. apply comp_resp_proper; [reflexivity | exact H].
Defined.
Next Obligation. intros f g H k r. exact (H (k r)). Defined.
Next Obligation. intros f. apply comp_resp_id_l. Defined.
Next Obligation. intros k. apply comp_resp_assoc. Defined.

(** A constant respectful function gives a pure reader value. *)

(** 常值保相等函数给出 Reader 纯值。 *)

Program Definition reader_pure@{r e u p +}
    (R : SetC@{r e}) (X : SetC@{u p})
  : X →r (R →S X)
  :=
  {|func x := {|func _ := x|}
  |}.
Next Obligation. intros r r' H. reflexivity. Defined.
Next Obligation. intros x x' H r. exact H. Defined.

(** Pair the outputs of two readers in their common environment. *)

(** 将同一环境下两个 Reader 的输出配对。 *)

Program Definition reader_pair@{r e u p +}
    (R : SetC@{r e}) (X Y : SetC@{u p})
  : ((R →S X) ×S (R →S Y)) →r (R →S (X ×S Y))
  :=
  {|func p := {|func r := (fst p r, snd p r)|}
  |}.
Next Obligation.
  intros r r' H. split; apply func_proper; exact H.
Defined.
Next Obligation.
  intros [f g] [f' g'] [H K] r. split; [exact (H r) | exact (K r)].
Defined.

(** Pointwise pairing is the reader's natural tensorator. *)

(** 逐点配对就是 Reader 的自然 tensorator。 *)

Program Definition ReaderTensorN@{r e u p +} (R : SetC@{r e})
  : (tensorF SetCartesianMonoidal ∘F
      (ReaderF@{r e u p _ _ _ _ _ _ _} R ×F ReaderF R)) ⇒
      (ReaderF R ∘F tensorF SetCartesianMonoidal)
  :=
  {|nt p := reader_pair R (fst p) (snd p)
  |}.
Next Obligation.
  destruct X as [P Q], Y as [P' Q'], f as [f g].
  intros [a b] r. split; reflexivity.
Defined.

(** The reader lax structure uses the existing cartesian monoidal model. *)

(** Reader 的 lax 结构使用已有笛卡尔幺半模型。 *)

Program Definition ReaderLax@{r e u p +} (R : SetC@{r e})
  : LaxMonoidalFunctor (C := SetCat@{u p _ _ _ _ _})
      (D := SetCat@{u p _ _ _ _ _})
      SetCartesianMonoidal SetCartesianMonoidal
  :=
  {|LaxMonoidalF := ReaderF R
  ; lax_unit := reader_pure R UnitS
  ; lax_tensorN := ReaderTensorN R
  |}.
Next Obligation.
  intros [[] f] r. reflexivity.
Defined.
Next Obligation.
  intros [f []] r. reflexivity.
Defined.
Next Obligation.
  intros [[f g] h] r. split; [reflexivity |].
  split; reflexivity.
Defined.

(** The pure readers form a natural transformation. *)

(** Reader 纯值组成自然变换。 *)

Program Definition ReaderPureN@{r e u p +} (R : SetC@{r e})
  : IdF ⇒ ReaderF@{r e u p _ _ _ _ _ _ _} R
  :=
  {|nt X := reader_pure R X
  |}.
Next Obligation. intros x r. reflexivity. Defined.

(** Explicitly choose the lawful reader Applicative [ReaderA]. Pin the
    ambient levels independently of the environment throughout its data. *)

(** 显式选择带定律的 Reader Applicative [ReaderA]，在全部数据中固定独立于
    环境的所在层级。 *)

Program Definition ReaderA@{r e u p +} (R : SetC@{r e})
  : Applicative (SetCat@{u p _ _ _ _ _})
      SetCat_HasTerminal SetCat_HasProduct
  :=
  {|ApplicativeLax := ReaderLax R
  ; applicative_pure := ReaderPureN R
  |}.
Next Obligation. intros [] r. reflexivity. Defined.
Next Obligation. intros [x y] r. split; reflexivity. Defined.
