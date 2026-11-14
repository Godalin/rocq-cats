From Cats Require Export
  Cat.Functor.Core
  Cat.Functor.Product
  Cat.Natural.
From Cats Require Import
  Cat.Core
  Instance.Set.Core.

(** * Setoid-Valued Profunctors

    A profunctor is exactly an existing mixed-variance functor: contravariant
    in its input category and covariant in its output category. Reuse that
    bundle and its object-map coercion; no second data or law record is
    introduced. Value carriers and equality witnesses remain independent. *)

(** * 广集值 Profunctor

    Profunctor 恰为已有的混合变元函子：输入范畴反变，输出范畴协变。复用该
    打包及对象映射强制转换，不新增第二份数据或定律记录。值载体与相等见证
    的层级保持独立。 *)

Definition Profunctor@{u p +} (C D : Cat)
  : Type
  := Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _}).

(** Ordinary natural transformations and their designated pointwise equality
    already form the required category; neither ends nor coends are needed. *)

(** 通常自然变换及其指定逐点相等已组成所需范畴，不要求 end 或 coend。 *)

Definition ProfunctorCat@{u p +} (C D : Cat)
  : Cat
  := FctCat ((C^op) ×C D) (SetCat@{u p _ _ _ _ _}).

Declare Scope profunctor_scope.
Delimit Scope profunctor_scope with profunctor.

(** Preprocess an input and postprocess an output. The input arrow points
    from the new input to the old input. Respectfulness is inherited. *)

(** 预处理输入并后处理输出；输入箭头从新输入指向旧输入，尊重性由函子继承。 *)

Definition profunctor_dimap {C D : Cat} (P : Fct ((C^op) ×C D) SetCat)
    {X X' : @Ob C} {Y Y' : @Ob D} (f : Hom X' X) (g : Hom Y Y')
  : P (X,Y) →r P (X',Y')
  := fmap P (X := (X,Y)) (Y := (X',Y')) (f,g).

Notation "'dimap[' P ';' f ';' g ']'" := (profunctor_dimap P f g)
  : profunctor_scope.
Local Open Scope profunctor_scope.

(** Input-only action keeps the output object fixed. *)

(** 仅输入作用保持输出对象不变。 *)

Definition profunctor_lmap {C D : Cat} (P : Fct ((C^op) ×C D) SetCat)
    {Y : @Ob D} {X X' : @Ob C} (f : Hom X' X)
  : P (X,Y) →r P (X',Y)
  := dimap[P; f; @Cat.Core.id D Y].

Notation "'lmap[' P ';' f ']'" := (profunctor_lmap P f)
  : profunctor_scope.

(** Output-only action keeps the input object fixed. *)

(** 仅输出作用保持输入对象不变。 *)

Definition profunctor_rmap {C D : Cat} (P : Fct ((C^op) ×C D) SetCat)
    {X : @Ob C} {Y Y' : @Ob D} (g : Hom Y Y')
  : P (X,Y) →r P (X,Y')
  := dimap[P; @Cat.Core.id C X; g].

Notation "'rmap[' P ';' g ']'" := (profunctor_rmap P g)
  : profunctor_scope.

(** ** Acting on Input and Output Arrows

    Fix a profunctor between named categories. Read the two-variable action
    from its existing functor map. One-sided restrictions and interchange
    reuse the product-coordinate theory, without new naturality axioms. *)

(** ** 对输入与输出箭头的作用

    固定具名范畴间的 profunctor，从已有函子映射读取双变量作用。单侧限制及
    交换律复用积坐标理论，不增加新的自然性公理。 *)

Section Actions.
Universes u p.
Context {C D : Cat} (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).

(** Changing either arrow by specified equality changes no result. *)

(** 将任一箭头换为指定相等的箭头，不改变结果。 *)

Global Instance profunctor_dimap_proper {X X' : @Ob C} {Y Y' : @Ob D}
  : Proper (@HomEq C X' X ==> @HomEq D Y Y' ==> FunEq)
      (@profunctor_dimap C D P X X' Y Y').
Proof.
  intros f f' E g g' H.
  apply (@functor_fmap_proper _ _ P _ _). split; assumption.
Defined.

(** Identity preprocessing and postprocessing leave the value unchanged. *)

(** 恒等预处理及后处理保持值不变。 *)

Lemma profunctor_dimap_id (X : @Ob C) (Y : @Ob D)
  : dimap[P; @Cat.Core.id C X; @Cat.Core.id D Y] ≈f id_resp.
Proof. exact (@functor_id _ _ P (X,Y)). Defined.

(** Input composition reverses its action order; output composition keeps
    its ordinary order. Both are the original product-functor law. *)

(** 输入复合反转作用顺序，输出复合保持通常顺序；二者均为原积函子定律。 *)

Lemma profunctor_dimap_comp {X X' X'' : @Ob C} {Y Y' Y'' : @Ob D}
    (f : Hom X' X) (f' : Hom X'' X') (g : Hom Y Y') (g' : Hom Y' Y'')
  : dimap[P; f ∘ f'; g' ∘ g] ≈f (dimap[P; f'; g'] ∘r dimap[P; f; g]).
Proof.
  exact (@functor_comp ((C^op) ×C D) SetCat P
    (X,Y) (X',Y') (X'',Y'') (f',g') (f,g)).
Defined.

(** An input arrow gives a natural comparison of the output diagrams. *)

(** 输入箭头给出输出图式的自然比较。 *)

Definition ProfunctorLmapN {X X' : @Ob C} (f : Hom X' X)
  : π2F P X ⇒ π2F P X'
  := ProductFirstAtN P f.

(** An output arrow gives a natural comparison of the input diagrams. *)

(** 输出箭头给出输入图式的自然比较。 *)

Definition ProfunctorRmapN {Y Y' : @Ob D} (g : Hom Y Y')
  : π1F P Y ⇒ π1F P Y'
  := ProductAtN P g.

(** The input restriction respects specified arrow equality. *)

(** 输入限制保持指定箭头相等。 *)

Global Instance profunctor_lmap_proper {Y : @Ob D} {X X' : @Ob C}
  : Proper (@HomEq C X' X ==> FunEq) (@profunctor_lmap C D P Y X X').
Proof.
  intros f f' E. apply profunctor_dimap_proper; [exact E|reflexivity].
Defined.

(** The output restriction respects specified arrow equality. *)

(** 输出限制保持指定箭头相等。 *)

Global Instance profunctor_rmap_proper {X : @Ob C} {Y Y' : @Ob D}
  : Proper (@HomEq D Y Y' ==> FunEq) (@profunctor_rmap C D P X Y Y').
Proof.
  intros g g' E. apply profunctor_dimap_proper; [reflexivity|exact E].
Defined.

(** Identity input action is the identity map. *)

(** 恒等输入作用为恒等映射。 *)

Lemma profunctor_lmap_id (X : @Ob C) (Y : @Ob D)
  : lmap[P; @Cat.Core.id C X] ≈f (@Cats.Set.Morphism.id_resp (P (X,Y))).
Proof. exact (profunctor_dimap_id X Y). Defined.

(** Identity output action is the identity map. *)

(** 恒等输出作用为恒等映射。 *)

Lemma profunctor_rmap_id (X : @Ob C) (Y : @Ob D)
  : rmap[P; @Cat.Core.id D Y] ≈f (@Cats.Set.Morphism.id_resp (P (X,Y))).
Proof. exact (profunctor_dimap_id X Y). Defined.

(** Preprocessing is contravariantly functorial. *)

(** 预处理具有反变函子性。 *)

Lemma profunctor_lmap_comp {X X' X'' : @Ob C} (Y : @Ob D)
    (f : Hom X' X) (f' : Hom X'' X')
  : lmap[P; f ∘ f'] ≈f (lmap[P; f'] ∘r (@profunctor_lmap C D P Y _ _ f)).
Proof.
  exact (@functor_comp (C^op) SetCat (π1F P Y) X X' X'' f' f).
Defined.

(** Postprocessing is covariantly functorial. *)

(** 后处理具有协变函子性。 *)

Lemma profunctor_rmap_comp (X : @Ob C) {Y Y' Y'' : @Ob D}
    (g : Hom Y Y') (g' : Hom Y' Y'')
  : rmap[P; g' ∘ g] ≈f (rmap[P; g'] ∘r (@profunctor_rmap C D P X _ _ g)).
Proof.
  exact (@functor_comp D SetCat (π2F P X) Y Y' Y'' g' g).
Defined.

(** The two actions commute by naturality of the input comparison. *)

(** 两个作用由输入比较的自然性交换。 *)

Lemma profunctor_interchange {X X' : @Ob C} {Y Y' : @Ob D}
    (f : Hom X' X) (g : Hom Y Y')
  : (lmap[P; f] ∘r rmap[P; g]) ≈f (rmap[P; g] ∘r lmap[P; f]).
Proof. exact (nt_naturality (ProfunctorLmapN f) g). Defined.

(** A two-sided action first postprocesses, then preprocesses. *)

(** 双侧作用可先后处理，再预处理。 *)

Lemma profunctor_dimap_l_r {X X' : @Ob C} {Y Y' : @Ob D}
    (f : Hom X' X) (g : Hom Y Y')
  : dimap[P; f; g] ≈f (lmap[P; f] ∘r rmap[P; g]).
Proof. exact (product_at_map P f g). Defined.

(** The commuting actions also allow the reverse evaluation order. *)

(** 交换的两个作用也允许相反求值顺序。 *)

Lemma profunctor_dimap_r_l {X X' : @Ob C} {Y Y' : @Ob D}
    (f : Hom X' X) (g : Hom Y Y')
  : dimap[P; f; g] ≈f (rmap[P; g] ∘r lmap[P; f]).
Proof.
  rewrite profunctor_dimap_l_r. exact (profunctor_interchange f g).
Defined.

End Actions.

(** ** Natural Transformations and Reindexing

    Keep the same value carrier/equality levels. A profunctor transformation
    is the existing natural transformation. Reindex both categories using
    ordinary composition and opposite/product functors; no coends or
    relation between the two categories' sizes are imposed. *)

(** ** 自然变换与重索引

    保持相同值载体／相等层级，profunctor 变换就是已有自然变换。使用通常复合、
    反函子及积函子在两个范畴上重索引，不要求 coend 或两范畴大小间的次序。 *)

Section Reindexing.
Universes u p.
Context {C D C' D' : Cat}.
Context (F : Fct C' C) (G : Fct D' D).

(** Precompose independently in both arguments. *)

(** 独立地在两个变元上预合成。 *)

Definition ProfunctorReindex (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _}))
  : Profunctor C' D'
  := P ∘F (F^opF ×F G).

(** Reindexed action is the original action on the two mapped arrows. *)

(** 重索引后的作用，是原作用施于两个映射后的箭头。 *)

Lemma profunctor_reindex_dimap
    (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _}))
    {X X' : @Ob C'} {Y Y' : @Ob D'} (f : Hom X' X) (g : Hom Y Y')
  : dimap[ProfunctorReindex P; f; g] ≈f dimap[P; fmap F f; fmap G g].
Proof. reflexivity. Defined.

(** Reindex transformations by the existing right whiskering operation. *)

(** 通过已有右须化运算重索引变换。 *)

Definition ProfunctorReindexN
    {P Q : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})} (α : P ⇒ Q)
  : ProfunctorReindex P ⇒ ProfunctorReindex Q
  := α ∘Nr (F^opF ×F G).

(** Right whiskering retains chosen natural inverses. *)

(** 右须化保留选定自然逆。 *)

Definition profunctor_reindex_iso
    {P Q : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})}
    (α : P ⇒ Q) (Hα : α ⦂ P ≅N Q)
  : ProfunctorReindexN α ⦂ ProfunctorReindex P ≅N ProfunctorReindex Q
  := nt_whisker_r_NatIso α (F^opF ×F G) Hα.

(** Restrict the existing horizontal-composition functor at this precomposition.
    Its laws and specified equality come from that functor category. *)

(** 在此预合成处限制已有水平复合函子；其定律及指定相等来自该函子范畴。 *)

Definition ProfunctorReindexF
  : Fct (ProfunctorCat C D) (ProfunctorCat C' D')
  := π1F (CompNF ((C'^op) ×C D') ((C^op) ×C D) (SetCat@{u p _ _ _ _ _}))
      (F^opF ×F G).

(** The inherited functor action agrees with right whiskering in natural
    equality; the comparison does not identify transformation records. *)

(** 继承的函子作用按自然相等与右须化一致，不识别变换记录。 *)

Lemma profunctor_reindex_map
    {P Q : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})} (α : P ⇒ Q)
  : fmap ProfunctorReindexF α ≈N ProfunctorReindexN α.
Proof.
  intros [X Y] h.
  change (α (F X,G Y) (fmap P
    (@Cat.Core.id ((C^op) ×C D) (F X,G Y)) h) ≈S α (F X,G Y) h).
  apply (@func_proper _ _ (α (F X,G Y))).
  exact (@functor_id _ _ P (F X,G Y) h).
Defined.

End Reindexing.

(** Natural transformations commute with the two-sided action, on the same
    underlying component family. No separate profunctor homomorphism is
    stored. *)

(** 自然变换与双侧作用交换，沿用同一底层分量族；不另存 profunctor 同态。 *)

Lemma profunctor_natural {C D : Cat} {P Q : Fct ((C^op) ×C D) SetCat}
    (α : P ⇒ Q) {X X' : @Ob C} {Y Y' : @Ob D}
    (f : Hom X' X) (g : Hom Y Y')
  : (α (X',Y') ∘r dimap[P; f; g]) ≈f (dimap[Q; f; g] ∘r α (X,Y)).
Proof. exact (nt_naturality α (X := (X,Y)) (Y := (X',Y')) (f,g)). Defined.
