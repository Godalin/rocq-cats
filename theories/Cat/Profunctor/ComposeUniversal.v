From Cats Require Export
  Cat.Profunctor.Compose.
From Cats Require Import
  Cat.Core
  Instance.Set.Core
  Instance.Set.Product.

Local Open Scope profunctor_scope.

(** * Generators and Descent of Profunctor Composition

    A value pair is inserted at its intermediate object. The coend glues
    output substitution in [P] to input substitution in [Q]. At fixed outer
    boundaries only that single coend is needed, not a complete family. *)

(** * Profunctor 复合的生成元与下降

    值对在其中间对象处注入，coend 将 [P] 的输出代入与 [Q] 的输入代入粘合。
    固定外部边界时只需该单个 coend，不要求完整核族。 *)

(** Retain the original coend injection as a respectful map on value pairs. *)

(** 保留原 coend 注入作为值对上的尊重映射。 *)

Definition profunctor_comp_inject@{u p +} {C D E : Cat}
    (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _}))
    (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _}))
    {X : @Ob C} {Z : @Ob E}
    `{HC : !HasCoend SetCat (ProfunctorCompKernel Q P X Z)} (Y : @Ob D)
  : (P (X,Y) ×S Q (Y,Z)) →r coend[ProfunctorCompKernel Q P X Z]
  := ιcoend[ProfunctorCompKernel Q P X Z] Y.

Notation "'ιPr[' Q ';' P ';' Y ']'" := (profunctor_comp_inject Q P Y)
  : profunctor_scope.

(** ** Fixed-Boundary Generators

    Fix just one selected kernel coend. Its cowedge and universal mediator
    supply gluing, extensionality and transparent descent for all respectful
    balanced operations, with the existing Type-valued witnesses. *)

(** ** 固定边界生成元

    只固定一个选定核 coend，其余楔及泛中介为全部尊重的平衡操作提供粘合、
    外延性及透明下降，使用已有 Type 值见证。 *)

Section Generators.
Universes u p.
Context {C D E : Cat}.
Context (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})).
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context {X : @Ob C} {Z : @Ob E}.
Context `{HC : !HasCoend SetCat (ProfunctorCompKernel Q P X Z)}.

(** Moving an intermediate arrow between the two factors is the original
    cowedge equation; identity actions are removed by the functor laws. *)

(** 将中间箭头在两因子间移动，就是原余楔方程；恒等作用由函子律消去。 *)

Lemma profunctor_comp_gluing {Y Y' : @Ob D} (h : Hom Y Y')
    (x : P (X,Y)) (y : Q (Y',Z))
  : ιPr[Q; P; Y] (x,lmap[Q; h] y) ≈S
      ιPr[Q; P; Y'] (rmap[P; h] x,y).
Proof.
  transitivity (ιPr[Q; P; Y]
    (dimap[P; @id X; @id Y] x,lmap[Q; h] y)).
  - apply (@func_proper _ _ (ιPr[Q; P; Y])). split.
    + symmetry. exact (profunctor_dimap_id P X Y x).
    + reflexivity.
  - transitivity (ιPr[Q; P; Y']
      (rmap[P; h] x,dimap[Q; @id Y'; @id Z] y)).
    + exact (cowedge_comm ιcoend[ProfunctorCompKernel Q P X Z] h (x,y)).
    + apply (@func_proper _ _ (ιPr[Q; P; Y'])). split.
      * reflexivity.
      * exact (profunctor_dimap_id Q Y' Z y).
Defined.

(** Generator equations determine a map out of the selected composite. *)

(** 生成元方程确定从选定复合出发的映射。 *)

Lemma profunctor_comp_hom_ext {W : SetC}
    (f g : coend[ProfunctorCompKernel Q P X Z] →r W)
    (H : ∀ Y, (f ∘r ιPr[Q; P; Y]) ≈f (g ∘r ιPr[Q; P; Y]))
  : f ≈f g.
Proof. exact (@coend_hom_ext D SetCat _ _ W f g H). Defined.

(** Descend a supplied cowedge using the same transparent universal map. *)

(** 用同一透明泛映射让给定余楔下降。 *)

Definition profunctor_comp_desc {W : SetC}
    (κ : Cowedge (ProfunctorCompKernel Q P X Z) W)
  : coend[ProfunctorCompKernel Q P X Z] →r W
  := coend⟨κ⟩.

(** Descent computes to the supplied operation on each generating pair. *)

(** 下降在每个生成对上计算为给定操作。 *)

Lemma profunctor_comp_desc_β {W : SetC}
    (κ : Cowedge (ProfunctorCompKernel Q P X Z) W) (Y : @Ob D)
  : (profunctor_comp_desc κ ∘r ιPr[Q; P; Y]) ≈f κ Y.
Proof. exact (coend_β κ Y). Defined.

(** The original universal witness retains mediator uniqueness. *)

(** 原泛见证保留中介唯一性。 *)

Definition profunctor_comp_desc_unique {W : SetC}
    (κ : Cowedge (ProfunctorCompKernel Q P X Z) W)
  : is_unique (λ f, ∀ Y, (f ∘r ιPr[Q; P; Y]) ≈f κ Y)
      (profunctor_comp_desc κ)
  := coend_desc_unique κ.

(** Reinserting all generator evaluations recovers an outgoing map. *)

(** 重新插入全部生成元求值，恢复原出射映射。 *)

Lemma profunctor_comp_desc_η {W : SetC}
    (f : coend[ProfunctorCompKernel Q P X Z] →r W)
  : profunctor_comp_desc
      (cowedge_comp (D := SetCat) f
        ιcoend[ProfunctorCompKernel Q P X Z]) ≈f f.
Proof. exact (@coend_η D SetCat _ _ W f). Defined.

End Generators.

(** ** Boundary Action on Generators

    Only the two endpoint coends are needed for a boundary map. A full
    composite profunctor specializes that same equation to its dimap. *)

(** ** 生成元上的边界作用

    边界映射只需要两个端点的 coend；完整复合 profunctor 将同一方程特化为 dimap。 *)

Section BoundaryInjection.
Universes u p.
Context {C D E : Cat}.
Context (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})).
Context (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})).
Context {X X' : @Ob C} {Z Z' : @Ob E}.
Context `{HF : !HasCoend SetCat (ProfunctorCompKernel Q P X Z)}.
Context `{HG : !HasCoend SetCat (ProfunctorCompKernel Q P X' Z')}.

(** Each factor receives its own outer boundary map, in the same order. *)

(** 每个因子接受其自身的外部边界映射，保持原顺序。 *)

Lemma profunctor_comp_boundary_inject (f : Hom X' X) (g : Hom Z Z')
    (Y : @Ob D) (x : P (X,Y)) (y : Q (Y,Z))
  : coend_map (ProfunctorCompBoundaryN Q P f g) (ιPr[Q; P; Y] (x,y)) ≈S
      ιPr[Q; P; Y] (lmap[P; f] x,rmap[Q; g] y).
Proof. exact (coend_map_β (ProfunctorCompBoundaryN Q P f g) Y (x,y)). Defined.

End BoundaryInjection.

(** Dimap of a selected composite is exactly its boundary map on generators. *)

(** 选定复合的 dimap 在生成元上恰为其边界映射。 *)

Lemma profunctor_comp_dimap_inject@{u p +} {C D E : Cat}
    (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _}))
    (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _}))
    `{HC : !HasProfunctorComp C D E Q P}
    {X X' : @Ob C} {Z Z' : @Ob E} (f : Hom X' X) (g : Hom Z Z')
    (Y : @Ob D) (x : P (X,Y)) (y : Q (Y,Z))
  : dimap[Q ∘Pr P; f; g] (ιPr[Q; P; Y] (x,y)) ≈S
      ιPr[Q; P; Y] (lmap[P; f] x,rmap[Q; g] y).
Proof. exact (profunctor_comp_boundary_inject Q P f g Y x y). Defined.
