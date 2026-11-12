From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Cat.Pullback
  Cat.Fibration
  Cat.Comprehension
  Cat.Arrow.Core.
From Cats Require Import
  DTT.CwF
  DTT.Context.Pullback.
From Cats Require Import
  Instance.Set.Fam.Core
  Instance.Set.Fam.Cat.

(** * Comprehension from a CwF

    Objects are contexts with a type. Morphisms are commuting squares of their
    display projections, retaining both maps and the commutativity witness.
    Equality compares the maps, not the witness. *)

(** * 由带族范畴构造理解结构

    对象是上下文与类型的配对，态射是显示投影之间的交换方形，保留两条边及交换性
    见证；相等比较映射，不比较见证。 *)

Definition ContextType {C : Cat} (T : Functor (C^op) FamCat)
  := ∃ Γ : @Ob C, Ty T Γ.

(** ** Maps between Context Extensions

    Fix a family-valued presheaf [T] on [C] with chosen context extensions.
    Define commuting maps between extensions, their specified equality, and
    identity and composition. *)

(** ** 上下文扩张之间的映射

    固定 [C] 上具有选定上下文扩张的族值预层 [T]，定义扩张之间的交换映射、指定相等以及恒等和复合。 *)

Section ContextMaps.
Context {C : Cat} (T : Functor (C^op) FamCat) `{HC : !HasContextExtension T}.

(** A commuting square between context-extension projections. *)

(** 上下文扩张投影之间的交换方形。 *)

Record ContextMap (X Y : ContextType T)
  :=
  { context_map_base : Hom X.1 Y.1
  ; context_map_ext : Hom (X.1 ▹[T] X.2) (Y.1 ▹[T] Y.2)
  ; context_map_comm : context_proj T Y.2 ∘ context_map_ext ≈
      context_map_base ∘ context_proj T X.2
  }.

Arguments context_map_base {_ _} _.
Arguments context_map_ext {_ _} _.
Arguments context_map_comm {_ _} _.

(** Compare the base and extension arrows of context maps. *)

(** 比较上下文映射的基底箭头与扩张箭头。 *)

Definition ContextMapEq {X Y : ContextType T} (f g : ContextMap X Y)
  := context_map_base f ≈ context_map_base g ∧ context_map_ext f ≈ context_map_ext g.

(** [ContextMapEq] is an equivalence relation. *)

(** [ContextMapEq] 是等价关系。 *)

Global Instance ContextMapEq_Equivalence {X Y : ContextType T}
  : Equivalence (@ContextMapEq X Y).
Proof.
  split.
  - intros f. split; reflexivity.
  - intros f g [Hb He]. split; symmetry; assumption.
  - intros f g h [Hb He] [Kb Ke]. split.
    + transitivity (context_map_base g); assumption.
    + transitivity (context_map_ext g); assumption.
Defined.

(** The identity square between a context extension and itself. *)

(** 上下文扩张到自身的恒等方形。 *)

Program Definition context_map_id (X : ContextType T)
  : ContextMap X X
  :=
  {|context_map_base := id
  ; context_map_ext := id
  |}.
Next Obligation. rewrite comp_id_r, comp_id_l. reflexivity. Defined.

(** Compose the base and extension sides of context maps. *)

(** 复合上下文映射的基底侧边与扩张侧边。 *)

Program Definition context_map_comp {X Y Z : ContextType T}
    (g : ContextMap Y Z) (f : ContextMap X Y)
  : ContextMap X Z
  :=
  {|context_map_base := context_map_base g ∘ context_map_base f
  ; context_map_ext := context_map_ext g ∘ context_map_ext f
  |}.
Next Obligation.
  rewrite <- comp_assoc, (context_map_comm g), comp_assoc, (context_map_comm f),
    <- comp_assoc. reflexivity.
Defined.

End ContextMaps.

Arguments context_map_base {_ _ _ _ _} _.
Arguments context_map_ext {_ _ _ _ _} _.
Arguments context_map_comm {_ _ _ _ _} _.

Notation "g '∘Ctx[' T ']' f" := (context_map_comp T g f)
  (at level 40, left associativity, format "g  ∘Ctx[ T ]  f") : cat_scope.

(** ** The Category of Context Types

    Keep [T] and its chosen context extensions fixed. Assemble context types
    and commuting extension maps into a category, with base and extension
    functors and a projection transformation. *)

(** ** 上下文类型范畴

    保持 [T] 及其选定上下文扩张固定，将上下文类型和交换扩张映射组装为范畴，并给出基底函子、扩张函子及投影变换。 *)

Section ContextCategory.
Context {C : Cat} (T : Functor (C^op) FamCat) `{HC : !HasContextExtension T}.

(** The category of context-type pairs and commuting display squares. *)

(** 上下文与类型的配对及显示交换方形构成的范畴。 *)

Program Definition ContextTypeCat
  : Cat
  :=
  {|Ob := ContextType T
  ; HomSet X Y :=
      {|carrier := ContextMap T X Y
      ; carrier_equiv := ContextMapEq T
      ; carrier_setoid := ContextMapEq_Equivalence T
      |}
  ; id := context_map_id T
  ; comp X Y Z := context_map_comp T
  |}.
Next Obligation.
  intros g g' [Hb He] f f' [Kb Ke]. split; apply comp_proper; assumption.
Defined.
Next Obligation. split; apply comp_id_r. Defined.
Next Obligation. split; apply comp_id_l. Defined.
Next Obligation. split; apply comp_assoc. Defined.

(** Forget a context-type pair to its base context. *)

(** 将上下文与类型的配对忘却为基底上下文。 *)

Program Definition CwFBaseF
  : Functor ContextTypeCat C
  :=
  {|F0 X := X.1
  ; F1 X Y := context_map_base
  |}.
Next Obligation. intros f g H. exact (fst H). Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** Send a context-type pair to its context extension. *)

(** 将上下文与类型的配对送到其上下文扩张。 *)

Program Definition CwFExtF
  : Functor ContextTypeCat C
  :=
  {|F0 X := X.1 ▹[T] X.2
  ; F1 X Y := context_map_ext
  |}.
Next Obligation. intros f g H. exact (snd H). Defined.
Next Obligation. reflexivity. Defined.
Next Obligation. reflexivity. Defined.

(** Context-extension projections form a natural transformation to the base
    functor. *)

(** 上下文扩张投影组成到基底函子的自然变换。 *)

Program Definition CwFProjectionN
  : CwFExtF ⇒ CwFBaseF
  :=
  {|nt X := context_proj T X.2
  |}.
Next Obligation. apply context_map_comm. Defined.

End ContextCategory.

(** Substitute the type component of a context-type pair. *)

(** 替换上下文与类型配对中的类型分量。 *)

Definition ReindexContextType {C : Cat} (T : Functor (C^op) FamCat)
    (Y : ContextType T) {Γ : @Ob C} (σ : Hom Γ Y.1)
  : ContextType T
  := (Γ; Y.2[σ]Ty[T]).

Notation "Y '[' σ ']Ctx[' T ']'" := (ReindexContextType T Y σ)
  (at level 8, left associativity, format "Y [ σ ]Ctx[ T ]") : cat_scope.

(** ** Comprehension from Context Extensions

    Assume chosen context extensions for [T]. Use substitution pullbacks to
    construct cartesian reindexing and the comprehension structure, then
    characterize cartesian maps. *)

(** ** 由上下文扩张构造理解结构

    假定 [T] 具有选定上下文扩张，用替换拉回构造笛卡尔重索引及理解结构，再刻画笛卡尔映射。 *)

Section ContextComprehension.
Context {C : Cat} (T : Functor (C^op) FamCat) `{HC : !HasContextExtension T}.

(** The canonical display square over a context substitution. *)

(** 上下文替换上的标准显示方形。 *)

Program Definition context_type_reindex (Y : ContextType T) {Γ : @Ob C}
    (σ : Hom Γ Y.1)
  : ContextMap T Y[σ]Ctx[T] Y
  :=
  {|context_map_base := σ
  ; context_map_ext := σ^+[T, Y.2]
  |}.
Next Obligation. apply context_lift_proj. Defined.

(** A pullback display square is cartesian in the total category. *)

(** 拉回显示方形在全范畴中是笛卡尔态射。 *)

Definition context_map_pullback_cartesian {X Y : ContextType T}
    (f : ContextMap T X Y)
    (HP : is_pullback (context_map_base f) (context_proj T Y.2)
      (X.1 ▹[T] X.2) (context_proj T X.2) (context_map_ext f))
  : f ⦂ Cart(CwFBaseF T).
Proof.
  intros Z g u H.
  assert (Hcone : context_map_base f ∘ (u ∘ context_proj T Z.2) ≈
      context_proj T Y.2 ∘ context_map_ext g).
  { rewrite <- comp_assoc, H. symmetry. apply context_map_comm. }
  destruct (snd HP (Z.1 ▹[T] Z.2) (u ∘ context_proj T Z.2) (context_map_ext g) Hcone)
    as [h [[Hbase Hext] Hunique]].
  pose (k := ({|context_map_base := u
              ; context_map_ext := h
              ; context_map_comm := Hbase
              |}
    : ContextMap T Z X)).
  exists k. refine {|this := _
                   ; that := _
                   |}.
  - split; [reflexivity | split; assumption].
  - intros l [Hlbase [_ Hlext]]. split; [exact Hlbase |].
    apply Hunique. split.
    + transitivity (context_map_base l ∘ context_proj T Z.2).
      * apply context_map_comm.
      * rewrite Hlbase. reflexivity.
    + exact Hlext.
Defined.

(** Canonical substitution squares are cartesian for the context-base functor. *)

(** 标准替换方形对上下文基底函子是笛卡尔的。 *)

Definition context_type_reindex_cartesian (Y : ContextType T) {Γ : @Ob C}
    (σ : Hom Γ Y.1)
  : context_type_reindex Y σ ⦂ Cart(CwFBaseF T)
  := context_map_pullback_cartesian (context_type_reindex Y σ) (context_lift_pullback T σ Y.2).

(** Enable the chosen lifts explicitly; their base identification is
    reflexive. *)

(** 选定提升须显式启用，其基底识别是自反见证。 *)

Program Definition CwFBaseF_HasCartesianLift
  : HasCartesianLift (CwFBaseF T)
  :=
  {|CartesianLift Y Γ σ := Y[σ]Ctx[T]
  ; cartesian_lift_base Y Γ σ := eq_refl
  ; cartesian_lift Y Γ σ := context_type_reindex Y σ
  |}.
Next Obligation. symmetry. apply comp_id_r. Defined.
Next Obligation. apply context_type_reindex_cartesian. Defined.

(** Any cartesian square is isomorphic to the chosen display pullback. *)

(** 任意笛卡尔方形都同构于选定显示拉回。 *)

Definition cwf_comprehension_universal
  : is_comprehension (CwFProjectionN T).
Proof.
  intros X Y f Hf. pose (σ := context_map_base f).
  assert (H : fmap (CwFBaseF T) (context_type_reindex Y σ) ∘ id ≈ fmap (CwFBaseF T) f).
  { apply comp_id_r. }
  pose (k := cartesian_factor (context_type_reindex_cartesian Y σ) f id H).
  assert (Hiso : @is_iso (ContextTypeCat T) _ _ k).
  { apply (cartesian_factor_is_iso Hf (context_type_reindex_cartesian Y σ) id).
    exists id. split; apply comp_id_l. }
  pose proof (cartesian_factor_base (context_type_reindex_cartesian Y σ) f id H) as Hbase.
  pose proof (cartesian_factor_comp (context_type_reindex_cartesian Y σ) f id H) as Hcomp.
  change (context_map_base k ≈ id) in Hbase.
  eapply (pullback_iso (C := C) (p1 := context_proj T Y.2[σ]Ty[T])
    (p2 := σ^+[T, Y.2]) (fmap (CwFExtF T) k) (functor_is_iso (CwFExtF T) k Hiso)).
  - transitivity (context_map_base k ∘ context_proj T X.2).
    + exact (context_map_comm k).
    + rewrite Hbase, comp_id_l. reflexivity.
  - exact (snd Hcomp).
  - apply context_lift_pullback.
Defined.

(** Chosen context extensions determine a comprehension structure. *)

(** 选定上下文扩张确定理解结构。 *)

Program Definition CwFComprehension
  : Comprehension (CwFBaseF T)
  :=
  {|comprehension_lifts := CwFBaseF_HasCartesianLift
  ; ExtF := CwFExtF T
  ; projectionN := CwFProjectionN T
  ; comprehension_universal := cwf_comprehension_universal
  |}.

(** A context map is cartesian exactly when its display square is a pullback. *)

(** 上下文映射是笛卡尔的，当且仅当其显示方形为拉回。 *)

Theorem context_map_cartesian_iff_pullback {X Y : ContextType T}
    (f : ContextMap T X Y)
  : f ⦂ Cart(CwFBaseF T) ↔
    is_pullback (context_map_base f) (context_proj T Y.2)
      (X.1 ▹[T] X.2) (context_proj T X.2) (context_map_ext f).
Proof.
  split.
  - exact (cwf_comprehension_universal X Y f).
  - apply context_map_pullback_cartesian.
Defined.

End ContextComprehension.

(** ** Full Faithfulness of Comprehension

    Continue with the same [T] and chosen extensions. Recover a context map
    from its underlying arrow square to prove the comprehension functor fully
    faithful. *)

(** ** 理解函子的全忠实性

    继续使用同一 [T] 及选定扩张，从底层箭头方形恢复上下文映射，证明理解函子全忠实。 *)

Section FullComprehension.
Context {C : Cat} (T : Functor (C^op) FamCat) `{HC : !HasContextExtension T}.

(** Present the CwF comprehension as a functor to the arrow category. *)

(** 将带族范畴的理解结构表示为到箭头范畴的函子。 *)

Definition CwFComprehensionF
  : Functor (ContextTypeCat T) (Arr C)
  := ComprehensionF (CwFComprehension T).

(** A square between context projections determines a context map. *)

(** 上下文投影间的方形确定上下文映射。 *)

Program Definition context_map_from_arrow {X Y : ContextType T}
    (f : Hom (CwFComprehensionF X) (CwFComprehensionF Y))
  : ContextMap T X Y
  :=
  {|context_map_base := arrow_bottom f
  ; context_map_ext := arrow_top f
  ; context_map_comm := arrow_comm f
  |}.

(** The CwF comprehension embedding into the arrow category is fully faithful. *)

(** 带族范畴理解结构到箭头范畴的嵌入全忠实。 *)

Theorem cwf_comprehension_fully_faithful
  : is_fully_faithful CwFComprehensionF.
Proof.
  split.
  - intros X Y f. exists (context_map_from_arrow f). split; reflexivity.
  - intros X Y f g [He Hb]. split; assumption.
Defined.

End FullComprehension.
