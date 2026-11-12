From Cats Require Export
  Cat.Exponential.InternalHom
  Cat.Exponential.Functor.
From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Product.Transport.

Import Cats.Cat.Exponential.Core.

(** * Internal Sequencing and Product Contexts

    These are ordinary arrows in a cartesian closed base. Sequencing lists
    its inputs in execution order, before any effectful lifting is chosen. *)

(** * 内部顺序组合与积上下文

    这些是笛卡尔闭基底中的通常态射。顺序组合在选取效应提升之前，先按执行
    次序排列输入。 *)

Section Contexts.
Context {C : Cat} `{HP : !HasProduct C} `{HE : !HasExponential HP}.

(** Reverse the input order of internal composition, retaining its one
    underlying construction. *)

(** 反转内部复合的输入次序，保留同一个底层构造。 *)

Definition internal_then (X Y Z : @Ob C)
  : Hom ((Y ^ X) × (Z ^ Y)) (Z ^ X)
  := π2 ∘ᴱ π1.

(** Sequencing applies the first function before the second. *)

(** 顺序组合先应用第一个函数，再应用第二个。 *)

Lemma internal_then_app {W X Y Z : @Ob C}
    (u : Hom W ((Y ^ X) × (Z ^ Y))) (a : Hom W X)
  : app (internal_then X Y Z ∘ u) a ≈
      app (π2 ∘ u) (app (π1 ∘ u) a).
Proof.
  unfold internal_then. rewrite exponential_comp_sub, exponential_comp_app.
  reflexivity.
Qed.

(** Carry a fixed ordinary context through an internal function. *)

(** 将固定通常上下文穿过内部函数。 *)

Definition internal_context (Z X Y : @Ob C)
  : Hom (Y ^ X) ((Z × Y) ^ (Z × X))
  := ƛ ⟨π1 ∘ π2, app π1 (π2 ∘ π2)⟩.

(** Evaluation leaves the context alone and applies only the function. *)

(** 求值保持上下文不变，只应用函数。 *)

Lemma internal_context_app {W X Y : @Ob C} (Z : @Ob C)
    (f : Hom W (Y ^ X)) (a : Hom W (Z × X))
  : app (internal_context Z X Y ∘ f) a ≈
      ⟨π1 ∘ a, app f (π2 ∘ a)⟩.
Proof.
  unfold internal_context. rewrite <- exponential_curry_comp_r,
    exponential_app_β.
  repeat first [rewrite exponential_app_comp | rewrite product_comp_r |
    rewrite cross_η | rewrite comp_assoc | rewrite product_β1 |
    rewrite product_β2 | rewrite comp_id_l | rewrite comp_id_r].
  reflexivity.
Qed.

Local Ltac context_simpl :=
  repeat first [rewrite comp_assoc | rewrite internal_context_app |
    rewrite internal_then_app | rewrite exponential_app_dimap |
    rewrite exponential_app_comp | rewrite product_comp_r |
    rewrite cross_η | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r].

(** The sequential internal composition diagram uses the selected product
    associator, with inputs in the order first, second, third. *)

(** 内部顺序复合图使用选定积结合子，输入依次为第一、第二、第三个函数。 *)

Lemma internal_then_assoc (X Y Z T : @Ob C)
  : internal_then X Z T ∘ (internal_then X Y Z × id) ≈
      internal_then X Y T ∘ (id × internal_then Y Z T) ∘
        (@product_assoc C HP (Y ^ X) (Z ^ Y) (T ^ Z)).1.
Proof.
  apply exponential_ext. rewrite !exponential_uncurry_app.
  unfold product_assoc. cbn [projT1]. context_simpl. reflexivity.
Qed.

(** Carrying context preserves internal sequencing. *)

(** 携带上下文保持内部顺序组合。 *)

Lemma internal_context_then (W X Y Z : @Ob C)
  : internal_context W X Z ∘ internal_then X Y Z ≈
      internal_then (W × X) (W × Y) (W × Z) ∘
        (internal_context W X Y × internal_context W Y Z).
Proof.
  apply exponential_ext. rewrite !exponential_uncurry_app.
  context_simpl. reflexivity.
Qed.

(** Ordinary changes of context commute with an internal computation. *)

(** 通常上下文变化与内部计算交换。 *)

Lemma internal_context_natural {Z W : @Ob C} (h : Hom Z W)
    (X Y : @Ob C)
  : exponential_map (h × @id Y) ∘ internal_context Z X Y ≈
      exponential_dimap (h × @id X) id ∘ internal_context W X Y.
Proof.
  apply exponential_ext. rewrite !exponential_uncurry_app.
  rewrite <- !exponential_dimap_id_r. context_simpl. reflexivity.
Qed.

Context `{HT : !HasTerminal C}.

(** Name an ordinary arrow as a global internal function. *)

(** 将通常态射命名为全局内部函数。 *)

Definition exponential_name {X Y : @Ob C} (f : Hom X Y)
  : Hom 1 (Y ^ X)
  := ƛ (f ∘ π2).

(** Naming preserves the specified arrow equality. *)

(** 命名保持指定态射相等。 *)

Global Instance exponential_name_proper {X Y : @Ob C}
  : Proper (HomEq ==> HomEq) (@exponential_name X Y).
Proof. intros f g H. unfold exponential_name. rewrite H. reflexivity. Qed.

(** A named function evaluates in every context, with no well-pointedness
    assumption or equality of functions. *)

(** 命名函数可在每个上下文中求值，不要求良点性或函数原生相等。 *)

Lemma exponential_name_app {W X Y : @Ob C} (f : Hom X Y)
    (σ : Hom W 1) (a : Hom W X)
  : app (exponential_name f ∘ σ) a ≈ f ∘ a.
Proof.
  unfold exponential_name. rewrite <- exponential_curry_comp_r,
    exponential_app_β. context_simpl. reflexivity.
Qed.

(** The name of identity is the existing internal identity. *)

(** 恒等的命名就是已有内部恒等。 *)

Lemma exponential_name_id (X : @Ob C)
  : exponential_name (@id X) ≈ idᴱ[X].
Proof. unfold exponential_name, exponential_id. rewrite comp_id_l. reflexivity. Qed.

(** A named first function is ordinary precomposition. *)

(** 第一个函数为命名函数时，顺序组合就是通常预合成。 *)

Lemma internal_then_name_l {X Y : @Ob C} (f : Hom X Y) (Z : @Ob C)
  : internal_then X Y Z ∘ (exponential_name f × id) ≈
      exponential_dimap f id ∘ π2.
Proof.
  apply exponential_ext. rewrite !exponential_uncurry_app.
  context_simpl. rewrite exponential_name_app. reflexivity.
Qed.

(** A named second function is ordinary postcomposition. *)

(** 第二个函数为命名函数时，顺序组合就是通常后合成。 *)

Lemma internal_then_name_r {Y Z : @Ob C} (g : Hom Y Z) (X : @Ob C)
  : internal_then X Y Z ∘ (id × exponential_name g) ≈
      exponential_map g ∘ π1.
Proof.
  apply exponential_ext. rewrite !exponential_uncurry_app.
  rewrite <- exponential_dimap_id_r. context_simpl.
  rewrite exponential_name_app. reflexivity.
Qed.

(** Naming preserves ordinary composition in its sequential presentation. *)

(** 命名在顺序呈现下保持通常复合。 *)

Lemma internal_then_names {X Y Z : @Ob C} (g : Hom Y Z) (f : Hom X Y)
  : internal_then X Y Z ∘ ⟨exponential_name f, exponential_name g⟩ ≈
      exponential_name (g ∘ f).
Proof.
  apply exponential_ext. rewrite !exponential_uncurry_app.
  context_simpl. rewrite !exponential_name_app, comp_assoc. reflexivity.
Qed.

(** Naming a context-extended function agrees with extending its name. *)

(** 命名上下文扩展函数，等于扩展其命名。 *)

Lemma internal_context_name {X Y : @Ob C} (Z : @Ob C) (f : Hom X Y)
  : internal_context Z X Y ∘ exponential_name f ≈
      exponential_name (@id Z × f).
Proof.
  apply exponential_ext. rewrite !exponential_uncurry_app.
  context_simpl. rewrite !exponential_name_app. context_simpl. reflexivity.
Qed.

(** The terminal context is removed by the ordinary projection unitor. *)

(** 终上下文通过通常投影单位子移去。 *)

Lemma internal_context_unit (X Y : @Ob C)
  : exponential_map (π2 : Hom (1 × Y) Y) ∘ internal_context 1 X Y ≈
      exponential_dimap (π2 : Hom (1 × X) X) id.
Proof.
  apply exponential_ext. rewrite !exponential_uncurry_app.
  rewrite <- exponential_dimap_id_r. context_simpl. reflexivity.
Qed.

(** Nested ordinary contexts agree with a product context after the same
    selected reassociation on the argument and result. *)

(** 嵌套通常上下文经参数及结果上的同一组选定括号重排后，等于积上下文。 *)

Lemma internal_context_assoc (Z W X Y : @Ob C)
  : exponential_map (@product_assoc C HP Z W Y).1 ∘
      internal_context (Z × W) X Y ≈
      exponential_dimap (@product_assoc C HP Z W X).1 id ∘
        internal_context Z (W × X) (W × Y) ∘ internal_context W X Y.
Proof.
  apply exponential_ext. rewrite !exponential_uncurry_app.
  rewrite <- exponential_dimap_id_r.
  unfold product_assoc. cbn [projT1]. context_simpl. reflexivity.
Qed.

End Contexts.
