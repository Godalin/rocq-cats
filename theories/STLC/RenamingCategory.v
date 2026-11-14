From Cats Require Export
  STLC.Renaming
  Cat.Core.
From Cats Require Import
  STLC.Category
  Cat.Functor.Core.

(** * Contexts as Renaming Worlds

    A world records the available typed variables. An arrow from [Δ] to [Γ]
    assigns each variable requested by [Γ] a variable available in [Δ],
    following the existing context-map orientation. Thus the weakening arrow
    goes from [Γ ▻ A] to [Γ], although its action on syntax goes the other way.

    Arbitrary type-preserving renamings include exchange and identification
    of variables. There may be different parallel arrows; this category is
    not merely a preorder of context extensions. Hom equality compares the
    assignments pointwise, never their functions or equality witnesses.

    This world category differs from [CtxCat], whose arrows are arbitrary
    substitutions compared by beta/eta equality. Variable substitution gives
    a functor between them, but we do not assert it is faithful: at unit type
    beta/eta equality identifies terms from different variable positions. *)

(** * 将上下文视为重命名世界

    世界记录可用的带类型变量。从 [Δ] 到 [Γ] 的箭头为 [Γ] 所需的每个变量
    指定 [Δ] 中的一个变量，遵循既有上下文映射方向。因此，弱化箭头从
    [Γ ▻ A] 指向 [Γ]，虽然它在语法上的作用朝相反方向。

    任意保类型重命名包含变量交换与识别。同一对对象间可以存在不同箭头，
    因而此范畴不只是上下文扩张的预序。Hom 相等逐点比较赋值，从不比较函数
    或相等见证本身。

    世界范畴不同于 [CtxCat]：后者的箭头为任意替换，按 βη 相等比较。变量
    替换给出两者之间的函子，但这里不断言其忠实性：单位类型处的 βη 相等会
    识别来自不同变量位置的项。 *)

Local Open Scope stlc_ren_scope.

(** Renaming assignments as a setoid with pointwise structural equality.
    The carrier and equality-witness levels remain independently bounded. *)

(** 以逐点结构相等比较重命名赋值的广集。载体与相等见证层级保留独立界限。 *)

Program Definition RenS@{b r +} {B : Type@{b}} (Δ Γ : Ctx B)
  : SetC@{b r}
  :=
  {|carrier := Ren Δ Γ
  ; carrier_equiv := @RenEq B Δ Γ
  |}.

(** The category laws are precisely the existing renaming laws. Auxiliary
    law bounds do not identify hom-equality evidence with the carrier. *)

(** 范畴律恰为既有重命名定律；定律的辅助界限不将 Hom 相等见证与载体合并。 *)

Program Definition RenamingCat@{b r l +} (B : Type@{b})
  : Cat@{b b r l l}
  :=
  {|Ob := Ctx B
  ; HomSet := RenS@{b r}
  ; id _ := ren_id
  ; comp _ _ _ := ren_comp
  ; comp_proper _ _ _ ρ ρ' h τ τ' k A x
      := ren_comp_proper ρ ρ' h τ τ' k A x
  |}.
Next Obligation. apply ren_comp_id_r. Defined.
Next Obligation. apply ren_comp_id_l. Defined.
Next Obligation. apply ren_comp_assoc. Defined.

(** Interpret a renaming as simultaneous substitution of variables. Source
    hom equality and target beta/eta evidence have separate size bounds. *)

(** 将重命名解释为变量的同时替换。源 Hom 相等与目标 βη 见证具有独立大小界限。 *)

Program Definition RenamingToContextF@{b r e l +} (B : Type@{b})
  : Fct (RenamingCat B : Cat@{b b r l l}) (CtxCat@{b e l} B)
  :=
  {|F0 Γ := Γ
  ; F1 _ _ ρ := RenSub ρ
  |}.
Next Obligation.
  intros ρ τ h A x. apply tm_eq_of_eq.
  change (tm_var (ρ A x) = tm_var (τ A x)). now rewrite (h A x).
Defined.
Next Obligation. intros A x. apply tm_eq_refl. Defined.
Next Obligation. intros A x. apply tm_eq_refl. Defined.
