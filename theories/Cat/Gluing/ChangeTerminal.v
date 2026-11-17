From Cats Require Export
  Cat.Gluing.ChangeProduct.
From Cats Require Import
  Cat.Isomorphism
  Cat.Functor.Cartesian.

(** * Terminal Objects under Gluing Model Change

    For a base object [T], the image of [(F T, T, id)] has structure
    arrow equal to [α T]. If [H T] is terminal and this one component is
    invertible, compare the image with [(F' (H T), H T, id)] and transport
    the existing terminal universal property. Neither terminal preservation
    by [K] nor a globally invertible natural boundary is required.

    Combine this local condition with the independently proved binary
    product conditions in an explicit cartesian-preservation value. No
    terminal choices or preservation instances are registered by import. *)

(** * 粘合模型变化下的终对象

    对基对象 [T]，[(F T, T, id)] 的像结构箭头等于 [α T]。若 [H T]
    为终且此单个分量可逆，则将像与 [(F' (H T), H T, id)] 比较并运输
    既有终对象泛性质。不要求 [K] 保持终对象，也不要求自然边界全局可逆。

    将此局部条件与独立证明的二元积条件组合为显式笛卡尔保持值；导入本模块
    不会注册终对象选择或保持性实例。 *)

(** ** A Local Boundary at the Base Object

    Fix a compatible model change and a supplied base object. The object
    comparison itself needs no terminality; its inverse uses only [α T].
    All maps retain the original comma side-map presentation. *)

(** ** 基对象处的局部边界

    固定相容模型变化及给定基对象。对象比较本身不要求终性，其逆只使用
    [α T] 的逆。全部映射保留原逗号侧边表示。 *)

Section GluingChangeTerminal.
Context {C D C' D' : Cat}.
Context {F : Fct C D} {F' : Fct C' D'}.
Context (H : Fct C C') (K : Fct D D').
Context (α : (K ∘F F) ⇒ (F' ∘F H)) (T : C).

(** Functoriality removes the identity factors in the stored structure. *)

(** 函子性消去所存结构中的恒等因子。 *)

Definition gluing_change_terminal_arrow
  : comma_arrow (GluingChangeF H K α (GluingTerminal F T)) ≈ α T.
Proof.
  etransitivity; [apply gluing_change_arrow |].
  change (α T ∘ fmap K (@id (F T)) ≈ α T).
  rewrite (@fct_id D D' K), comp_id_r. reflexivity.
Defined.

(** The forward comparison uses the boundary and an identity base map. *)

(** 正向比较使用边界及恒等基映射。 *)

Program Definition gluing_change_terminal_map
  : Hom (GluingChangeF H K α (GluingTerminal F T))
      (GluingTerminal F' (H T))
  :=
  {|comma_left := α T
  ; comma_right := id
  |}.
Next Obligation.
  rewrite fct_id, comp_id_l, comp_id_l.
  exact gluing_change_terminal_arrow.
Defined.

(** The inverse keeps exactly the supplied inverse boundary map. *)

(** 逆恰保留给定的逆边界映射。 *)

Program Definition gluing_change_terminal_inverse (Hα : is_iso (α T))
  : Hom (GluingTerminal F' (H T))
      (GluingChangeF H K α (GluingTerminal F T))
  :=
  {|comma_left := Hα.1
  ; comma_right := id
  |}.
Next Obligation.
  rewrite fct_id, comp_id_l, gluing_change_terminal_arrow.
  symmetry. exact (snd Hα.2).
Defined.

(** Both inverse equations use side-map equality, without comparing the
    commutativity or inverse-law witnesses. *)

(** 两条互逆方程使用侧边相等，不比较交换性或互逆定律的见证。 *)

Definition gluing_change_terminal_iso (Hα : is_iso (α T))
  : GluingChangeF H K α (GluingTerminal F T) ≅ GluingTerminal F' (H T).
Proof.
  exists gluing_change_terminal_map, (gluing_change_terminal_inverse Hα).
  split; split; cbn.
  - exact (fst Hα.2).
  - apply comp_id_l.
  - exact (snd Hα.2).
  - apply comp_id_l.
Defined.

(** Transport the already proved terminal property along the inverse
    comparison; there is no new universal-property proof. *)

(** 沿逆比较运输已经证明的终性，不另证泛性质。 *)

Definition gluing_change_terminal (HT : is_terminal (H T))
    (Hα : is_iso (α T))
  : @is_terminal (Gluing F')
      (GluingChangeF H K α (GluingTerminal F T))
  := terminal_iso (gluing_terminal F' (H T) HT)
      (iso_symm (gluing_change_terminal_iso Hα)).

End GluingChangeTerminal.

(** ** Finite-Product Preservation with Named Source Choices

    Add only a chosen base terminal to the binary-product hypotheses.
    At that selected object require its [H]-image to be terminal and the
    boundary to be invertible. Reuse both accepted candidate results;
    no terminal in [D] or selected structures in the target are required. *)

(** ** 具名来源选择下的有限积保持

    在二元积假设上只增加选定基终对象；在该对象处要求其 [H] 像为终且边界
    可逆。复用两个已得候选结果，不要求 [D] 有终对象或目标有选定结构。 *)

Section GluingChangeCartesian.
Context {C D C' D' : Cat}.
Context {F : Fct C D} {F' : Fct C' D'}.
Context (H : Fct C C') (K : Fct D D').
Context (α : (K ∘F F) ⇒ (F' ∘F H)).
Context `{TC : !HasTerminal C} `{PC : !HasProduct C}
    `{PD : !HasProduct D}.
Context (source : ∀ A B : C,
    is_product (F A) (F B) (F ((A × B)%ob)) (fmap F π1) (fmap F π2)).
Context (base : ∀ A B : C,
    is_product (H A) (H B) (H ((A × B)%ob)) (fmap H π1) (fmap H π2)).
Context (target : ∀ A B : D,
    is_product (K A) (K B) (K ((A × B)%ob)) (fmap K π1) (fmap K π2)).
Context (image : ∀ A B : C,
    is_product (F' (H A)) (F' (H B)) (F' (H ((A × B)%ob)))
      (fmap F' (fmap H π1)) (fmap F' (fmap H π2))).

(** This explicit preservation value uses the same terminal and product
    choices as the existing source gluing cartesian category. *)

(** 此显式保持值使用与既有来源粘合笛卡尔范畴相同的终对象及积选择。 *)

Program Definition GluingChange_IsCartF
    (HT : is_terminal (H (@Term C TC)))
    (Hα : is_iso (α (@Term C TC)))
  : IsCartF (GluingChangeF H K α) (Gluing_HasTerminal F)
      (Gluing_HasProduct F source)
  :=
  {|fct_terminal := gluing_change_terminal H K α (@Term C TC) HT Hα
  ; fct_product := gluing_change_product H K α source base target image
  |}.

End GluingChangeCartesian.
