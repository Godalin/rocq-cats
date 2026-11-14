From Cats Require Export Cat.Functor.Core.
From Cats Require Import
  Cat.Core
  Cat.Terminal
  Cat.Product.Core
  Cat.Product.Transport.

(** * Functors Preserving Finite Products

    Preservation concerns full universal properties. The canonical comparison
    and its inverse are derived, without equality of chosen objects. *)

(** * 保持有限积的函子

    保持性使用完整泛性质；规范比较及其逆由此导出，不要求选定对象原生相等。 *)

Local Open Scope hom_scope.
Local Open Scope cat_scope.

(** Preserve the selected terminal and binary-product cones as full cones. *)

(** 将选定终对象与二元积锥保持为具有完整泛性质的锥。 *)

Class IsCartF {C D : Cat} (F : Fct C D)
    (TC : HasTerminal C) (PC : HasProduct C)
  :=
  { functor_terminal : is_terminal (F (@Term C TC))
  ; functor_product X Y : is_product (F X) (F Y)
      (F (@Prod C PC X Y)) (fmap F (@Cats.Cat.Product.Core.π1 C PC X Y))
      (fmap F (@Cats.Cat.Product.Core.π2 C PC X Y))
  }.

(** ** Product Comparisons for a Cartesian Functor

    Fix chosen terminal objects and binary products in [C] and [D], and a
    functor [F] preserving the chosen source structures. Derive the canonical
    product isomorphism and its pairing and naturality laws. *)

(** ** 笛卡尔函子的积比较

    固定 [C]、[D] 的选定终对象与二元积，以及保持来源选定结构的函子 [F]，导出规范积同构及其配对和自然性定律。 *)

Section CartFct.
Context {C D : Cat} (F : Fct C D)
    `{TC : !HasTerminal C} `{PC : !HasProduct C}
    `{TD : !HasTerminal D} `{PD : !HasProduct D}
    `{HF : !IsCartF F TC PC}.

(** The image product and the chosen target product are canonically isomorphic. *)

(** 像积与目标选定积之间具有规范同构。 *)

Definition functor_product_iso (X Y : @Ob C)
  : F ((X × Y)%ob) ≅ (F X × F Y)%ob.
Proof.
  exact (product_unique (functor_product X Y) (@product_universal D PD (F X) (F Y))).
Defined.

(** The inverse comparison is the mediator of the preserved product. *)

(** 逆向比较是保持积的泛中介。 *)

Definition functor_product_inv (X Y : @Ob C)
  : Hom (F X × F Y)%ob (F ((X × Y)%ob))
  := (functor_product X Y _ π1 π2).1.

(** Both projections of the inverse comparison compute. *)

(** 逆向比较的两个投影均满足计算方程。 *)

Lemma functor_product_inv_β (X Y : @Ob C)
  : (fmap F π1 ∘ functor_product_inv X Y ≈ π1) ∧
    (fmap F π2 ∘ functor_product_inv X Y ≈ π2).
Proof. exact (@this _ _ _ _ _ (functor_product X Y _ π1 π2).2). Qed.

(** Pairing is preserved through the product comparison. *)

(** 配对通过积比较得到保持。 *)

Lemma functor_pair {X Y Z : @Ob C} (f : Hom Z X) (g : Hom Z Y)
  : fmap F ⟨f, g⟩ ≈ functor_product_inv X Y ∘ ⟨fmap F f, fmap F g⟩.
Proof.
  transitivity ((functor_product X Y _ (fmap F f) (fmap F g)).1).
  - apply (functor_product X Y _ (fmap F f) (fmap F g)).2.
    split; rewrite <- functor_comp; [rewrite product_β1 | rewrite product_β2];
      reflexivity.
  - symmetry. apply (functor_product X Y _ (fmap F f) (fmap F g)).2.
    split; rewrite <- comp_assoc;
      [rewrite (fst (functor_product_inv_β X Y)), product_β1 |
       rewrite (snd (functor_product_inv_β X Y)), product_β2]; reflexivity.
Qed.

(** The inverse comparison is natural in both factors. *)

(** 逆向比较在两个因子上自然。 *)

Lemma functor_product_inv_natural {X Y X' Y' : @Ob C}
    (f : Hom X X') (g : Hom Y Y')
  : fmap F (f × g) ∘ functor_product_inv X Y ≈
      functor_product_inv X' Y' ∘ (fmap F f × fmap F g).
Proof.
  transitivity ((functor_product X' Y' _
    (fmap F f ∘ π1) (fmap F g ∘ π2)).1).
  - apply (functor_product X' Y' _ _ _).2. split;
      rewrite <- comp_assoc, <- functor_comp, cross_η;
      [rewrite product_β1 | rewrite product_β2];
      rewrite functor_comp, comp_assoc;
      [rewrite (fst (functor_product_inv_β X Y)) |
       rewrite (snd (functor_product_inv_β X Y))]; reflexivity.
  - symmetry. apply (functor_product X' Y' _ _ _).2. split;
      rewrite <- comp_assoc;
      [rewrite (fst (functor_product_inv_β X' Y')), cross_η, product_β1 |
       rewrite (snd (functor_product_inv_β X' Y')), cross_η, product_β2];
      reflexivity.
Qed.

End CartFct.

(** Identity functors preserve every selected finite-product structure. *)

(** 恒等函子保持任意选定有限积结构。 *)

Program Definition IdF_IsCartF (C : Cat)
    (TC : HasTerminal C) (PC : HasProduct C)
  : IsCartF (@IdF C) TC PC
  :=
  {|functor_terminal := @terminal_universal C TC
  ; functor_product := @product_universal C PC
  |}.

(** The identity functor's inverse product comparison is the identity arrow. *)

(** 恒等函子的逆向积比较等于恒等箭头。 *)

Lemma id_functor_product_inv (C : Cat) (TC : HasTerminal C)
    (PC : HasProduct C) (X Y : @Ob C)
  : @functor_product_inv C C (@IdF C) TC PC PC
      (IdF_IsCartF C TC PC) X Y ≈ id.
Proof.
  symmetry. apply product_pair_unique. split; apply comp_id_r.
Qed.

(** A cartesian functor preserves any terminal object, using its isomorphism
    with the selected one. *)

(** 笛卡尔函子通过与选定终对象的同构保持任意终对象。 *)

Definition cartesian_preserves_terminal {C D : Cat} (F : Fct C D)
    `{TC : !HasTerminal C} `{PC : !HasProduct C}
    `{HF : !IsCartF F TC PC} {T : @Ob C} (HT : is_terminal T)
  : is_terminal (F T).
Proof.
  pose (i := terminal_unique (@terminal_universal C TC) HT).
  pose (j := functor_is_iso F i.1 i.2).
  intros X. destruct (functor_terminal X) as [h Hh].
  exists (fmap F i.1 ∘ h). split; [exact I |].
  intros k _.
  assert (H : j.1 ∘ k ≈ h) by (apply Hh; exact I).
  rewrite <- H, <- comp_assoc, (snd j.2), comp_id_l. reflexivity.
Defined.

(** Preservation of a selected product implies preservation of every
    candidate product, without equality of chosen objects. *)

(** 保持选定积蕴含保持任意候选积，不要求选定对象相等。 *)

Definition cartesian_preserves_product {C D : Cat} (F : Fct C D)
    `{TC : !HasTerminal C} `{PC : !HasProduct C}
    `{HF : !IsCartF F TC PC} {X Y P : @Ob C}
    {p : Hom P X} {q : Hom P Y} (HP : is_product X Y P p q)
  : is_product (F X) (F Y) (F P) (fmap F p) (fmap F q).
Proof.
  pose (i := product_unique (@product_universal C PC X Y) HP).
  refine (product_apex_iso (functor_product X Y)
    (fmap F i.1; functor_is_iso F i.1 i.2) (fmap F p) (fmap F q) _ _).
  - change (fmap F p ∘ fmap F i.1 ≈ fmap F π1).
    rewrite <- functor_comp. apply functor_fmap_proper.
    exact (fst (@this _ _ _ _ _ (HP _ π1 π2).2)).
  - change (fmap F q ∘ fmap F i.1 ≈ fmap F π2).
    rewrite <- functor_comp. apply functor_fmap_proper.
    exact (snd (@this _ _ _ _ _ (HP _ π1 π2).2)).
Defined.

(** Cartesian functors compose relative to their named source structures. *)

(** 笛卡尔函子相对于具名源结构可以复合。 *)

Program Definition CompF_IsCartF {C D E : Cat}
    (F : Fct C D) (G : Fct D E)
    `{TC : !HasTerminal C} `{PC : !HasProduct C}
    `{TD : !HasTerminal D} `{PD : !HasProduct D}
    `{HF : !IsCartF F TC PC} `{HG : !IsCartF G TD PD}
  : IsCartF (G ∘F F) TC PC
  :=
  {|functor_terminal := cartesian_preserves_terminal G
      (@functor_terminal _ _ F TC PC HF)
  ; functor_product X Y := cartesian_preserves_product G
      (@functor_product _ _ F TC PC HF X Y)
  |}.

(** Inverse product comparisons compose through the second functor. *)

(** 逆向积比较通过第二个函子复合。 *)

Lemma functor_product_inv_comp {C D E : Cat}
    (F : Fct C D) (G : Fct D E)
    `{TC : !HasTerminal C} `{PC : !HasProduct C}
    `{TD : !HasTerminal D} `{PD : !HasProduct D}
    `{PE : !HasProduct E}
    `{HF : !IsCartF F TC PC} `{HG : !IsCartF G TD PD}
    (X Y : @Ob C)
  : @functor_product_inv _ _ (G ∘F F) TC PC PE
      (CompF_IsCartF F G) X Y ≈
      fmap G (functor_product_inv F X Y) ∘ functor_product_inv G (F X) (F Y).
Proof.
  symmetry. apply (functor_product (F := G ∘F F)
    (IsCartF := CompF_IsCartF F G) X Y _ π1 π2).2.
  split.
  - change (fmap G (fmap F π1) ∘
      (fmap G (functor_product_inv F X Y) ∘
        functor_product_inv G (F X) (F Y)) ≈ π1).
    rewrite <- comp_assoc, <- functor_comp,
      (fst (functor_product_inv_β F X Y)).
    exact (fst (functor_product_inv_β G (F X) (F Y))).
  - change (fmap G (fmap F π2) ∘
      (fmap G (functor_product_inv F X Y) ∘
        functor_product_inv G (F X) (F Y)) ≈ π2).
    rewrite <- comp_assoc, <- functor_comp,
      (snd (functor_product_inv_β F X Y)).
    exact (snd (functor_product_inv_β G (F X) (F Y))).
Qed.

(** ** Bundled Cartesian Functors *)

(** ** 打包的笛卡尔函子 *)

(** A functor together with preservation of the named source terminal and
    products. The target need not have globally chosen products. The unique
    coercion exposes the underlying functor; inherited preservation evidence
    remains available to the fixed-functor theorems above. *)

(** 函子及其对具名来源终对象和积的保持性；不要求目标具有全局选定的积。
    唯一强制转换暴露底层函子，继承的保持性证据可用于上述固定函子定理。 *)

Class CartFct {C D : Cat}
    (TC : HasTerminal C) (PC : HasProduct C)
  :=
  { CartF :> Fct C D
  ; cartesian_isCartF :: IsCartF CartF TC PC
  }.

Arguments CartF {_ _ _ _} _.
Arguments cartesian_isCartF {_ _ _ _} _.

(** Bundle an existing functor and its preservation evidence, retaining
    exactly their original computational data. *)

(** 打包已有函子及其保持性证据，保留原有计算数据。 *)

Program Definition CartFctFromPreservation {C D : Cat}
    {TC : HasTerminal C} {PC : HasProduct C}
    (F : Fct C D) (HF : IsCartF F TC PC)
  : @CartFct C D TC PC
  :=
  {|CartF := F
  ; cartesian_isCartF := HF
  |}.

(** The bundled identity reuses the existing preservation proof. Chosen
    functors are constructed explicitly, not selected by import. *)

(** 打包的恒等函子复用已有保持性证明；选定函子显式构造，不在导入时选取。 *)

Program Definition IdCartF (C : Cat)
    (TC : HasTerminal C) (PC : HasProduct C)
  : @CartFct C C TC PC
  := CartFctFromPreservation IdF (IdF_IsCartF C TC PC).

(** Composition needs only the chosen source structures of its two factors.
    Its preservation evidence is the existing generic composition theorem. *)

(** 复合只需要两个因子的选定来源结构，保持性证据复用已有通用复合定理。 *)

Program Definition CompCartF {C D E : Cat}
    {TC : HasTerminal C} {PC : HasProduct C}
    {TD : HasTerminal D} {PD : HasProduct D}
    (G : @CartFct D E TD PD) (F : @CartFct C D TC PC)
  : @CartFct C E TC PC
  := CartFctFromPreservation (G ∘F F)
      (@CompF_IsCartF C D E F G TC PC TD PD
        (cartesian_isCartF F) (cartesian_isCartF G)).
