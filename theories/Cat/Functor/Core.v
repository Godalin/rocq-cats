From Cats Require Import Cat.Core.



(** * Functor *)

(** * 函子 *)

(** ** Functor Laws on Fixed Maps

    Separate preservation evidence from supplied object and arrow maps.
    Context actions can share one object tensor while using this same law
    interface independently on the left and right. *)

(** ** 固定映射上的函子律

    为给定的对象与态射映射单独提供保持性见证。上下文作用可以共享一个对象
    张量，并在左右两侧分别使用同一个定律接口。 *)

Class IsFct {C D : Cat} (obj : C → D)
    (map : ∀ {X Y : C}, Hom X Y → Hom (obj X) (obj Y))
  :=
  (** Respect the specified equality on each hom-set. *)

  (** 保持每个 Hom 广集的指定相等。 *)

  { fmap_proper {X Y : C}
    :: Proper (≈[X,Y] ==> ≈[obj X,obj Y]) (@map X Y)

  (** Preserve identities and composition on these same maps. *)

  (** 在同一组映射上保持恒等及复合。 *)

  ; fmap_id (X : C) :
    map (id[X]) ≈ id[obj X]

  ; fmap_comp {X Y Z : C} (f : Hom Y Z) (g : Hom X Y)
    : map (f ∘ g) ≈ map f ∘ map g
  }.

(** ** Bundled Functors *)

(** ** 打包函子 *)

(** A functor stores its object map, its dependent arrow map and one
    witness of the laws on those maps. The object coercion writes [F X]. *)

(** 函子保存对象映射、依赖于对象映射的态射映射及一份函子律见证。
    对象强制转换可直接写作 [F X]。 *)

Record Fct@{o h p l hm lm o' h' p' l'}
    (C : Cat@{o h p l l}) (D : Cat@{o' h' p' l' l'})
  : Type@{max(o,h,lm,o',h',p')}
  := MakeFct
  { fobj :> C → D
  ; fmap {X Y : C} : Hom X Y → Hom (fobj X) (fobj Y)
  ; isFct
    :: @IsFct@{hm lm o h p l o' h' p' l'} C D fobj (@fmap)
  }.

Arguments MakeFct {_ _} _ _ _.
Arguments isFct {_ _} _.

Arguments fobj {_ _} _ _.
Arguments fmap {_ _} _ {_ _} _.
Arguments fmap_id {_ _ _ _ _ X}.

(** ** Faithful and Full Functors

    Comparisons use the source and target categories' morphism equivalences.
    Fullness retains a preimage witness in [Type] for each target morphism. *)

(** ** 忠实函子与满函子

    比较使用两侧范畴指定的态射相等；满性为每条目标态射保留 Type 中的原像见证。 *)

Definition is_faithful {C D : Cat} (F : Fct C D)
  := ∀ X Y (f g : Hom X Y), fmap F f ≈ fmap F g → f ≈ g.

(** Every arrow between image objects has a selected preimage up to hom
    equality. *)

(** 像对象之间的每条箭头都具有按 Hom 相等选取的原像。 *)

Definition is_full {C D : Cat} (F : Fct C D)
  := ∀ X Y (g : Hom (F X) (F Y)),
    ∃ f : Hom X Y, fmap F f ≈ g.

(** Fullness together with faithfulness, retaining full preimage data. *)

(** 同时具有满性与忠实性，并保留满性的原像数据。 *)

Definition is_fully_faithful {C D : Cat} (F : Fct C D)
  := is_full F ∧ is_faithful F.

(** Essential surjectivity retains an object representative and an
    isomorphism, rather than an equality of objects or a truncated existence
    statement. *)

(** 本质满保留对象代表与同构，不要求对象原生相等，也不截断存在见证。 *)

Definition is_essentially_surjective {C D : Cat} (F : Fct C D)
  := ∀ Y : D, ∃ X : C, F X ≅ Y.

(** A functor sends an invertible arrow to an invertible arrow. *)

(** 函子将可逆箭头送到可逆箭头。 *)

Definition fct_is_iso {C D : Cat} (F : Fct C D)
    {X Y : C} (f : Hom X Y) (Hf : is_iso f)
  : is_iso (fmap F f).
Proof.
  exists (fmap F Hf.1). split;
    unfold is_linv_of, is_rinv_of in *;
    rewrite <- fmap_comp;
    [rewrite (fst Hf.2) | rewrite (snd Hf.2)]; apply fmap_id.
Defined.

(** A fully faithful functor reflects invertibility. Fullness supplies an
    inverse preimage, and faithfulness reflects its two inverse equations. *)

(** 全忠实函子反映可逆性：满性提供逆的原像，忠实性反映两条互逆方程。 *)

Definition fct_reflects_iso {C D : Cat} (F : Fct C D)
    (HF : is_fully_faithful F) {X Y : C} (f : Hom X Y)
    (Hf : is_iso (fmap F f))
  : is_iso f.
Proof.
  destruct (fst HF Y X Hf.1) as [g Hg].
  exists g. split; apply (snd HF); rewrite fmap_comp, Hg, fmap_id;
    [exact (fst Hf.2) | exact (snd Hf.2)].
Defined.



(** ** Identity Functor *)

(** ** 恒等函子 *)

(** The identity functor. *)

(** 恒等函子。 *)

Program Definition IdF {C : Cat}
  : Fct C C
  :=
  {|fobj X := X
  ; fmap _ _ f := f
  ; isFct := _
  |}.
Next Obligation.
  refine {|fmap_proper := _; fmap_id := _; fmap_comp := _|}.
  - intros X Y f g H. exact H.
  - intros X. reflexivity.
  - intros X Y Z f g. reflexivity.
Qed.

(** Compose functors on objects and morphisms. *)

(** 在对象与态射上复合函子。 *)

Program Definition CompF {C D E : Cat}
    (G : Fct D E) (F : Fct C D)
  :=
  {|fobj X := G (F X)
  ; fmap _ _ f := fmap G (fmap F f)
  ; isFct := _
  |}.
Next Obligation.
  refine {|fmap_proper := _; fmap_id := _; fmap_comp := _|}.
  - intros X Y f g H. cbn.
    apply fmap_proper, fmap_proper. exact H.
  - intros X. cbn. repeat rewrite fmap_id. reflexivity.
  - intros X Y Z f g. cbn. repeat rewrite fmap_comp. reflexivity.
Qed.

(** ** Fixing One Argument of a Functor from a Product Category *)

(** ** 固定乘积范畴上的一个函子参数 *)

Section PartialFunctor.
Context {C D E : Cat}.

(** Apply at the right argument [d], leaving the left argument free. *)

(** 在右侧代入对象 [d]，左侧仍为变量。 *)

Program Definition AtRF
    (F : Fct (C ×C D) E) (d : D)
  : Fct C E
  :=
  {|fobj c := F (c, d)
  ; fmap X Y f := fmap F ((f, id[d]) : _)
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation.
  intros u v Huv.
  apply fmap_proper. split; cato.
Qed.
Next Obligation.
  exact (fmap_id (IsFct := isFct F) (X := (X, d))).
Qed.
Next Obligation.
  rewrite <- fmap_comp. apply fmap_proper. split; cato.
Qed.

(** Apply at the left argument [c], leaving the right argument free. *)

(** 在左侧代入对象 [c]，右侧仍为变量。 *)

Program Definition AtLF
    (F : Fct (C ×C D) E) (c : C)
  : Fct D E
  :=
  {|fobj d := F (c, d)
  ; fmap X Y f := fmap F ((id[c], f) : _)
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation.
  intros u v Huv. apply fmap_proper. split; cato.
Qed.
Next Obligation.
  exact (fmap_id (IsFct := isFct F) (X := (c, X))).
Qed.
Next Obligation.
  rewrite <- fmap_comp. apply fmap_proper. split; cato.
Qed.

End PartialFunctor.

Infix "∘F" := CompF
  (at level 40) : cat_scope.

(** Independent functors act componentwise on a product category. *)

(** 两个独立函子在乘积范畴上逐分量作用。 *)

Program Definition ProdF {C D E K : Cat}
    (F : Fct C D) (G : Fct E K)
  : Fct (C ×C E) (D ×C K)
  :=
  {|fobj p := (F (fst p), G (snd p))
  ; fmap X Y f := (fmap F (fst f), fmap G (snd f))
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation.
  intros [f g] [f' g'] [Hf Hg]. split; cbn.
  - exact (fmap_proper (IsFct := isFct F) f f' Hf).
  - exact (fmap_proper (IsFct := isFct G) g g' Hg).
Qed.
Next Obligation. split; apply fmap_id. Qed.
Next Obligation. split; apply fmap_comp. Qed.

Infix "×F" := ProdF (at level 41)
  : cat_scope.

(** A functor preserves identities transported along native object equality. *)

(** 函子保持沿对象原生相等运输的恒等态射。 *)

Lemma fmap_eq_to_hom {C D : Cat} (F : Fct C D)
    {X Y : C} (p : X = Y)
  : fmap F (eq_to_hom p) ≈ eq_to_hom (f_equal F p).
Proof. destruct p. simpl. apply fmap_id. Qed.

(** ** Opposite Functors

    Taking opposites reverses arrows in both categories. Double opposition is
    compared by explicit identity-on-objects-and-morphisms functors, without
    requiring equality of category records or their law proofs. *)

(** ** 反函子

    取反同时反转两侧范畴的箭头。双重取反通过在对象和态射上为恒等的显式函子比较，
    不要求范畴记录或定律证明原生相等。 *)

Program Definition OpF {C D : Cat} (F : Fct C D)
  : Fct (C^op) (D^op)
  :=
  {|fobj X := F X
  ; fmap X Y f := fmap F f
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation.
  intros u v Huv.
  exact (fmap_proper (IsFct := isFct F) u v Huv).
Qed.
Next Obligation.
  exact (fmap_id (IsFct := isFct F) (X := X)).
Qed.
Next Obligation.
  exact (fmap_comp (IsFct := isFct F) g f).
Qed.

Notation "F '^opF'" := (OpF F)
  (at level 1) : cat_scope.

(** Taking opposites preserves chosen arrow preimages. *)

(** 取反保留选定的箭头原像。 *)

Definition fct_op_full {C D : Cat} {F : Fct C D}
    (HF : is_full F)
  : is_full (F^opF)
  := λ X Y f, HF Y X f.

(** Inverting the representative isomorphism gives essential surjectivity
    in the opposite category, with the same object representatives. *)

(** 反转代表同构给出反范畴中的本质满性，并保留原对象代表。 *)

Definition fct_op_essentially_surjective {C D : Cat}
    {F : Fct C D} (HF : is_essentially_surjective F)
  : is_essentially_surjective (F^opF).
Proof.
  intros Y. destruct (HF Y) as [X e].
  exists X, e.2.1, e.1. split;
    [exact (fst e.2.2) | exact (snd e.2.2)].
Defined.

(** Read a functor between opposite categories in the original categories.
    This keeps the underlying maps, without comparing category records. *)

(** 将反范畴之间的函子读作原范畴之间的函子，保留底层映射，不比较范畴记录。 *)

Program Definition UnopF {C D : Cat}
    (F : Fct (C^op) (D^op))
  : Fct C D
  :=
  {|fobj X := F X
  ; fmap X Y f := fmap F f
  ; isFct :=
      {|fmap_proper _ _ f g H := fmap_proper (IsFct := isFct F) f g H
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation.
  exact (fmap_id (IsFct := isFct F) (X := X)).
Qed.
Next Obligation.
  exact (fmap_comp (IsFct := isFct F) g f).
Qed.

Notation "F '^unopF'" := (UnopF F)
  (at level 1) : cat_scope.

(** The identity action from a category to its double opposite. *)

(** 从范畴到其双重反范畴的恒等作用。 *)

Program Definition ToDoubleOpF {C : Cat}
  : Fct C ((C^op)^op)
  :=
  {|fobj X := X
  ; fmap X Y f := f
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation. intros f g Hfg. exact Hfg. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(** The identity action from the double opposite back to the category. *)

(** 从双重反范畴返回原范畴的恒等作用。 *)

Program Definition FromDoubleOpF {C : Cat}
  : Fct ((C^op)^op) C
  :=
  {|fobj X := X
  ; fmap X Y f := f
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation. intros f g Hfg. exact Hfg. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(** The double-opposite inclusion is full, with the same arrow as preimage. *)

(** 双重反范畴嵌入是满的，箭头的原像就是它本身。 *)

Definition to_double_op_full {C : Cat}
  : is_full (@ToDoubleOpF C).
Proof. intros X Y f. exists f. reflexivity. Defined.

(** Every double-opposite object is represented by itself. *)

(** 每个双重反范畴对象以自身为代表。 *)

Definition to_double_op_essentially_surjective {C : Cat}
  : is_essentially_surjective (@ToDoubleOpF C).
Proof.
  intro X. exists X.
  exact iso_refl.
Defined.

(** Removing double opposition is full with the identity preimage map. *)

(** 去除双重取反是满的，原像映射为恒等。 *)

Definition from_double_op_full {C : Cat}
  : is_full (@FromDoubleOpF C).
Proof. intros X Y f. exists f. reflexivity. Defined.

(** Removing double opposition is essentially surjective on objects. *)

(** 去除双重取反在对象上本质满。 *)

Definition from_double_op_essentially_surjective {C : Cat}
  : is_essentially_surjective (@FromDoubleOpF C).
Proof. intro X. exists X. exact iso_refl. Defined.
