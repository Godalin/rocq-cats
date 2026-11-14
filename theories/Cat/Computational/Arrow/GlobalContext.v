From Cats Require Export
  Cat.Computational.Arrow.Pairing.
Local Open Scope computation_scope.

(** * Carrying Global Computations through Ordinary Inputs

    Fix an Arrow over selected finite products. Attach a terminal-input
    computation to an ordinary input, retaining its context. Prove pure
    substitution, ordered pairing and nested-context laws without
    exponentials, Monad structure or effect interchange. *)

(** * 普通输入携带全局计算

    固定选定有限积上的 Arrow，将终输入计算附在普通输入旁，并保留其上下文。
    不要求指数、Monad 结构或效应交换，证明纯替换、有序配对及嵌套上下文律。 *)

Section GlobalContext.
Context {C K : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (A : Arrow C K (@CartesianMonoidal C HT HP)).

(** Run a global computation while carrying an ordinary input unchanged. *)

(** 携带不变的普通输入，同时运行一项全局计算。 *)

Definition arrow_global_context {P : @Ob C} (X : @Ob C)
    (f : Hom (A 1) (A P))
  : Hom (A X) (A (X × P)%ob)
  := second[A; f; X] ∘ arr[A; ⟨id, !⟩].

(** Attaching a global result respects its computation equality. *)

(** 附加全局结果保持其计算相等。 *)

Global Instance arrow_global_context_proper {P : @Ob C} (X : @Ob C)
  : Proper (HomEq ==> HomEq) (@arrow_global_context P X).
Proof.
  intros f g H. unfold arrow_global_context. rewrite H. reflexivity.
Qed.

(** Inserting the ordinary terminal right context commutes with every
    computation. *)

(** 插入通常的右侧终上下文与每项计算交换。 *)

Lemma arrow_first_unit_inv {X Y : @Ob C} (k : Hom (A X) (A Y))
  : first[A; k; 1] ∘ arr[A; ⟨id, !⟩] ≈ arr[A; ⟨id, !⟩] ∘ k.
Proof.
  transitivity (arr[A; (⟨id, !⟩ : Hom Y (Y × 1))] ∘
    (arr[A; (π1 : Hom (Y × 1) Y)] ∘ first[A; k; 1]) ∘
      arr[A; (⟨id, !⟩ : Hom X (X × 1))]).
  - rewrite <- comp_assoc, <- functor_comp.
    apply comp_proper; [| reflexivity].
    rewrite product_comp_r, comp_id_l.
    assert (Hu : (⟨π1, ! ∘ (π1 : Hom (Y × 1) Y)⟩ :
      Hom (Y × 1) (Y × 1)) ≈ id).
    { apply product_eq_iff. split.
      - rewrite product_β1, comp_id_r. reflexivity.
      - rewrite product_β2, comp_id_r. transitivity (! : Hom (Y × 1) 1);
          [apply term_η | symmetry; apply term_η]. }
    rewrite Hu, functor_id, comp_id_l. reflexivity.
  - rewrite arrow_first_projection, !comp_assoc, <- functor_comp,
      product_β1, functor_id, comp_id_r. reflexivity.
Qed.

(** A prior computation runs once; the global result is then paired with its
    output. *)

(** 先前计算只运行一次，再将全局计算结果与其输出配对。 *)

Lemma arrow_global_context_post {P X Y : @Ob C}
    (g : Hom (A 1) (A P)) (k : Hom (A X) (A Y))
  : arrow_global_context Y g ∘ k ≈ k &&&[A] (g ∘ arr[A; !]).
Proof.
  pose proof (arrow_split_pre A k g (@id X) (! : Hom X 1)) as H.
  rewrite arrow_arr_id, comp_id_r in H.
  unfold arrow_global_context, arrow_fanout. rewrite <- H.
  unfold arrow_split. rewrite !comp_assoc, <- functor_comp.
  assert (Hi : ((@id X × (! : Hom X 1)) ∘ ⟨id, id⟩) ≈
    (⟨id, !⟩ : Hom X (X × 1))).
  { repeat first [rewrite cross_η | rewrite product_comp_r |
      rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
      rewrite comp_id_l | rewrite comp_id_r]. reflexivity. }
  rewrite Hi, arrow_first_unit_inv. reflexivity.
Qed.

(** Attaching a global result is ordered fanout with the pure input
    identity. *)

(** 附加全局结果就是与纯输入恒等做有序扇出。 *)

Lemma arrow_global_context_fanout {P : @Ob C} (X : @Ob C)
    (f : Hom (A 1) (A P))
  : arrow_global_context X f ≈ @id (A X) &&&[A] (f ∘ arr[A; !]).
Proof.
  pose proof (arrow_global_context_post f (@id (A X))) as H.
  rewrite comp_id_r in H. exact H.
Qed.

(** Attaching an ordered pair agrees with attaching the two global
    computations in sequence. *)

(** 附加有序配对，等于依次附加两项全局计算。 *)

Lemma arrow_global_context_pair {P Q : @Ob C} (X : @Ob C)
    (f : Hom (A 1) (A P)) (g : Hom (A 1) (A Q))
  : arrow_global_context X (f &&&[A] g) ≈
      arr[A; (@product_assoc C HP X P Q).1] ∘
        arrow_global_context (X × P)%ob g ∘ arrow_global_context X f.
Proof.
  rewrite comp_assoc, arrow_global_context_post, !arrow_global_context_fanout,
    arrow_fanout_pre, arrow_fanout_assoc. reflexivity.
Qed.

(** Mapping a global result is the pure product map after attachment. *)

(** 映射全局结果，等于附加后作纯积映射。 *)

Lemma arrow_global_context_map {P Q : @Ob C} (X : @Ob C)
    (f : Hom (A 1) (A P)) (h : Hom P Q)
  : arrow_global_context X (arr[A; h] ∘ f) ≈
      arr[A; @id X × h] ∘ arrow_global_context X f.
Proof.
  unfold arrow_global_context. rewrite arrow_second_comp,
    arrow_second_arr, comp_assoc. reflexivity.
Qed.

(** Pure input substitution commutes with attaching the same global
    computation. *)

(** 纯输入替换与附加同一项全局计算交换。 *)

Lemma arrow_global_context_pre {P X Y : @Ob C}
    (f : Hom (A 1) (A P)) (h : Hom X Y)
  : arrow_global_context Y f ∘ arr[A; h] ≈
      arr[A; h × @id P] ∘ arrow_global_context X f.
Proof.
  unfold arrow_global_context. rewrite !comp_assoc.
  rewrite <- (comp_assoc arr[A; h × @id P] (second[A; f; X])),
    arrow_second_natural, !comp_assoc.
  apply comp_proper; [reflexivity |].
  rewrite <- !functor_comp. apply functor_fmap_proper.
  repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r | rewrite term_comp_l]. reflexivity.
Qed.

(** Attaching a pure global value is ordinary pairing with that value. *)

(** 附加纯全局值，就是与该值作通常配对。 *)

Lemma arrow_global_context_pure {P : @Ob C} (X : @Ob C) (p : Hom 1 P)
  : arrow_global_context X arr[A; p] ≈ arr[A; ⟨id, p ∘ !⟩].
Proof.
  unfold arrow_global_context. rewrite arrow_second_arr, <- functor_comp.
  apply functor_fmap_proper.
  repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r]. reflexivity.
Qed.

(** Nested ordinary context is the selected reassociation of one larger
    context. *)

(** 嵌套通常上下文，等于对一个较大上下文作选定括号重排。 *)

Lemma arrow_global_context_nested {P : @Ob C} (Z X : @Ob C)
    (f : Hom (A 1) (A P))
  : second[A; arrow_global_context X f; Z] ≈
      arr[A; (@product_assoc C HP Z X P).1] ∘
        arrow_global_context (Z × X)%ob f.
Proof.
  unfold arrow_global_context. rewrite arrow_second_comp,
    arrow_second_arr, arrow_second_nested, !comp_assoc.
  apply comp_proper; [reflexivity |].
  apply comp_proper; [reflexivity |].
  rewrite <- functor_comp. apply functor_fmap_proper.
  unfold product_assoc. cbn [projT1 projT2].
  repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r | rewrite term_comp_l].
  rewrite product_pair_η. reflexivity.
Qed.
End GlobalContext.
