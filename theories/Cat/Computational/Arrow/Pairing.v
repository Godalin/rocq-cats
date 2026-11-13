From Cats Require Export
  Cat.Computational.Arrow.Cartesian.

Local Open Scope computation_scope.

(** * Ordered Pairing Laws for Computational Arrows

    Fix an Arrow over selected finite products. Prove pure substitution,
    reassociation and terminal-input unit laws for its derived split and
    fanout. Effects retain their execution order; no Monad or exponential
    structure is required. *)

(** * 计算 Arrow 的有序配对定律

    固定选定有限积上的 Arrow，证明其导出 split 与 fanout 的纯替换、括号
    重排和终输入单位律。效应保持执行次序，不要求 Monad 或指数结构。 *)

Section Pairing.
Context {C K : Cat} `{HT : !HasTerminal C} `{HP : !HasProduct C}
    (A : Arrow C K (@CartesianMonoidal C HT HP)).

(** Pure maps of both results distribute over ordered splitting. Only
    pure context maps commute with effects. *)

(** 两个结果的纯映射分配到有序 split；只有纯上下文映射与效应交换。 *)

Lemma arrow_split_post {X Y X' Y' Z Z' : @Ob C}
    (f : Hom (A X) (A Y)) (g : Hom (A X') (A Y'))
    (p : Hom Y Z) (q : Hom Y' Z')
  : arr[A; p × q] ∘ (f ***[A] g) ≈
      (arr[A; p] ∘ f) ***[A] (arr[A; q] ∘ g).
Proof.
  unfold arrow_split. rewrite arrow_first_comp, arrow_second_comp,
    arrow_first_arr, arrow_second_arr.
  transitivity ((arr[A; id × q] ∘ arr[A; p × id]) ∘
    (second[A; g; Y] ∘ first[A; f; X'])).
  - rewrite <- functor_comp, <- cross_comp, comp_id_l, comp_id_r.
    reflexivity.
  - rewrite !comp_assoc.
    rewrite <- (comp_assoc arr[A; p × id] (second[A; g; Y])
      (first[A; f; X'])), arrow_second_natural, !comp_assoc. reflexivity.
Qed.

(** Pure maps of the two inputs can be substituted before ordered splitting. *)

(** 两个输入的纯映射可在有序 split 之前代入。 *)

Lemma arrow_split_pre {X Y X' Y' W W' : @Ob C}
    (f : Hom (A X) (A Y)) (g : Hom (A X') (A Y'))
    (p : Hom W X) (q : Hom W' X')
  : (f ***[A] g) ∘ arr[A; p × q] ≈
      (f ∘ arr[A; p]) ***[A] (g ∘ arr[A; q]).
Proof.
  unfold arrow_split. rewrite arrow_first_comp, arrow_second_comp,
    arrow_first_arr, arrow_second_arr.
  transitivity ((second[A; g; Y] ∘ first[A; f; X']) ∘
    (arr[A; id × q] ∘ arr[A; p × id])).
  - rewrite <- functor_comp, <- cross_comp, comp_id_l, comp_id_r.
    reflexivity.
  - rewrite <- !comp_assoc.
    rewrite (comp_assoc (second[A; g; Y]) (first[A; f; X'])
      arr[A; id × q]), <- arrow_first_natural, <- !comp_assoc. reflexivity.
Qed.

(** Three ordered computations reassociate along the selected product
    associator. The three context naturality squares compose by [comp_square]. *)

(** 三个有序计算沿选定积结合子重排括号；三个上下文自然性方块通过
    [comp_square] 复合。 *)

Lemma arrow_split_assoc {X X' Y Y' Z Z' : @Ob C}
    (f : Hom (A X) (A X')) (g : Hom (A Y) (A Y'))
    (h : Hom (A Z) (A Z'))
  : arr[A; (@product_assoc C HP X' Y' Z').1] ∘
      ((f ***[A] g) ***[A] h) ≈
      (f ***[A] (g ***[A] h)) ∘
        arr[A; (@product_assoc C HP X Y Z).1].
Proof.
  unfold arrow_split. rewrite arrow_first_comp, arrow_second_comp.
  assert (Hh : arr[A; (@product_assoc C HP X' Y' Z').1] ∘
    second[A; h; (X' × Y')%ob] ≈
    second[A; second[A; h; Y']; X'] ∘
      arr[A; (@product_assoc C HP X' Y' Z).1]).
  { exact (arrow_context_assoc A h). }
  pose proof (comp_square _ _ _ _ _ _ _ (arrow_first_assoc A (Z := Y) (W := Z) f)
    (arrow_middle_assoc A (X := X') (Z := Z) g)) as Hfg.
  pose proof (comp_square _ _ _ _ _ _ _ Hfg Hh) as H.
  rewrite !comp_assoc in *. exact H.
Qed.

(** Pure result maps distribute over copying and ordered combination. *)

(** 纯结果映射分配到输入复制及有序组合。 *)

Lemma arrow_fanout_post {W X Y X' Y' : @Ob C}
    (f : Hom (A W) (A X)) (g : Hom (A W) (A Y))
    (p : Hom X X') (q : Hom Y Y')
  : arr[A; p × q] ∘ (f &&&[A] g) ≈
      (arr[A; p] ∘ f) &&&[A] (arr[A; q] ∘ g).
Proof.
  unfold arrow_fanout. rewrite <- comp_assoc, arrow_split_post. reflexivity.
Qed.

(** A pure shared-input substitution acts on both computations. *)

(** 纯共同输入替换作用于两个计算。 *)

Lemma arrow_fanout_pre {W V X Y : @Ob C}
    (f : Hom (A W) (A X)) (g : Hom (A W) (A Y)) (p : Hom V W)
  : (f &&&[A] g) ∘ arr[A; p] ≈
      (f ∘ arr[A; p]) &&&[A] (g ∘ arr[A; p]).
Proof.
  unfold arrow_fanout.
  transitivity (((f ***[A] g) ∘ arr[A; p × p]) ∘ arr[A; ⟨id, id⟩]).
  - rewrite !comp_assoc. apply comp_proper; [reflexivity |].
    rewrite <- !functor_comp. apply functor_fmap_proper.
    repeat first [rewrite cross_η | rewrite product_comp_r |
      rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
      rewrite comp_id_l | rewrite comp_id_r]. reflexivity.
  - rewrite arrow_split_pre. reflexivity.
Qed.

(** Combining two pure arrows gives their ordinary pairing. *)

(** 组合两个纯箭头，得到其通常配对。 *)

Lemma arrow_fanout_pure {W X Y : @Ob C} (f : Hom W X) (g : Hom W Y)
  : arr[A; f] &&&[A] arr[A; g] ≈ arr[A; ⟨f, g⟩].
Proof.
  unfold arrow_fanout, arrow_split.
  rewrite arrow_second_arr, arrow_first_arr, <- !functor_comp.
  apply functor_fmap_proper.
  repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r]. reflexivity.
Qed.

(** Ordered fanout is associative after pure reassociation, in every
    shared input context. No effect interchange is used. *)

(** 在每个共同输入上下文中，有序 fanout 经纯括号重排后满足结合律，不使用
    效应交换。 *)

Lemma arrow_fanout_assoc {W X Y Z : @Ob C}
    (f : Hom (A W) (A X)) (g : Hom (A W) (A Y)) (h : Hom (A W) (A Z))
  : arr[A; (@product_assoc C HP X Y Z).1] ∘ ((f &&&[A] g) &&&[A] h) ≈
      f &&&[A] (g &&&[A] h).
Proof.
  pose proof (arrow_split_pre (f ***[A] g) h
    (⟨id, id⟩ : Hom W (W × W)) (@id W)) as Hl.
  pose proof (arrow_split_pre f (g ***[A] h)
    (@id W) (⟨id, id⟩ : Hom W (W × W))) as Hr.
  rewrite arrow_arr_id in Hl, Hr.
  try rewrite comp_id_r in Hl.
  try rewrite comp_id_r in Hr.
  unfold arrow_fanout. rewrite <- Hl, <- Hr, <- !comp_assoc,
    arrow_split_assoc, !comp_assoc.
  apply comp_proper; [reflexivity |].
  rewrite <- !functor_comp. apply functor_fmap_proper.
  unfold product_assoc. cbn [projT1].
  repeat first [rewrite cross_η | rewrite product_comp_r |
    rewrite comp_assoc | rewrite product_β1 | rewrite product_β2 |
    rewrite comp_id_l | rewrite comp_id_r]. reflexivity.
Qed.

(** For terminal-input computations, pure identity is the left pairing unit. *)

(** 对于终输入计算，纯恒等为配对的左单位。 *)

Lemma arrow_fanout_unit_l {X : @Ob C} (f : Hom (A 1) (A X))
  : arr[A; (π2 : Hom (1 × X) X)] ∘ ((@id (A 1)) &&&[A] f) ≈ f.
Proof.
  unfold arrow_fanout, arrow_split.
  rewrite <- (arrow_arr_id A 1), arrow_first_arr, cross_id, arrow_arr_id,
    comp_id_r, <- comp_assoc, arrow_second_projection, comp_assoc,
    <- functor_comp, product_β2, arrow_arr_id, comp_id_r. reflexivity.
Qed.

(** For terminal-input computations, pure identity is also the right unit. *)

(** 对于终输入计算，纯恒等也为配对的右单位。 *)

Lemma arrow_fanout_unit_r {X : @Ob C} (f : Hom (A 1) (A X))
  : arr[A; (π1 : Hom (X × 1) X)] ∘ (f &&&[A] (@id (A 1))) ≈ f.
Proof.
  unfold arrow_fanout, arrow_split.
  rewrite <- (arrow_arr_id A 1), arrow_second_arr, cross_id, arrow_arr_id,
    comp_id_l, <- comp_assoc, arrow_first_projection, comp_assoc,
    <- functor_comp, product_β1, arrow_arr_id, comp_id_r. reflexivity.
Qed.

End Pairing.
