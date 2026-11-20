From Cats Require Export
  Cat.Profunctor.ComposeUniversal.
From Cats Require Import
  Cat.Core
  Cat.Product.Core
  Instance.Set.Core
  Instance.Set.Product.

Local Open Scope prof_scope.

(** * Natural Maps of Profunctor Composites

    Transform both input profunctors without changing the middle category.
    Components keep the execution order [P] then [Q]; the general coend map
    supplies the induced map. Only endpoint composition choices are needed. *)

(** * Profunctor 复合的自然映射

    变换两个输入 profunctor，保持中间范畴不变。分量保留先 [P] 再 [Q] 的执行
    顺序；一般 coend 映射提供诱导映射。只需端点处的复合选择。 *)

(** Pair the two transformation components at the separate middle indices.
    Naturality is the original naturality in each value coordinate. *)

(** 在分离的中间指标处配对两个变换分量；自然性就是各值坐标的原自然性。 *)

Program Definition ProfCompInputN@{u p +} {C D E : Cat}
    {Q Q' : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})}
    {P P' : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})}
    (β : Q ⇒ Q') (α : P ⇒ P') (X : @Ob C) (Z : @Ob E)
  : ProfCompKernel Q P X Z ⇒ ProfCompKernel Q' P' X Z
  :=
  {|nt AB := α (X,snd AB) × β (fst AB,Z)
  |}.
Next Obligation.
  intros [x y]. split.
  - exact (nat_naturality α
      (X := (X,snd X0)) (Y := (X,snd Y)) (id,snd f) x).
  - exact (nat_naturality β
      (X := (fst X0,Z)) (Y := (fst Y,Z)) (fst f,id) y).
Qed.

(** ** Kernel Map Laws

    Fix the three categories and value universes. Input maps respect the
    specified natural equality, preserve identities and composition, and
    commute with the outer boundary maps by the original naturality laws. *)

(** ** 核映射定律

    固定三个范畴和值宇宙。输入映射保持指定自然相等、恒等与复合，并由原自然性
    定律与外部边界映射交换。 *)

Section InputLaws.
Universes u p.
Context {C D E : Cat}.

(** Equal transformations induce equal maps of kernels. *)

(** 相等的变换诱导相等的核映射。 *)

Global Instance prof_comp_input_proper
    {Q Q' : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})}
    {P P' : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})}
    (X : @Ob C) (Z : @Ob E)
  : Proper (NatEq ==> NatEq ==> NatEq)
      (λ (β : Q ⇒ Q') (α : P ⇒ P'), ProfCompInputN β α X Z).
Proof.
  intros β β' H α α' K [A B] [x y]. split.
  - exact (K (X,B) x).
  - exact (H (A,Z) y).
Defined.

(** Input identities preserve both coordinates. *)

(** 输入恒等保持两个坐标。 *)

Lemma prof_comp_input_id
    (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _}))
    (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _}))
    (X : @Ob C) (Z : @Ob E)
  : ProfCompInputN (IdN (F := Q)) (IdN (F := P)) X Z ≈N IdN.
Proof. intros [A B] [x y]. split; reflexivity. Defined.

(** Successive input transformations compose coordinatewise. *)

(** 连续输入变换按坐标复合。 *)

Lemma prof_comp_input_comp
    {Q Q' Q'' : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})}
    {P P' P'' : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})}
    (β' : Q' ⇒ Q'') (β : Q ⇒ Q')
    (α' : P' ⇒ P'') (α : P ⇒ P') (X : @Ob C) (Z : @Ob E)
  : ProfCompInputN (β' ∘Nv β) (α' ∘Nv α) X Z ≈N
      (ProfCompInputN β' α' X Z ∘Nv ProfCompInputN β α X Z).
Proof. intros [A B] [x y]. split; reflexivity. Defined.

(** Input transformation and outer reindexing form a commuting square. *)

(** 输入变换与外部重索引组成交换方块。 *)

Lemma prof_comp_input_boundary
    {Q Q' : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})}
    {P P' : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})}
    (β : Q ⇒ Q') (α : P ⇒ P')
    {X X' : @Ob C} {Z Z' : @Ob E} (f : Hom X' X) (g : Hom Z Z')
  : (ProfCompInputN β α X' Z' ∘Nv ProfCompBoundaryN Q P f g)
      ≈N (ProfCompBoundaryN Q' P' f g ∘Nv
        ProfCompInputN β α X Z).
Proof.
  intros [A B] [x y]. split.
  - exact (prof_natural α f (id[B]) x).
  - exact (prof_natural β (id[A]) g y).
Defined.

End InputLaws.

(** The component is the general coend map. Its naturality reuses the
    commuting kernel square and coend composition, with only the two
    endpoint composition choices. Neither strength nor uniform choices
    over all profunctors are required. *)

(** 分量就是一般 coend 映射。其自然性复用核交换方块与 coend 复合，只需两个
    端点的复合选择，不要求强度或覆盖全部 profunctor 的统一选择。 *)

Program Definition ProfCompMapN@{u p +} {C D E : Cat}
    {Q Q' : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})}
    {P P' : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})}
    `{HC : !HasProfComp C D E Q P}
    `{HC' : !HasProfComp C D E Q' P'}
    (β : Q ⇒ Q') (α : P ⇒ P')
  : Q ∘Pr P ⇒ Q' ∘Pr P'
  :=
  {|nt XZ := coend_map (ProfCompInputN β α (fst XZ) (snd XZ))
  |}.
Next Obligation.
  transitivity (coend_map (ProfCompInputN β α (fst Y) (snd Y)
    ∘Nv ProfCompBoundaryN Q P (fst f) (snd f))).
  - symmetry. apply (@coend_map_comp D SetCat).
  - transitivity (coend_map
      (ProfCompBoundaryN Q' P' (fst f) (snd f)
        ∘Nv ProfCompInputN β α (fst X) (snd X))).
    + apply (@coend_map_proper D SetCat). apply prof_comp_input_boundary.
    + apply (@coend_map_comp D SetCat).
Qed.

(** ** Maps between Selected Composites

    Work with explicit endpoint choices. Coend functoriality proves the
    map laws and supplies chosen natural inverses; no comparison of law
    records or equality of choice families is needed. *)

(** ** 选定复合之间的映射

    使用显式端点选择。coend 函子性证明映射定律并提供选定自然逆，不比较定律
    记录，也不要求选择族相等。 *)

Section MapLaws.
Universes u p.
Context {C D E : Cat}.

(** Composite maps respect the specified equality of both transformations. *)

(** 复合映射保持两个变换的指定相等。 *)

Global Instance prof_comp_map_proper
    {Q Q' : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})}
    {P P' : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})}
    `{HC : !HasProfComp C D E Q P}
    `{HC' : !HasProfComp C D E Q' P'}
  : Proper (NatEq ==> NatEq ==> NatEq)
      (λ (β : Q ⇒ Q') (α : P ⇒ P'), ProfCompMapN β α).
Proof.
  intros β β' H α α' K [X Z].
  apply (@coend_map_proper D SetCat
    (ProfCompKernel Q P X Z) (ProfCompKernel Q' P' X Z)
    (@hasProfCompCoend C D E Q P HC X Z)
    (@hasProfCompCoend C D E Q' P' HC' X Z)).
  exact (@prof_comp_input_proper C D E Q Q' P P' X Z β β' H α α' K).
Defined.

(** Identity transformations give the identity on the same selected composite. *)

(** 恒等变换给出同一选定复合上的恒等。 *)

Lemma prof_comp_map_id
    (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _}))
    (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _}))
    `{HC : !HasProfComp C D E Q P}
  : ProfCompMapN (IdN (F := Q)) (IdN (F := P)) ≈N IdN.
Proof.
  intros [X Z].
  transitivity (@coend_map D SetCat
    (ProfCompKernel Q P X Z) (ProfCompKernel Q P X Z)
    (@hasProfCompCoend C D E Q P HC X Z)
    (@hasProfCompCoend C D E Q P HC X Z) IdN).
  - apply (@coend_map_proper D SetCat). apply prof_comp_input_id.
  - apply (@coend_map_id D SetCat).
Defined.

(** Input composition is preserved with only its three endpoint choices. *)

(** 只需三个端点选择即可保持输入复合。 *)

Lemma prof_comp_map_comp
    {Q Q' Q'' : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})}
    {P P' P'' : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})}
    `{HC : !HasProfComp C D E Q P}
    `{HC' : !HasProfComp C D E Q' P'}
    `{HC'' : !HasProfComp C D E Q'' P''}
    (β' : Q' ⇒ Q'') (β : Q ⇒ Q') (α' : P' ⇒ P'') (α : P ⇒ P')
  : ProfCompMapN (β' ∘Nv β) (α' ∘Nv α) ≈N
      (ProfCompMapN β' α' ∘Nv ProfCompMapN β α).
Proof.
  intros [X Z].
  transitivity (@coend_map D SetCat
    (ProfCompKernel Q P X Z) (ProfCompKernel Q'' P'' X Z)
    (@hasProfCompCoend C D E Q P HC X Z)
    (@hasProfCompCoend C D E Q'' P'' HC'' X Z)
    (ProfCompInputN β' α' X Z ∘Nv ProfCompInputN β α X Z)).
  - apply (@coend_map_proper D SetCat). apply prof_comp_input_comp.
  - apply (@coend_map_comp D SetCat).
Defined.

(** Supplied natural inverses induce the same map construction in reverse.
    Both inverse equations use the original specified natural equality. *)

(** 给定自然逆在反向诱导同一映射构造；两条互逆方程使用原指定自然相等。 *)

Definition prof_comp_map_iso
    {Q Q' : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})}
    {P P' : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})}
    `{HC : !HasProfComp C D E Q P}
    `{HC' : !HasProfComp C D E Q' P'}
    (β : Q ⇒ Q') (α : P ⇒ P') (Hβ : β ⦂ Q ≅N Q') (Hα : α ⦂ P ≅N P')
  : ProfCompMapN β α ⦂ Q ∘Pr P ≅N Q' ∘Pr P'.
Proof.
  intros [X Z]. exists (ProfCompMapN (β ^-1N Hβ) (α ^-1N Hα) (X,Z)).
  split; unfold is_linv_of, is_rinv_of.
  - transitivity (ProfCompMapN
      ((β ^-1N Hβ) ∘Nv β) ((α ^-1N Hα) ∘Nv α) (X,Z)).
    + symmetry. exact (@prof_comp_map_comp
        Q Q' Q P P' P HC HC' HC (β ^-1N Hβ) β (α ^-1N Hα) α (X,Z)).
    + transitivity (ProfCompMapN (IdN (F := Q)) (IdN (F := P)) (X,Z)).
      * exact (@prof_comp_map_proper Q Q P P HC HC
          ((β ^-1N Hβ) ∘Nv β) IdN (λ U, fst (Hβ U).2)
          ((α ^-1N Hα) ∘Nv α) IdN (λ U, fst (Hα U).2) (X,Z)).
      * exact (@prof_comp_map_id Q P HC (X,Z)).
  - transitivity (ProfCompMapN
      (β ∘Nv (β ^-1N Hβ)) (α ∘Nv (α ^-1N Hα)) (X,Z)).
    + symmetry. exact (@prof_comp_map_comp
        Q' Q Q' P' P P' HC' HC HC' β (β ^-1N Hβ) α (α ^-1N Hα) (X,Z)).
    + transitivity (ProfCompMapN (IdN (F := Q')) (IdN (F := P')) (X,Z)).
      * exact (@prof_comp_map_proper Q' Q' P' P' HC' HC'
          (β ∘Nv (β ^-1N Hβ)) IdN (λ U, snd (Hβ U).2)
          (α ∘Nv (α ^-1N Hα)) IdN (λ U, snd (Hα U).2) (X,Z)).
      * exact (@prof_comp_map_id Q' P' HC' (X,Z)).
Defined.

End MapLaws.

(** ** Input Maps on Generators and Descent

    Fix one outer boundary and just the two kernel coends. The general
    coend computation and descent laws describe transformation of every
    generating pair and every balanced outgoing operation. *)

(** ** 生成元及下降上的输入映射

    固定一个外部边界，只选取两个核的 coend。一般 coend 计算与下降定律描述
    每个生成对及每个平衡出射操作的变换。 *)

Section InputGenerators.
Universes u p.
Context {C D E : Cat}.
Context {Q Q' : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})}.
Context {P P' : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})}.
Context (β : Q ⇒ Q') (α : P ⇒ P').
Context {X : @Ob C} {Z : @Ob E}.
Context `{HC : !HasCoend SetCat (ProfCompKernel Q P X Z)}.
Context `{HC' : !HasCoend SetCat (ProfCompKernel Q' P' X Z)}.

(** Each factor receives its own transformation component, in order. *)

(** 各因子按原顺序接受各自的变换分量。 *)

Lemma prof_comp_input_inject (Y : @Ob D)
    (x : P (X,Y)) (y : Q (Y,Z))
  : coend_map (ProfCompInputN β α X Z) (ιPr[Q; P; Y] (x,y)) ≈S
      ιPr[Q'; P'; Y] (α (X,Y) x,β (Y,Z) y).
Proof. exact (coend_map_β (ProfCompInputN β α X Z) Y (x,y)). Defined.

(** Descending a transformed operation agrees with applying the input map
    followed by the original descent. Only these two kernel coends are needed. *)

(** 变换后操作的下降，等于先作用输入映射再进行原下降；只需这两个核的 coend。 *)

Lemma prof_comp_desc_input {W : SetC}
    (κ : Cowedge (ProfCompKernel Q' P' X Z) W)
  : prof_comp_desc Q P
      (cowedge_precompose κ (ProfCompInputN β α X Z)) ≈f
      (prof_comp_desc Q' P' κ ∘r
        coend_map (ProfCompInputN β α X Z)).
Proof. exact (coend_desc_map (ProfCompInputN β α X Z) κ). Defined.

End InputGenerators.

(** The natural map of whole composites has that same generator equation. *)

(** 完整复合的自然映射具有同一生成元方程。 *)

Lemma prof_comp_map_inject@{u p +} {C D E : Cat}
    {Q Q' : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _})}
    {P P' : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})}
    `{HC : !HasProfComp C D E Q P}
    `{HC' : !HasProfComp C D E Q' P'}
    (β : Q ⇒ Q') (α : P ⇒ P') (X : @Ob C) (Y : @Ob D) (Z : @Ob E)
    (x : P (X,Y)) (y : Q (Y,Z))
  : ProfCompMapN β α (X,Z) (ιPr[Q; P; Y] (x,y)) ≈S
      ιPr[Q'; P'; Y] (α (X,Y) x,β (Y,Z) y).
Proof. exact (prof_comp_input_inject β α Y x y). Defined.

(** A supplied family of composition choices gives the bifunctor. Its
    arguments follow ordinary composition order [Q,P], whereas generators
    retain execution order [P,Q]. This family is explicit and installs no
    global model or existence claim. Associators, units, coherence and
    strength on composites remain separate constructions. *)

(** 给定复合选择族得到双函子。其变元遵循通常复合顺序 [Q,P]，生成元则保留
    执行顺序 [P,Q]。该选择族是显式参数，不安装全局模型或存在断言。结合子、
    单位、相干及复合上的强度仍为独立构造。 *)

Program Definition ProfCompF@{u p +} (C D E : Cat)
    (HC : ∀ (Q : Fct ((D^op) ×C E) (SetCat@{u p _ _ _ _ _}))
      (P : Fct ((C^op) ×C D) (SetCat@{u p _ _ _ _ _})),
      HasProfComp C D E Q P)
  : Fct (ProfCat D E ×C ProfCat C D) (ProfCat C E)
  :=
  {|fobj QP := @ProfComp C D E (fst QP) (snd QP)
      (HC (fst QP) (snd QP))
  ; fmap QP QP' βα := @ProfCompMapN C D E
      (fst QP) (fst QP') (snd QP) (snd QP')
      (HC (fst QP) (snd QP)) (HC (fst QP') (snd QP'))
      (fst βα) (snd βα)
  ; isFct :=
      {|fmap_proper := _
      ; fmap_id := _
      ; fmap_comp := _
      |}
  |}.
Next Obligation.
  intros [β α] [β' α'] [H K].
  exact (@prof_comp_map_proper C D E _ _ _ _ _ _ β β' H α α' K).
Qed.
Next Obligation. destruct X as [Q P]. apply prof_comp_map_id. Qed.
Next Obligation.
  destruct X as [Q P], Y as [Q' P'], Z as [Q'' P''],
    f as [β' α'], g as [β α].
  apply prof_comp_map_comp.
Qed.
