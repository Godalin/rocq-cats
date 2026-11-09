From Cats Require Export STLC.Equivalence.

(** * Context Concatenation and Simultaneous Pairing

    Concatenation appends the second context in order. Its two variable
    inclusions and assignment pairing are independent of term equality. *)

(** * 上下文连接与同时配对

    连接按顺序追加第二个上下文；两个变量嵌入及赋值配对独立于项相等的选择。 *)

(** ** Context blocks and their components

    [Γ ++Ctx Δ] keeps the variables of [Γ] followed by those of [Δ].
    The two renamings select the left and right blocks; [sub_append] fills
    both blocks using one common source context. Its projection laws say
    that selecting either block returns the assignment used to build it.
    Its reconstruction law says that the two selected blocks determine an
    assignment into the concatenation.

    These decomposition equations are structural and pointwise. The
    beta/eta properness instance separately shows that assignment pairing
    also respects the specified equational relation. The product module
    combines these two ingredients to prove a categorical universal
    property with uniqueness in hom equality. *)

(** ** 上下文块及其分量

    [Γ ++Ctx Δ] 保留 [Γ] 的变量，再接上 [Δ] 的变量。两条重命名分别选取
    左右两块；[sub_append] 用同一个源上下文填充两块。投影律说明：选取任意
    一块，就恢复构造它时使用的赋值。重建律说明：这两块的限制决定了指向连接
    上下文的赋值。

    这些分解方程使用逐点结构相等。βη 保相等实例另外说明：赋值配对也保持
    指定的等式关系。积模块结合这两部分，证明在 Hom 相等意义下唯一的范畴
    泛性质。 *)

Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** Append a context, recursively preserving its newest-variable order. *)

(** 递归追加上下文，保持其最新变量顺序。 *)

Fixpoint CtxAppend {B : Type} (Γ Δ : Ctx B)
  : Ctx B
  := match Δ with
  | ctx_empty => Γ
  | ctx_snoc Δ A => CtxAppend Γ Δ ▻ A
  end.

Infix "++Ctx" := CtxAppend
  (at level 60, right associativity) : stlc_ctx_scope.

(** Include variables of the left context by successive weakenings. *)

(** 通过连续弱化嵌入左上下文中的变量。 *)

Fixpoint ren_append_l {B : Type} (Γ Δ : Ctx B)
  : Ren (Γ ++Ctx Δ) Γ
  := match Δ with
  | ctx_empty => idRen
  | ctx_snoc Δ A => ren_append_l Γ Δ ∘Ren wkRen
  end.

(** Include variables of the right context, lifting at each new binder. *)

(** 在每个新绑定处提升，以此嵌入右上下文中的变量。 *)

Fixpoint ren_append_r {B : Type} (Γ Δ : Ctx B)
  : Ren (Γ ++Ctx Δ) Δ
  := match Δ with
  | ctx_empty => ren_empty
  | ctx_snoc Δ A => (ren_append_r Γ Δ)^↑Ren
  end.

(** Pair two simultaneous assignments by extending along the right context. *)

(** 沿右上下文逐次扩张，将两个同时赋值配对。 *)

Fixpoint sub_append {B : Type} {Θ Γ Δ : Ctx B}
    (σ : Sub Θ Γ) (τ : Sub Θ Δ)
  : Sub Θ (Γ ++Ctx Δ)
  := match Δ as Δ return Sub Θ Δ → Sub Θ (Γ ++Ctx Δ) with
  | ctx_empty => λ _, σ
  | ctx_snoc Δ A => λ τ,
      sub_append σ (λ U x, τ U (var_succ x)) ▻Sub τ A var_zero
  end τ.

Notation "'⟨' σ ',' τ '⟩Sub'" := (sub_append σ τ) : stlc_sub_scope.

(** Pairing respects pointwise structural equality of both assignments. *)

(** 配对保持两个赋值的逐点结构相等。 *)

Global Instance sub_append_proper {B : Type} {Θ Γ Δ : Ctx B}
  : Proper (SubEq ==> SubEq ==> SubEq) (@sub_append B Θ Γ Δ).
Proof.
  induction Δ as [|Δ IH A]; intros σ σ' H τ τ' K; cbn.
  - exact H.
  - apply sub_extend_proper; [apply IH; [exact H |] | apply K].
    intros U x. apply K.
Qed.

(** Pairing also respects the specified pointwise beta/eta equality. *)

(** 配对也保持指定的逐点 βη 相等。 *)

Global Instance sub_append_tm_proper@{b e +} {B : Type@{b}}
    {Θ Γ Δ : Ctx B}
  : Proper
      (SubTmEq@{b e _} ==> SubTmEq@{b e _} ==> SubTmEq@{b e _})
      (@sub_append B Θ Γ Δ).
Proof.
  induction Δ as [|Δ IH A]; intros σ σ' H τ τ' K; cbn.
  - exact H.
  - apply sub_extend_tm_proper; [apply IH; [exact H |] | apply K].
    intros U x. apply K.
Defined.

(** Restriction of the paired assignment to the left recovers its first part. *)

(** 配对赋值沿左嵌入限制后恢复第一分量。 *)

Lemma sub_append_β1 {B : Type} {Θ Γ Δ : Ctx B}
    (σ : Sub Θ Γ) (τ : Sub Θ Δ) (A : Ty B) (x : Var Γ A)
  : (⟨σ, τ⟩Sub) A (ren_append_l Γ Δ A x) = σ A x.
Proof.
  induction Δ as [|Δ IH U]; cbn; [reflexivity | apply IH].
Qed.

(** Restriction to the right recovers the second assignment. *)

(** 沿右嵌入限制后恢复第二个赋值。 *)

Lemma sub_append_β2 {B : Type} {Θ Γ Δ : Ctx B}
    (σ : Sub Θ Γ) (τ : Sub Θ Δ) (A : Ty B) (x : Var Δ A)
  : (⟨σ, τ⟩Sub) A (ren_append_r Γ Δ A x) = τ A x.
Proof.
  induction Δ as [|Δ IH U]; [destruct x |].
  destruct x as [x | x]; cbn; [apply IH | destruct x; reflexivity].
Qed.

(** Pairing the restrictions of any assignment recovers it pointwise. *)

(** 任意赋值的两个限制重新配对后逐点恢复原赋值。 *)

Lemma sub_append_η {B : Type} {Θ Γ Δ : Ctx B}
    (σ : Sub Θ (Γ ++Ctx Δ))
  : (⟨λ A x, σ A (ren_append_l Γ Δ A x),
        λ A x, σ A (ren_append_r Γ Δ A x)⟩Sub) ≈Sub σ.
Proof.
  induction Δ as [|Δ IH U]; intros A x; cbn in *.
  - reflexivity.
  - destruct x as [x | x]; cbn.
    + apply (IH (λ V y, σ V (var_succ y))).
    + destruct x. reflexivity.
Qed.
