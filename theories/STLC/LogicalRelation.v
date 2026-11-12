From Cats Require Export STLC.EvaluationEquivalence.
From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core
  Instance.Set.Lift
  Instance.Set.Kripke.

(** * A Logical Relation for Normalization

    Semantic equality compares values with values. Correctness also needs
    a bridge from syntax to values. At base types the bridge is beta/eta
    equality with the stored neutral; at products it observes projections;
    at functions it tests related arguments in every future world. Unit
    requires no observation, since its eta equation identifies every term.

    The relation is Type valued and keeps its computational witnesses.
    Its auxiliary size can contain both semantic values and equational
    evidence, without ordering their independent bounds [s] and [e]. *)

(** * 正规化的逻辑关系

    语义相等比较值与值；正确性还需要从语法到值的桥梁。基类型处使用与所存
    中性项的 βη 相等，积类型处观察投影，函数类型处在每个未来世界测试相关
    实参。单位类型无须观察，因为其 η 方程识别所有项。

    此关系取值于 Type 并保留计算见证。辅助大小可同时容纳语义值与等式证据，
    无须规定两者独立界限 [s] 与 [e] 的大小顺序。 *)

Local Open Scope stlc_ty_scope.
Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.
Local Open Scope stlc_tm_scope.

(** ** Realization for a Fixed Signature and Evidence Bound

    Fix [B] with independent world equality, semantic, world-law and
    equational evidence bounds. Evidence must contain the signature level.
    Construct realization, its transport laws and the evaluation
    fundamental lemma; auxiliary sizes accommodate the relation itself. *)

(** ** 固定签名与证据界限的实现关系

    固定 [B] 及独立的世界相等、语义、世界定律和等式证据界限。证据须容纳签名
    层级。构造实现关系、其输运律及求值基本引理；辅助大小容纳关系本身。 *)

Section LogicalRelation.
Universes b r s l e.
Constraint b <= e.
Context {B : Type@{b}}.

(** A term realizes a semantic value when its type-directed observations
    agree with that value. The arrow clause quantifies future renamings,
    syntax arguments, values and their relation witnesses. *)

(** 当项的类型导向观察与语义值相符时，称该项实现此值。箭头条款量化未来
    重命名、语法实参、语义值及其关系见证。 *)

Fixpoint Realizes (A : Ty B)
  : ∀ Γ : Ctx B, Tm Γ A →
      (SemF A : Functor ((RenamingCat B : Cat@{b b r l l})^op)
        SetCat@{s s _ _ _ _ _}) Γ → Type.
Proof.
  destruct A as [p | | A U | A U]; intros Γ t v.
  - exact (TmEq@{b e _} t (embed_ne (lower v))).
  - exact unit.
  - exact (Realizes A Γ (π₁ t) (fst v) *
      Realizes U Γ (π₂ t) (snd v))%type.
  - exact (∀ (Δ : Ctx B) (ρ : Ren Δ Γ) (u : Tm Δ A) (a : SemF A Δ),
      Realizes A Δ u a → Realizes U Δ (t⟨ρ⟩ · u) (v Δ ρ a)).
Defined.

(** Replacing a term by a beta/eta equal term preserves realization. *)

(** 将项换成 βη 相等的项，保持实现关系。 *)

Lemma realizes_tm_eq (A : Ty B)
  : ∀ (Γ : Ctx B) (t u : Tm Γ A) (v : SemF A Γ),
      TmEq@{b e _} t u → Realizes A Γ t v → Realizes A Γ u v.
Proof.
  induction A as [p | | A IHA U IHU | A IHA U IHU];
    intros Γ t u v h k.
  - exact (tm_eq_trans (tm_eq_sym h) k).
  - exact tt.
  - split.
    + exact (IHA Γ (π₁ t) (π₁ u) (fst v) (tm_eq_fst h) (fst k)).
    + exact (IHU Γ (π₂ t) (π₂ u) (snd v) (tm_eq_snd h) (snd k)).
  - intros Δ ρ w a q.
    exact (IHU Δ (t⟨ρ⟩ · w) (u⟨ρ⟩ · w) (v Δ ρ a)
      (tm_eq_app (tm_eq_rename h Δ ρ) (tm_eq_refl w)) (k Δ ρ w a q)).
Defined.

(** Equivalent values have the same realizing terms. Base-type equality
    unwraps the lifted neutral equality; function equality is observed at
    each future application. Stored laws are never compared. *)

(** 等价的值有相同的实现项。基类型相等解包提升后的中性项相等；函数相等在
    每个未来应用处观察。从不比较保存的定律。 *)

Lemma realizes_sem_eq (A : Ty B)
  : ∀ (Γ : Ctx B) (t : Tm Γ A) (v w : SemF A Γ),
      v ≈S w → Realizes A Γ t v → Realizes A Γ t w.
Proof.
  induction A as [p | | A IHA U IHU | A IHA U IHU];
    intros Γ t v w h k.
  - destruct v as [n], w as [m], h as [h]. cbn in h. destruct h. exact k.
  - exact tt.
  - destruct v as [v v'], w as [w w'], h as [h h']. split.
    + exact (IHA Γ (π₁ t) v w h (fst k)).
    + exact (IHU Γ (π₂ t) v' w' h' (snd k)).
  - intros Δ ρ u a q.
    exact (IHU Δ (t⟨ρ⟩ · u) (v Δ ρ a) (w Δ ρ a)
      (h Δ ρ a) (k Δ ρ u a q)).
Defined.

(** The logical relation respects both designated equalities. This
    registration exposes its two transport lemmas to setoid reasoning;
    logical equivalence keeps maps in both directions. *)

(** 逻辑关系保持两边的指定相等。此注册将两个输运引理提供给广集推理；逻辑
    等价保留双向映射。 *)

Global Instance Realizes_proper (A : Ty B) (Γ : Ctx B)
  : Proper (TmEq@{b e _} ==> [≈S] ==> iffT) (Realizes A Γ).
Proof.
  intros t u h v w k. split; intros q.
  - exact (realizes_sem_eq A Γ u v w k
      (realizes_tm_eq A Γ t u v h q)).
  - exact (realizes_sem_eq A Γ t w v (symmetry k)
      (realizes_tm_eq A Γ u t w (tm_eq_sym h) q)).
Defined.

(** Realization commutes with changing the world. The function clause
    composes future renamings; it uses structural composition of syntax
    and the existing restriction action of coherent Kripke functions. *)

(** 实现关系与更换世界交换。函数条款复合未来重命名，使用语法的结构复合律
    与相容 Kripke 函数已有的限制作用。 *)

Lemma realizes_rename (A : Ty B)
  : ∀ (Γ Δ : Ctx B) (ρ : Ren Δ Γ) (t : Tm Γ A) (v : SemF A Γ),
      Realizes A Γ t v →
      Realizes A Δ t⟨ρ⟩ (fmap (SemF A) ρ v).
Proof.
  induction A as [p | | A IHA U IHU | A IHA U IHU];
    intros Γ Δ ρ t v h.
  - change (TmEq t⟨ρ⟩ (embed_ne ((lower v)⟨ρ⟩ne))).
    rewrite embed_rename_ne. exact (tm_eq_rename h Δ ρ).
  - exact tt.
  - split.
    + exact (IHA Γ Δ ρ (π₁ t) (fst v) (fst h)).
    + exact (IHU Γ Δ ρ (π₂ t) (snd v) (snd h)).
  - intros Θ τ u a k.
    change (Realizes U Θ (t⟨ρ⟩⟨τ⟩ · u) (v Θ (ρ ∘Ren τ) a)).
    rewrite rename_comp. exact (h Θ (ρ ∘Ren τ) u a k).
Defined.

(** Reification correctness and neutral reflection are proved together by
    induction on types. At an arrow, reification tests the fresh reflected
    variable, while reflection quotes each related argument before forming
    a blocked application. The two directions therefore need each other at
    the smaller domain type. *)

(** 实化正确性与中性反射沿类型共同归纳证明。箭头处，实化测试新反射变量；
    反射则先实化相关实参，再形成被阻塞应用。因此两个方向在较小的定义域
    类型处相互依赖。 *)

Lemma realizes_reification (A : Ty B)
  : (∀ (Γ : Ctx B) (t : Tm Γ A) (v : SemF A Γ),
      Realizes A Γ t v →
      TmEq@{b e _} t (embed_nf (reify_sem (TypeReification A) Γ v))) *
    (∀ (Γ : Ctx B) (t : Tm Γ A) (n : Ne Γ A),
      TmEq@{b e _} t (embed_ne n) →
      Realizes A Γ t (reflect_ne (TypeReification A) Γ n)).
Proof.
  induction A as [p | | A [quoteA reflectA] U [quoteU reflectU] |
    A [quoteA reflectA] U [quoteU reflectU]]; split.
  - intros Γ t v h. exact h.
  - intros Γ t n h. exact h.
  - intros Γ t v h. apply tm_eq_unit_η.
  - intros Γ t n h. exact tt.
  - intros Γ t v [h k].
    refine (tm_eq_trans (tm_eq_sym (tm_eq_product_η t)) _).
    exact (tm_eq_pair (quoteA Γ (π₁ t) (fst v) h)
      (quoteU Γ (π₂ t) (snd v) k)).
  - intros Γ t n h. split.
    + exact (reflectA Γ (π₁ t) (ne_fst n) (tm_eq_fst h)).
    + exact (reflectU Γ (π₂ t) (ne_snd n) (tm_eq_snd h)).
  - intros Γ t v h.
    refine (tm_eq_trans (tm_eq_sym (tm_eq_function_η t)) _).
    apply tm_eq_lam.
    exact (quoteU (Γ ▻ A) (t⟨wkRen⟩ · (# var_zero))
      (v (Γ ▻ A) wkRen
        (reflect_ne (TypeReification A) (Γ ▻ A) (ne_var var_zero)))
      (h (Γ ▻ A) wkRen (# var_zero)
        (reflect_ne (TypeReification A) (Γ ▻ A) (ne_var var_zero))
        (reflectA (Γ ▻ A) (# var_zero) (ne_var var_zero)
          (tm_eq_refl _)))).
  - intros Γ t n h Δ ρ u a k.
    change (Realizes U Δ (t⟨ρ⟩ · u)
      (reflect_ne (TypeReification U) Δ
        (ne_app n⟨ρ⟩ne (reify_sem (TypeReification A) Δ a)))).
    apply reflectU. cbn [embed_ne]. apply tm_eq_app.
    + rewrite embed_rename_ne. exact (tm_eq_rename h Δ ρ).
    + exact (quoteA Δ u a k).
Defined.

(** A related value reifies to syntax beta/eta equal to its realizing term. *)

(** 相关的值实化为与其实现项 βη 相等的语法。 *)

Definition realizes_reify (A : Ty B)
  : ∀ (Γ : Ctx B) (t : Tm Γ A) (v : SemF A Γ),
      Realizes A Γ t v →
      TmEq@{b e _} t (embed_nf (reify_sem (TypeReification A) Γ v))
  := fst (realizes_reification A).

(** A term equal to a neutral realizes that neutral's reflection. *)

(** 与中性项相等的项，实现该中性项的反射。 *)

Definition realizes_reflect (A : Ty B)
  : ∀ (Γ : Ctx B) (t : Tm Γ A) (n : Ne Γ A),
      TmEq@{b e _} t (embed_ne n) →
      Realizes A Γ t (reflect_ne (TypeReification A) Γ n)
  := snd (realizes_reification A).

(** A syntactic substitution and a semantic environment are related when
    each assigned term realizes the corresponding looked-up value. *)

(** 当每个赋值项实现对应查找值时，语法替换与语义环境相关。 *)

Definition EnvRealizes (Γ Δ : Ctx B) (σ : Sub Δ Γ) (γ : EnvF Γ Δ)
  : Type
  := ∀ (A : Ty B) (x : Var Γ A),
      Realizes A Δ (σ A x) (EnvLookupN Γ A x Δ γ).

(** Reindex all related assignments and environment entries together.
    Lookup naturality identifies the two ways to obtain each new value. *)

(** 同时重索引相关赋值与环境分量。查找的自然性识别取得新值的两条路径。 *)

Lemma env_realizes_rename {Γ Δ Θ : Ctx B}
    (σ : Sub Δ Γ) (γ : EnvF Γ Δ) (ρ : Ren Θ Δ)
    (h : EnvRealizes Γ Δ σ γ)
  : EnvRealizes Γ Θ (λ A x, (σ A x)⟨ρ⟩) (fmap (EnvF Γ) ρ γ).
Proof.
  intros A x.
  refine (realizes_sem_eq A Θ (σ A x)⟨ρ⟩ _ _ _
    (realizes_rename A Δ Θ ρ (σ A x) _ (h A x))).
  symmetry. exact (nt_naturality (EnvLookupN Γ A x) ρ γ).
Defined.

(** Extending both assignments by a related term/value preserves their
    pointwise relation, including the fresh binder marker. *)

(** 按相关的项与值扩张两边赋值，保持逐点关系，包括新的绑定标记。 *)

Lemma env_realizes_extend {Γ Δ : Ctx B} {A : Ty B}
    (σ : Sub Δ Γ) (γ : EnvF Γ Δ) (t : Tm Δ A) (a : SemF A Δ)
    (h : EnvRealizes Γ Δ σ γ) (k : Realizes A Δ t a)
  : EnvRealizes (Γ ▻ A) Δ (σ ▻Sub t) (γ, a).
Proof.
  intros U [x | x].
  - exact (h U x).
  - destruct x. exact k.
Defined.

(** Any environment whose entries are the reflected variables is related
    to the identity substitution. Only componentwise semantic equality is
    required, so this applies to any representation of that environment. *)

(** 只要环境分量是反射变量，该环境就与恒等替换相关。只要求逐分量语义相等，
    因而适用于该环境的任意表示。 *)

Lemma env_realizes_reflected (Γ : Ctx B) (γ : EnvF Γ Γ)
    (h : ∀ (A : Ty B) (x : Var Γ A),
      EnvLookupN Γ A x Γ γ ≈S
        reflect_ne (TypeReification A) Γ (ne_var x))
  : EnvRealizes Γ Γ idSub γ.
Proof.
  intros A x.
  refine (realizes_sem_eq A Γ (# x) _ _ _
    (realizes_reflect A Γ (# x) (ne_var x) (tm_eq_refl _))).
  symmetry. exact (h A x).
Defined.

(** The fundamental lemma: a term substituted by related syntax realizes
    its evaluation in the related environment. Under a lambda, reindex the
    old assignments and extend both environments by the tested argument.
    Function beta and the raw binder-substitution law connect the body to
    that application; semantic evaluation already has the required form. *)

(** 基本引理：按相关语法替换后的项，实现在相关环境中的求值结果。λ 下先
    重索引旧赋值，再按受测实参扩张两边环境。函数 β 与原始绑定替换律将项体
    接到该应用；语义求值本身已具有所需形式。 *)

Lemma eval_realizes {Γ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : ∀ (Δ : Ctx B) (σ : Sub Δ Γ) (γ : EnvF Γ Δ),
      EnvRealizes Γ Δ σ γ → Realizes A Δ t[σ] (eval t Δ γ).
Proof.
  induction t as [Γ A x | Γ | Γ A U t IHt u IHu |
    Γ A U t IH | Γ A U t IH | Γ A U t IH |
    Γ A U f IHf a IHa]; intros Δ σ γ h.
  - exact (h A x).
  - exact tt.
  - split.
    + exact (realizes_tm_eq A Δ t[σ] (π₁ (⟨t[σ], u[σ]⟩)) _
        (tm_eq_sym (tm_eq_product_β1 _ _)) (IHt Δ σ γ h)).
    + exact (realizes_tm_eq U Δ u[σ] (π₂ (⟨t[σ], u[σ]⟩)) _
        (tm_eq_sym (tm_eq_product_β2 _ _)) (IHu Δ σ γ h)).
  - exact (fst (IH Δ σ γ h)).
  - exact (snd (IH Δ σ γ h)).
  - intros Θ ρ u a k.
    change (Realizes U Θ ((ƛ t)[σ]⟨ρ⟩ · u)
      (eval t Θ (fmap (EnvF Γ) ρ γ, a))).
    refine (realizes_tm_eq U Θ
      t[(λ V x, (σ V x)⟨ρ⟩) ▻Sub u]
      ((ƛ t)[σ]⟨ρ⟩ · u) _ _ _).
    + apply tm_eq_sym.
      change (TmEq ((ƛ (t[σ^↑Sub]⟨ρ^↑Ren⟩)) · u)
        t[(λ V x, (σ V x)⟨ρ⟩) ▻Sub u]).
      refine (tm_eq_trans (tm_eq_function_β _ _) _).
      apply tm_eq_of_eq. exact (subst_lift_rename_single t σ ρ u).
    + exact (IH Θ _ _ (env_realizes_extend _ _ u a
        (env_realizes_rename σ γ ρ h) k)).
  - pose proof (IHf Δ σ γ h Δ idRen a[σ] (eval a Δ γ)
      (IHa Δ σ γ h)) as k.
    rewrite rename_id in k. exact k.
Defined.

End LogicalRelation.
