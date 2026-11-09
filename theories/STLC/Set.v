From Cats Require Export STLC.Equivalence.
From Cats.Set Require Export Morphism.

(** * Syntactic Sets and Substitution Maps

    Terms use beta/eta equality. Substitutions compare their assigned terms
    pointwise, retaining derivations without forming a quotient type. *)

(** * 语法广集与替换映射

    项使用 βη 相等；替换逐点比较所赋项，保留推导而不构造商类型。 *)

(** ** Keeping syntax while changing its specified equality

    [TmS Γ A] keeps [Tm Γ A] as its carrier and chooses [TmEq] as its
    equality. [SubS Δ Γ] likewise keeps simultaneous assignments and uses
    pointwise beta/eta equality. There is no quotient carrier and no need
    to choose representatives of equivalence classes.

    A respectful map must send equal inputs to equal outputs. The maps
    below package renaming, substitution and evaluation at a fixed term
    with exactly these preservation laws. Their function fields still
    compute on raw syntax. Distinguishing carrier data from equality
    witnesses is why the carrier universe [b] and witness universe [e]
    remain separate in these setoids and their maps. *)

(** ** 保留语法载体，指定另一种相等

    [TmS Γ A] 以 [Tm Γ A] 为载体，选取 [TmEq] 作为相等。[SubS Δ Γ]
    同样保留同时赋值，以逐点 βη 关系比较。这里没有商载体，也无须为等价类
    选择代表元。

    保相等映射必须把相等输入送到相等输出。下面的映射用恰好的保持律封装
    重命名、替换以及对固定项的赋值作用；函数字段仍然对原始语法计算。
    区分载体数据与相等见证，正是这些广集和映射保持载体宇宙 [b] 与见证宇宙
    [e] 分离的原因。 *)

Local Open Scope stlc_ctx_scope.
Local Open Scope stlc_tm_scope.
Local Open Scope stlc_ren_scope.
Local Open Scope stlc_sub_scope.

(** Terms in one context and type, with their specified beta/eta equality. *)

(** 固定上下文及类型中的项，以 βη 作为指定相等。 *)

Program Definition TmS@{b e +} {B : Type@{b}} (Γ : Ctx B) (A : Ty B)
  : SetC@{b e}
  :=
  {|carrier := Tm Γ A
  ; carrier_equiv := @TmEq@{b e _} B Γ A
  |}.

(** Substitutions with pointwise beta/eta equality, not raw [SubEq]. *)

(** 以逐点 βη 相等比较替换，使用的关系为 [SubTmEq]。 *)

Program Definition SubS@{b e +} {B : Type@{b}} (Δ Γ : Ctx B)
  : SetC@{b e}
  :=
  {|carrier := Sub Δ Γ
  ; carrier_equiv := @SubTmEq@{b e _} B Δ Γ
  |}.

(** A renaming induces a respectful map between the term sets. *)

(** 重命名诱导项广集之间的保相等映射。 *)

Program Definition tm_rename_resp@{b e +} {B : Type@{b}}
    {Γ Δ : Ctx B} {A : Ty B}
    (ρ : Ren Δ Γ)
  : TmS@{b e} Γ A →r TmS@{b e} Δ A
  :=
  {|func t := t⟨ρ⟩
  |}.
Next Obligation. intros t u H. apply tm_eq_rename. exact H. Defined.

(** A fixed substitution acts respectfully on the term set. *)

(** 固定替换在项广集上的作用保持指定相等。 *)

Program Definition tm_subst_resp@{b e +} {B : Type@{b}}
    {Γ Δ : Ctx B} {A : Ty B}
    (σ : Sub Δ Γ)
  : TmS@{b e} Γ A →r TmS@{b e} Δ A
  :=
  {|func t := t[σ]
  |}.
Next Obligation. intros t u H. apply tm_eq_subst. exact H. Defined.

(** A fixed term also acts respectfully on the set of assignments. *)

(** 固定项对赋值广集的作用也保持指定相等。 *)

Program Definition tm_subst_assignment_resp@{b e +} {B : Type@{b}}
    {Γ Δ : Ctx B} {A : Ty B} (t : Tm Γ A)
  : SubS@{b e} Δ Γ →r TmS@{b e} Δ A
  :=
  {|func σ := t[σ]
  |}.
Next Obligation. intros σ τ H. now apply subst_tm_ext. Defined.
