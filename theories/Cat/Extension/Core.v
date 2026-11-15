From Cats Require Export
  Cat.Pushout.
From Cats Require Import
  Cat.Core.

(** * Constructive Map Extensions and Attachments

    An extension retains an actual map and its restriction equation.
    Extension targets are closed under composition and pushout of the
    domain map. For a pushout, first extend on its new piece, then use
    the existing universal mediator. No uniqueness of extensions on
    that new piece is assumed; only the mediator for fixed piece values
    is unique. The pushout theory itself is the original opposite
    pullback construction, rather than another universal-property proof. *)

(** * 构造性映射延拓与附着

    延拓保留实际映射及其限制方程。延拓目标沿域映射的复合和推出保持；对推出，
    先在新块上延拓，再使用已有泛中介。不要求新块上的延拓唯一，只对固定块值
    的中介使用唯一性。推出理论本身复用原反拉回构造，不另证一份泛性质。 *)

(** @lang both
%\begin{center}
\begin{tikzcd}[column sep=large,row sep=large]
Z \arrow[r,"f"] \arrow[d,"g"'] & A \arrow[d,"i"]
  \arrow[ddr,bend left=25,"a"] & \\
B \arrow[r,"j"'] \arrow[drr,bend right=20,"b"']
  & P \arrow[dr,dashed,"k"] & \\
&& Q
\end{tikzcd}
\qquad $b\circ g\approx a\circ f.$
\end{center}%
*)

(** ** Extension Equations in an Arbitrary Category

    Fix the ambient category. All equations use its specified Hom
    equality, retaining independent arrow and equality-witness sizes. *)

(** ** 任意范畴中的延拓方程

    固定环境范畴；全部方程使用其指定 Hom 相等，保留独立的箭头与相等见证大小。 *)

Section Extensions.
Context {C : Cat}.

(** A candidate extension restricts to the prescribed map. *)

(** 候选延拓限制后等于给定映射。 *)

Definition is_map_extension {A B Q : @Ob C}
    (i : Hom A B) (a : Hom A Q) (b : Hom B Q)
  : Type
  := b ∘ i ≈ a.

(** Every map on A has a retained extension across i. This Type-valued
    property supplies witnesses; no global model choice is registered. *)

(** A 上每条映射都有一份沿 i 的保留延拓。此 Type 值性质提供见证，不注册全局模型选择。 *)

Definition is_extension_target {A B : @Ob C} (i : Hom A B) (Q : @Ob C)
  : Type
  := ∀ a : Hom A Q, ∃ b : Hom B Q, is_map_extension i a b.

(** The identity requires only the original map itself. *)

(** 恒等映射只需原映射本身。 *)

Definition map_extension_target_id (A Q : @Ob C)
  : is_extension_target (id : Hom A A) Q.
Proof. intros a. exists a. apply comp_id_r. Defined.

(** Successively extend across the two supplied maps, without an
    assumption that the supplied extension operations are respectful. *)

(** 沿两条给定映射依次延拓，不假设给定延拓操作保持相等。 *)

Definition map_extension_target_comp {A B D Q : @Ob C}
    (i : Hom A B) (j : Hom B D)
    (Ei : is_extension_target i Q) (Ej : is_extension_target j Q)
  : is_extension_target (j ∘ i) Q.
Proof.
  intros a. destruct (Ei a) as [b E], (Ej b) as [c F].
  exists c. unfold is_map_extension in *. rewrite <- comp_assoc, F. exact E.
Defined.

(** Old prescribed values on any further domain remain fixed. *)

(** 任意进一步域上的旧给定值保持不变。 *)

Lemma map_extension_preserves {A B D Q : @Ob C}
    {i : Hom A B} {a : Hom A Q} {b : Hom B Q}
    (E : is_map_extension i a b) (r : Hom D A) (c : Hom D Q)
    (R : a ∘ r ≈ c)
  : b ∘ (i ∘ r) ≈ c.
Proof. rewrite <- comp_assoc, E. exact R. Defined.

End Extensions.

(** ** Extending Across One Supplied Pushout

    Fix a candidate pushout square and a target. Its universal property
    constructs the total map after an extension on the new piece has
    been supplied. Changing law witnesses does not compare their records. *)

(** ** 跨一个给定推出延拓

    固定候选推出方形及目标。给定新块上的延拓后，其泛性质构造总映射；
    改变定律见证时不比较其记录。 *)

Section PushoutExtensions.
Context {C : Cat} {A B Z P Q : @Ob C}.
Context {f : Hom Z A} {g : Hom Z B} {i : Hom A P} {j : Hom B P}.
Context (HP : is_pushout f g P i j).

(** Keep both equations: the old region is unchanged, and the new cell
    has exactly the supplied extension value in specified equality. *)

(** 保留两个方程：旧区域保持不变，新块按指定相等具有给定延拓值。 *)

Definition PushoutMapExtension (a : Hom A Q)
    (b : ∃ b : Hom B Q, is_map_extension g (a ∘ f) b)
  : ∃ k : Hom P Q, (k ∘ i ≈ a) ∧ (k ∘ j ≈ b.1).
Proof.
  pose (e := snd HP Q a b.1 (symmetry b.2)).
  exists e.1. exact (@this _ _ _ _ _ e.2).
Defined.

(** Pushout stability gives an actual extension for every old-region map. *)

(** 推出保持性给每条旧区域映射实际构造延拓。 *)

Definition pushout_extension_target (E : is_extension_target g Q)
  : is_extension_target i Q.
Proof.
  intros a. pose (e := PushoutMapExtension a (E (a ∘ f))).
  exists e.1. exact (fst e.2).
Defined.

(** Only equality of the old and new piece values is needed to compare
    two mediators. No claim of independence of arbitrary new-cell choices. *)

(** 比较两个中介只需旧块和新块值相等；不声称任意新块选择之间无关。 *)

Lemma pushout_map_extension_proper
    (a a' : Hom A Q)
    (b : ∃ b : Hom B Q, is_map_extension g (a ∘ f) b)
    (b' : ∃ b : Hom B Q, is_map_extension g (a' ∘ f) b)
    (E : a ≈ a') (F : b.1 ≈ b'.1)
  : (PushoutMapExtension a b).1 ≈ (PushoutMapExtension a' b').1.
Proof.
  apply (pushout_hom_ext HP).
  - transitivity a; [exact (fst (PushoutMapExtension a b).2) |].
    transitivity a'; [exact E | symmetry; exact (fst (PushoutMapExtension a' b').2)].
  - transitivity b.1; [exact (snd (PushoutMapExtension a b).2) |].
    transitivity b'.1; [exact F | symmetry; exact (snd (PushoutMapExtension a' b').2)].
Defined.

End PushoutExtensions.
