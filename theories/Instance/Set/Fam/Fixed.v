From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural.
From Cats Require Import
  Instance.Set.Core
  Instance.Set.Fam.Core
  Instance.Set.Fam.Cat.

(** * Coherent Families over a Fixed Setoid

    Morphisms stay in each fiber and commute with transport. Their equality
    compares values, without comparing respectfulness or coherence proofs.
    Coercion lets a fiber map be applied directly as [f x a]. *)

(** * 固定广集上的相干族

    态射逐纤维作用并与运输交换；相等比较值，不比较保相等或相干性证明。
    强制转换使逐纤维映射可直接写为 [f x a]。 *)

Record FamMap {X : SetC} (A B : FamS X)
  :=
  { fam_map (x : X) :> A x →r B x
  ; fam_map_naturality {x y : X} (p : x ≈S y) (a : A x)
    : fam_map y (transpS A p a) ≈S transpS B p (fam_map x a)
  }.

Arguments fam_map {_ _ _} _ _.
Arguments fam_map_naturality {_ _ _} _ {_ _} _ _.

Infix "→Fam" := FamMap (at level 99) : cat_scope.

(** Pointwise equality of fiber maps over the same base. *)

(** 同一基底上纤维映射的逐点相等。 *)

Definition FamMapEq {X : SetC} {A B : FamS X} (f g : A →Fam B)
  := ∀ x, f x ≈f g x.

Infix "≈Fam" := FamMapEq (at level 50) : cat_scope.

(** [FamMapEq] is an equivalence relation. *)

(** [FamMapEq] 是等价关系。 *)

Global Instance FamMapEq_Equivalence {X : SetC} {A B : FamS X}
  : Equivalence (@FamMapEq X A B).
Proof.
  split.
  - intros f x a. reflexivity.
  - intros f g H x a. symmetry. exact (H x a).
  - intros f g h Hfg Hgh x a. transitivity (g x a).
    + exact (Hfg x a).
    + exact (Hgh x a).
Qed.

(** The canonical set of fixed-base family maps has pointwise equality.
    Its carrier projection lets Rocq infer this set from a [FamMap] type. *)

(** 固定基底族映射的典范广集采用逐点相等；载体投影使 Rocq 可从 [FamMap]
    类型推断这个广集。 *)

Program Canonical FamMapS {X : SetC} (A B : FamS X)
  : SetC
  :=
  {|carrier := A →Fam B
  ; carrier_equiv := FamMapEq
  ; carrier_setoid := FamMapEq_Equivalence
  |}.

Infix "→FamS" := FamMapS (at level 99) : cat_scope.

(** The identity fiberwise map over a fixed base. *)

(** 固定基底上的恒等逐纤维映射。 *)

Program Definition fam_map_id {X : SetC} (A : FamS X)
  : A →Fam A
  :=
  {|fam_map x := id_resp
  |}.
Next Obligation. reflexivity. Defined.

(** Compose fixed-base maps independently in each fiber. *)

(** 在每个纤维中独立复合固定基底映射。 *)

Program Definition fam_map_comp {X : SetC} {A B D : FamS X}
    (g : B →Fam D) (f : A →Fam B)
  : A →Fam D
  :=
  {|fam_map x := g x ∘r f x
  |}.
Next Obligation.
  rewrite (fam_map_naturality f p), (fam_map_naturality g p). reflexivity.
Defined.

Infix "∘Fam" := fam_map_comp
  (at level 40, left associativity) : cat_scope.

(** The category of coherent families over one fixed base setoid. *)

(** 固定基底广集上的相干族范畴。 *)

Program Definition FamSCat (X : SetC)
  : Cat
  :=
  {|Ob := FamS X
  ; HomSet A B := A →FamS B
  ; id := fam_map_id
  ; comp A B D := fam_map_comp
  |}.
Next Obligation.
  intros g g' Hg f f' Hf x a. cbn.
  transitivity (g x (f' x a)).
  - apply func_proper. exact (Hf x a).
  - exact (Hg x (f' x a)).
Defined.
Next Obligation. intros x a. reflexivity. Defined.
Next Obligation. intros x a. reflexivity. Defined.

Next Obligation. intros x a. reflexivity. Defined.

(** Relate fixed-base maps to the existing category of all families. *)

(** 将固定基底映射关联到已有的全族范畴。 *)

Definition FixedFamC {X : SetC} (A : FamS X)
  : FamC
  :=
  {|famC_base := X
  ; famC_fam := A
  |}.

(** View a fixed-base fiber map as a family morphism over identity. *)

(** 将固定基底纤维映射视为恒等基底上的族态射。 *)

Program Definition fam_map_to_fam {X : SetC} {A B : FamS X} (f : A →Fam B)
  : FamF (FixedFamC A) (FixedFamC B)
  :=
  {|famF_base := id_resp
  ; famF_fam := f
  |}.
Next Obligation.
  transitivity (transpS B p (f x a)).
  - apply fam_map_naturality.
  - apply transpS_witness_independent.
Defined.

(** Embed fixed-base families into the category of all coherent families. *)

(** 将固定基底族嵌入全部相干族的范畴。 *)

Program Definition FamFixedF (X : SetC)
  : Fct (FamSCat X) FamCat
  :=
  {|F0 := FixedFamC
  ; F1 A B := fam_map_to_fam
  |}.
Next Obligation.
  intros f g H. exists (λ x, reflS (x := x)). intros x a.
  transitivity (f x a); [apply transpS_id | exact (H x a)].
Defined.
Next Obligation.
  exists (λ x, reflS (x := x)). intros x a. apply transpS_id.
Defined.
Next Obligation.
  exists (λ x, reflS (x := x)). intros x a. apply transpS_id.
Defined.

(** A fixed-base family map induces a respectful map of total spaces. *)

(** 固定基底族映射诱导全空间的保相等映射。 *)

Definition fam_map_total_resp {X : SetC} {A B : FamS X} (f : A →Fam B)
  : SigS X A →r SigS X B
  := fam_total_resp (fam_map_to_fam f).

(** Substitution is already available on families; extend it to maps. *)

(** 族上已有替换；将其延伸到映射。 *)

Program Definition fam_map_reindex {X Y : SetC} {A B : FamS Y}
    (f : X →r Y) (φ : A →Fam B)
  : A[f]S →Fam B[f]S
  :=
  {|fam_map x := φ (f x)
  |}.
Next Obligation. apply fam_map_naturality. Defined.

(** Reindex both coherent families and fixed-base family maps along a base
    arrow. *)

(** 沿基底箭头重索引相干族及固定基底族映射。 *)

Program Definition FamReindexF {X Y : SetC} (f : X →r Y)
  : Fct (FamSCat Y) (FamSCat X)
  :=
  {|F0 A := A[f]S
  ; F1 A B := fam_map_reindex f
  |}.
Next Obligation. intros φ ψ H x a. exact (H (f x) a). Defined.
Next Obligation. intros x a. reflexivity. Defined.
Next Obligation. intros x a. reflexivity. Defined.

(** Identity and composite substitution retain the same fiber values; their
    transport witnesses are compared by coherence. *)

(** 恒等与复合替换保留纤维值，其运输见证通过相干性比较。 *)

Program Definition fam_map_reindex_id {X : SetC} (A : FamS X)
  : A →Fam A[id_resp]S
  :=
  {|fam_map x := id_resp
  |}.
Next Obligation. apply transpS_witness_independent. Defined.

(** The fiberwise comparison for identity reindexing is invertible. *)

(** 恒等重索引的逐纤维比较可逆。 *)

Definition fam_map_reindex_id_iso {X : SetC} (A : FamS X)
  : @is_iso (FamSCat X) _ _ (fam_map_reindex_id A).
Proof.
  unshelve notypeclasses refine (({|fam_map := _
                                  |}); _).
  - exact (λ x, id_resp).
  - intros x y p a. cbn. apply transpS_witness_independent.
  - split; intros x a; reflexivity.
Defined.

(** Identity-reindexing comparisons are natural in the family. *)

(** 恒等重索引比较在族变量上自然。 *)

Program Definition FamReindexIdN (X : SetC)
  : (@IdF (FamSCat X)) ⇒ (FamReindexF (id_resp (X := X)))
  :=
  {|nt := fam_map_reindex_id
  |}.
Next Obligation. intros x a. reflexivity. Defined.

(** Identity reindexing is naturally isomorphic to the identity on fixed-base
    families. *)

(** 恒等重索引自然同构于固定基底族上的恒等函子。 *)

Definition fam_reindex_id_nat_iso (X : SetC)
  : (@IdF (FamSCat X)) ≅N (FamReindexF (id_resp (X := X)))
  := (FamReindexIdN X; fam_map_reindex_id_iso).

(** Compare iterated reindexing with reindexing along the composite base map. *)

(** 比较迭代重索引与沿复合基底映射的重索引。 *)

Program Definition fam_map_reindex_comp {X Y Z : SetC}
    (f : Y →r Z) (g : X →r Y) (A : FamS Z)
  : A[f]S[g]S →Fam A[f ∘r g]S
  :=
  {|fam_map x := id_resp
  |}.
Next Obligation. apply transpS_witness_independent. Defined.

Notation "A '⟨' f ',' g '⟩Fam'" := (fam_map_reindex_comp f g A)
  (at level 8, left associativity, format "A ⟨ f ,  g ⟩Fam") : cat_scope.

(** The comparison between iterated and composite family reindexing is
    invertible. *)

(** 迭代族重索引与复合族重索引间的比较可逆。 *)

Definition fam_map_reindex_comp_iso {X Y Z : SetC}
    (f : Y →r Z) (g : X →r Y) (A : FamS Z)
  : @is_iso (FamSCat X) _ _ A⟨f, g⟩Fam.
Proof.
  unshelve notypeclasses refine (({|fam_map := _
                                  |}); _).
  - exact (λ x, id_resp).
  - intros x y p a. cbn. apply transpS_witness_independent.
  - split; intros x a; reflexivity.
Defined.

(** Composition comparisons for reindexing are natural in the family. *)

(** 重索引的复合比较在族变量上自然。 *)

Program Definition FamReindexCompN {X Y Z : SetC} (f : Y →r Z) (g : X →r Y)
  : (FamReindexF g ∘F FamReindexF f) ⇒ (FamReindexF (f ∘r g))
  :=
  {|nt A := A⟨f,g⟩Fam
  |}.
Next Obligation. intros x a. reflexivity. Defined.

(** Iterated family reindexing is naturally isomorphic to composite
    reindexing. *)

(** 迭代族重索引自然同构于复合重索引。 *)

Definition fam_reindex_comp_nat_iso {X Y Z : SetC} (f : Y →r Z) (g : X →r Y)
  : (FamReindexF g ∘F FamReindexF f) ≅N (FamReindexF (f ∘r g))
  := (FamReindexCompN f g; fam_map_reindex_comp_iso f g).

(** ** Equivalent Substitutions and Coherence

    Base-map equivalences act by transport. Their witnesses are retained,
    while the resulting maps are independent of the chosen witness. *)

(** ** 等价替换与相干性

    基底映射相等通过运输作用；见证作为数据保留，但诱导映射独立于见证选择。 *)

Program Definition fam_map_reindex_equiv {X Y : SetC} {f g : X →r Y}
    (H : f ≈f g) (A : FamS Y)
  : A[f]S →Fam A[g]S
  :=
  {|fam_map x := transpS A (H x)
  |}.
Next Obligation.
  transitivity (transpS A (transitivity (@func_proper _ _ f x y p) (H y)) a).
  - symmetry. apply transpS_comp.
  - apply transpS_comp.
Defined.

Notation "A '⟦' H '⟧Fam'" := (fam_map_reindex_equiv H A)
  (at level 8, left associativity, format "A ⟦ H ⟧Fam") : cat_scope.

(** Transport along equality of base maps gives an invertible family map. *)

(** 沿基底映射相等的运输给出可逆族映射。 *)

Definition fam_map_reindex_equiv_iso {X Y : SetC} {f g : X →r Y}
    (H : f ≈f g) (A : FamS Y)
  : @is_iso (FamSCat X) _ _ A⟦H⟧Fam.
Proof.
  exists A⟦symmetry H⟧Fam. split; intros x a; cbn.
  - transitivity (transpS A (reflS (x := f x)) a).
    + symmetry. apply transpS_comp.
    + apply transpS_id.
  - transitivity (transpS A (reflS (x := g x)) a).
    + symmetry. apply transpS_comp.
    + apply transpS_id.
Defined.

(** Base-map equality comparisons are natural in the reindexed family. *)

(** 基底映射相等比较在重索引族变量上自然。 *)

Program Definition FamReindexEqN {X Y : SetC} {f g : X →r Y} (H : f ≈f g)
  : FamReindexF f ⇒ FamReindexF g
  :=
  {|nt := fam_map_reindex_equiv H
  |}.
Next Obligation.
  intros x a. cbn. symmetry. exact (fam_map_naturality f0 (H x) a).
Defined.

(** Equal base maps induce naturally isomorphic family-reindexing functors. *)

(** 相等基底映射诱导自然同构的族重索引函子。 *)

Definition fam_reindex_equiv_nat_iso {X Y : SetC} {f g : X →r Y} (H : f ≈f g)
  : FamReindexF f ≅N FamReindexF g
  := (FamReindexEqN H; fam_map_reindex_equiv_iso H).

(** The operation respects the specified equivalences of its arguments. *)

(** 该运算保持各参数指定的等价关系。 *)

Global Instance FamReindexF_proper {X Y : SetC}
  : Proper (@HomEq SetCat X Y ==> NatIso) (@FamReindexF X Y).
Proof. intros f g H. exact (fam_reindex_equiv_nat_iso H). Defined.

(** Changing equality witnesses leaves the resulting action equal. *)

(** 改变相等见证后，所得作用仍然相等。 *)

Theorem fam_reindex_equiv_witness_independent {X Y : SetC} {f g : X →r Y}
    (H K : f ≈f g)
  : FamReindexEqN H ≈N FamReindexEqN K.
Proof. intros A x a. cbn. apply transpS_witness_independent. Qed.

(** Transport induced by reflexive base-map equality is identity. *)

(** 自反基底映射相等诱导的运输是恒等。 *)

Theorem fam_reindex_equiv_id {X Y : SetC} {f : X →r Y} (H : f ≈f f)
  : FamReindexEqN H ≈N idN.
Proof. intros A x a. cbn. apply transpS_id. Qed.

(** Transport along composite base-map equality agrees with successive
    transport. *)

(** 沿复合基底映射相等的运输等于连续运输。 *)

Theorem fam_reindex_equiv_comp {X Y : SetC} {f g h : X →r Y}
    (H : f ≈f g) (K : g ≈f h) (L : f ≈f h)
  : FamReindexEqN L ≈N (FamReindexEqN K ∘Nv FamReindexEqN H).
Proof. intros A x a. cbn. apply transpS_comp. Qed.

(** The composition comparison is natural in both base maps. Any witness of
    the composite equivalence gives the same comparison. *)

(** 复合比较在两个基底映射上自然；复合相等的任意见证都给出相同比较。 *)

Theorem fam_reindex_comp_equiv {X Y Z : SetC} {f f' : Y →r Z} {g g' : X →r Y}
    (H : f ≈f f') (K : g ≈f g') (L : (f ∘r g) ≈f (f' ∘r g')) (A : FamS Z)
  : A⟦L⟧Fam ∘Fam A⟨f, g⟩Fam ≈Fam
      A⟨f', g'⟩Fam ∘Fam A[f']S⟦K⟧Fam ∘Fam
        fam_map_reindex g A⟦H⟧Fam.
Proof. intros x a. cbn. apply transpS_comp. Qed.

(** Unit and associativity diagrams are stated after aligning their base maps
    by equivalence; no equality of substitution records is used. *)

(** 单位与结合交换图先通过基底相等对齐，不使用替换记录的原生相等。 *)

Theorem fam_reindex_unit_l {X Y : SetC} (f : X →r Y)
    (H : (id_resp ∘r f) ≈f f) (A : FamS Y)
  : A⟦H⟧Fam ∘Fam A⟨id_resp, f⟩Fam ∘Fam
      fam_map_reindex f (fam_map_reindex_id A) ≈Fam fam_map_id A[f]S.
Proof. intros x a. cbn. apply transpS_id. Qed.

(** The right unit diagram for coherent family reindexing commutes. *)

(** 相干族重索引的右单位图交换。 *)

Theorem fam_reindex_unit_r {X Y : SetC} (f : X →r Y)
    (H : (f ∘r id_resp) ≈f f) (A : FamS Y)
  : A⟦H⟧Fam ∘Fam A⟨f, id_resp⟩Fam ∘Fam
      fam_map_reindex_id A[f]S ≈Fam fam_map_id A[f]S.
Proof. intros x a. cbn. apply transpS_id. Qed.

(** Associativity law for [fam_reindex]. *)

(** [fam_reindex] 结合律。 *)

Theorem fam_reindex_assoc {X Y Z W : SetC}
    (f : Z →r W) (g : Y →r Z) (h : X →r Y)
    (H : ((f ∘r g) ∘r h) ≈f (f ∘r (g ∘r h))) (A : FamS W)
  : A⟦H⟧Fam ∘Fam A⟨f ∘r g, h⟩Fam ∘Fam
      fam_map_reindex h A⟨f, g⟩Fam ≈Fam
    A⟨f, g ∘r h⟩Fam ∘Fam A[f]S⟨g, h⟩Fam.
Proof. intros x a. cbn. apply transpS_id. Qed.
