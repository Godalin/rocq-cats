From Cats Require Import
  Cat.Core
  Cat.Equalizer
  Cat.Coequalizer
  Instance.Set.Core.
From Cats.Set Require Export
  Generated.

(** * Coequalizers in the Category of Setoids *)

(** * 广集范畴中的余等化子 *)

(** Generate both the original target equality and the identifications
    prescribed by the parallel pair. *)

(** 同时生成目标原有相等及平行箭头对规定的识别。 *)

Inductive CoeqRel {X Y : SetC} (f g : X →r Y)
  : crelation Y
  := | coeq_rel_equiv {y y' : Y} : y ≈S y' → CoeqRel f g y y'
     | coeq_rel_pair (x : X) : CoeqRel f g (f x) (g x).

Arguments coeq_rel_equiv {_ _ _ _ _ _} _.
Arguments coeq_rel_pair {_ _} _ _ _.

(** Keep the target carrier and enlarge only its specified equality.
    The inferred size condition is [u ≤ p], since derivations store elements. *)

(** 保留目标载体，只扩大其指定相等；推导出的大小条件为 [u ≤ p]，因为推导保留元素。 *)

Definition CoeqS@{u p +} {X Y : SetC@{u p}} (f g : X →r Y)
  : SetC@{u p}
  := GeneratedS Y (CoeqRel f g).

(** The quotient projection is identity on underlying representatives. *)

(** 商投影在底层代表上为恒等。 *)

Program Definition coeq_proj_resp {X Y : SetC} (f g : X →r Y)
  : Y →r CoeqS f g
  :=
  {|func y := y
  |}.
Next Obligation.
  intros y y' H. exact (closure_step (coeq_rel_equiv H)).
Defined.

(** A coequalizing map preserves the generators, so its unchanged function
    descends by the general generated-equivalence theory. *)

(** 余等化映射保持生成元，因此其未变的函数通过一般生成等价理论下降。 *)

Program Definition coeq_desc_resp {X Y Q : SetC} {f g : X →r Y}
    (q : Y →r Q) (H : (q ∘r f) ≈f (q ∘r g))
  : CoeqS f g →r Q
  := generated_resp q _.
Next Obligation.
  destruct X0.
  - apply func_proper. assumption.
  - apply H.
Defined.

(** The unchanged representative function has the full coequalizer property.
    Uniqueness compares values, never respectfulness or derivation witnesses. *)

(** 未变的代表函数具有完整余等化子性质；唯一性比较值，不比较保相等或推导见证。 *)

Definition set_coequalizer_universal {X Y : SetC} (f g : X →r Y)
  : @is_coequalizer SetCat X Y f g (CoeqS f g) (coeq_proj_resp f g).
Proof.
  split.
  - intros x. exact (closure_step (coeq_rel_pair f g x)).
  - intros Q q H. exists (coeq_desc_resp q H).
    refine {|this := _
           ; that := _
           |}.
    + intros y. reflexivity.
    + intros h Hh y. exact (Hh y).
Defined.

(** Choose opposite equalizers as these generated setoid coequalizers.
    This model needs [u ≤ p] and adds no resizing assumption. *)

(** 将这些生成广集余等化子选为反等化子；模型需要 [u ≤ p]，不加入大小重设假设。 *)

Program Definition SetCat_HasCoequalizer@{u p +}
  : HasCoequalizer (SetCat@{u p _ _ _ _ _})
  :=
  {|hasOpEqualizer :=
      {|EqObj X Y f g := CoeqS f g
      ; eqι X Y f g := coeq_proj_resp f g
      ; equalizer_universal X Y f g := set_coequalizer_universal f g
      |}
  |}.
