From Cats Require Import
  Cat.Core
  Cat.Functor.Core
  Cat.Natural
  Instance.Set.Core
  Instance.Set.Fam.Core
  Instance.Set.Fam.Cat.

(** * Raising Fibers of Coherent Families

    Keep each supplied base setoid unchanged. Raise fiber carriers and
    equality witnesses independently, and lift the existing transport maps.
    This is an explicit wrapper, without resizing or a choice of models. *)

(** * 提升相干族的纤维

    保持给定基底广集不变，独立提升纤维载体及相等见证，并提升既有运输映射。
    这是显式包装，不使用大小重设或模型选择。 *)

(** Lift every fiber over the original base, retaining its coherent
    transport and the Type-valued equality witnesses. *)

(** 在原基底上提升各纤维，保留相干运输及 Type 值相等见证。 *)

Program Definition LiftFamS@{v q +} {X : SetC} (A : FamS X)
  : FamS@{_ _ _ v q} X
  :=
  {|fam x := LiftS@{_ _ v q} (A x)
  ; transpS x y p := (transpS A p)^↑S
  |}.
Next Obligation. constructor. apply transpS_id. Defined.
Next Obligation. constructor. apply transpS_comp. Defined.

(** Package the lifted fibers with the same base setoid. *)

(** 将提升纤维与同一基底广集打包。 *)

Definition LiftFamC@{v q +} (U : FamC)
  : FamC@{_ _ _ v q}
  :=
  {|famC_base := famC_base U
  ; famC_fam := LiftFamS U
  |}.

(** A lifted family morphism retains its base map and applies the original
    fiber map between the wrappers. Coherence uses the original witness.
    The input map's auxiliary carrier bound [s] is independent of [v]. *)

(** 提升族态射保留基底映射，在包装之间应用原纤维映射；相干性使用原见证。
    输入映射的辅助载体上界 [s] 与 [v] 独立。 *)

Program Definition lift_fam_map@{v q s +} {U V : FamC}
    (f : FamF@{_ _ _ _ _ _ _ _ s _ _ _ _ _} U V)
  : FamF (LiftFamC U : FamC@{_ _ _ v q})
      (LiftFamC V : FamC@{_ _ _ v q})
  :=
  {|famF_base := f
  ; famF_fam x := (famF_fam f x)^↑S
  |}.
Next Obligation.
  constructor. exact (@famF_naturality U V f x y p (lower a)).
Defined.

(** Fiber lifting preserves family-morphism equality, identity and
    composition. The base and its equality witnesses are not lifted. *)

(** 纤维提升保持族态射相等、恒等及复合；基底及其相等见证不作提升。 *)

Program Definition FamLiftF@{v q +}
  : Fct FamCat FamCat@{_ _ _ _ _ _ _ _ v q _ _ _ _ _ _}
  :=
  {|F0 := LiftFamC
  ; F1 U V f := lift_fam_map f
  |}.
Next Obligation.
  intros f g [p Hp]. exists p. intros x [a].
  constructor. exact (Hp x a).
Defined.
Next Obligation.
  exists (λ x, reflS (x := x)). intros x [a].
  constructor. apply transpS_id.
Defined.
Next Obligation.
  exists (λ x, reflS (x := f (g x))). intros x [a].
  constructor. apply transpS_id.
Defined.

(** Forgetting the base after fiber lifting has identity comparison
    components; naturality compares maps, not functor records. *)

(** 纤维提升后忘却到基底的比较分量为恒等；自然性比较映射而非函子记录。 *)

Program Definition FamLiftBaseN@{v q +}
  : (FamBaseF ∘F
      (FamLiftF : Fct FamCat FamCat@{_ _ _ _ _ _ _ _ v q _ _ _ _ _ _}))
      ⇒ FamBaseF
  := {|nt U := id|}.
Next Obligation. intros x. reflexivity. Defined.

(** The base comparison has transparent identity inverse data. No
    equivalence between different universe-sized family categories is
    asserted. *)

(** 基底比较具有透明恒等逆数据；不宣称不同大小族范畴之间的等价。 *)

Definition fam_lift_base_iso@{v q +}
  : (FamBaseF ∘F
      (FamLiftF : Fct FamCat FamCat@{_ _ _ _ _ _ _ _ v q _ _ _ _ _ _}))
      ≅N FamBaseF.
Proof.
  exists FamLiftBaseN. intros U.
  exists id. split; apply comp_id_l.
Defined.
