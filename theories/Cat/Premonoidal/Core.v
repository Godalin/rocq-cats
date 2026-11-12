From Cats Require Export
  Cat.Binoidal.Center.

Local Open Scope binoidal_scope.

(** * Premonoidal Categories

    A premonoidal category adds a unit and central structural isomorphisms
    to one binoidal structure. Naturality is stated one variable at a time:
    computations on different inputs need not exchange their order.
    Pentagon and triangle compare arrows using specified hom equality. *)

(** * 预幺半范畴

    预幺半范畴为一个双侧张量结构增加单位对象及中心结构同构。自然性逐变量
    表述：不同输入上的计算不必交换执行次序。五边形与三角形使用指定的
    Hom 相等比较态射。 *)

Class PremonoidalCat (C : Cat)
  :=
  (** The only parent view supplies both actions and their shared tensor. *)

  (** 唯一父视图提供两种作用及其共享张量。 *)

  { PremonoidalB :> BinoidalCat C

  (** A chosen unit object is part of the structure. *)

  (** 单位对象是结构中的选定数据。 *)

  ; PremonoidalUnit : @Ob C

  (** Rebracket three objects, retaining the computational inverse. *)

  (** 对三个对象重新加括号，保留可计算的逆。 *)

  ; premonoidal_associator (X Y Z : @Ob C)
    : ((X ⊗ Y) ⊗ Z) ≅ (X ⊗ (Y ⊗ Z))

  (** Remove the unit on either side, with chosen inverse insertions. *)

  (** 移除任一侧的单位对象，并保留反向插入的选择。 *)

  ; premonoidal_left_unitor (X : @Ob C)
    : (PremonoidalUnit ⊗ X) ≅ X
  ; premonoidal_right_unitor (X : @Ob C)
    : (X ⊗ PremonoidalUnit) ≅ X

  (** Only forward centrality is stored; centrality of inverses follows. *)

  (** 仅保存正向中心性；逆的中心性由此导出。 *)

  ; premonoidal_assoc_central (X Y Z : @Ob C)
    : is_central (premonoidal_associator X Y Z).1
  ; premonoidal_unit_l_central (X : @Ob C)
    : is_central (premonoidal_left_unitor X).1
  ; premonoidal_unit_r_central (X : @Ob C)
    : is_central (premonoidal_right_unitor X).1

  (** Each unitor is natural in its sole variable. *)

  (** 每个单位子在其唯一变量上自然。 *)

  ; premonoidal_unit_l_natural {X Y : @Ob C} (f : Hom X Y)
    : (premonoidal_left_unitor Y).1 ∘ (PremonoidalUnit ⊲ f) ≈
        f ∘ (premonoidal_left_unitor X).1
  ; premonoidal_unit_r_natural {X Y : @Ob C} (f : Hom X Y)
    : (premonoidal_right_unitor Y).1 ∘ (f ⊳ PremonoidalUnit) ≈
        f ∘ (premonoidal_right_unitor X).1

  (** The associator is separately natural in all three positions. *)

  (** 结合子在三个位置上分别自然。 *)

  ; premonoidal_assoc_natural_l {X X' : @Ob C}
      (Y Z : @Ob C) (f : Hom X X')
    : (premonoidal_associator X' Y Z).1 ∘ ((f ⊳ Y) ⊳ Z) ≈
        (f ⊳ (Y ⊗ Z)) ∘ (premonoidal_associator X Y Z).1
  ; premonoidal_assoc_natural_m {Y Y' : @Ob C}
      (X Z : @Ob C) (g : Hom Y Y')
    : (premonoidal_associator X Y' Z).1 ∘ ((X ⊲ g) ⊳ Z) ≈
        (X ⊲ (g ⊳ Z)) ∘ (premonoidal_associator X Y Z).1
  ; premonoidal_assoc_natural_r {Z Z' : @Ob C}
      (X Y : @Ob C) (h : Hom Z Z')
    : (premonoidal_associator X Y Z').1 ∘ ((X ⊗ Y) ⊲ h) ≈
        (X ⊲ (Y ⊲ h)) ∘ (premonoidal_associator X Y Z).1

  (** Coherence uses single context actions, never an interchange axiom. *)

  (** 相干性使用单侧上下文作用，不引入交换公理。 *)

  ; premonoidal_pentagon (W X Y Z : @Ob C)
    : (premonoidal_associator W X (Y ⊗ Z)).1 ∘
        (premonoidal_associator (W ⊗ X) Y Z).1 ≈
        (W ⊲ (premonoidal_associator X Y Z).1) ∘
          ((premonoidal_associator W (X ⊗ Y) Z).1 ∘
            ((premonoidal_associator W X Y).1 ⊳ Z))
  ; premonoidal_triangle (X Y : @Ob C)
    : (X ⊲ (premonoidal_left_unitor Y).1) ∘
        (premonoidal_associator X PremonoidalUnit Y).1 ≈
        (premonoidal_right_unitor X).1 ⊳ Y
  }.

Arguments PremonoidalB {_} _.
Arguments PremonoidalUnit {_} _.
Arguments premonoidal_associator {_ _} _ _ _.
Arguments premonoidal_left_unitor {_ _} _.
Arguments premonoidal_right_unitor {_ _} _.

(** Register that same parent for inherited instance search. *)

(** 为继承实例搜索注册同一个父结构。 *)

#[export] Existing Instance PremonoidalB.

Declare Scope premonoidal_scope.
Delimit Scope premonoidal_scope with premonoidal.
Notation "'Iₚ[' P ']'" := (PremonoidalUnit P) : premonoidal_scope.
Notation "'αₚ[' X ';' Y ';' Z ']'" :=
  (premonoidal_associator X Y Z).1 : premonoidal_scope.
Notation "'λₚ[' X ']'" := (premonoidal_left_unitor X).1
  : premonoidal_scope.
Notation "'ρₚ[' X ']'" := (premonoidal_right_unitor X).1
  : premonoidal_scope.
Notation "'αₚ⁻¹[' X ';' Y ';' Z ']'" :=
  (premonoidal_associator X Y Z).2.1 : premonoidal_scope.
Notation "'λₚ⁻¹[' X ']'" := (premonoidal_left_unitor X).2.1
  : premonoidal_scope.
Notation "'ρₚ⁻¹[' X ']'" := (premonoidal_right_unitor X).2.1
  : premonoidal_scope.
