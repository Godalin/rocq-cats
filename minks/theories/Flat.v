From elpi Require Import elpi.
From Minks Require Import Spec.

(** * Flat structure generator

    The generator builds a flat record and direct forgetful maps from
    named components and their dependency graph. *)

(** * 平铺结构生成器

    从具名组件及其依赖图生成平铺记录与直接忘却映射。 *)

Elpi File minks.flat lp:{{
  pred lookup i:id, i:list (pair id term), o:term.
  lookup Key Env T :-
    std.assert! (std.mem Env (pr Key T))
      ("Missing or out-of-order component " ^ Key).

  pred field-name i:id, i:id, o:id.
  field-name N Key F :- F is N ^ "_" ^ Key.

  pred fields i:id, i:list component, i:list (pair id term), o:record-decl.
  fields _ [] _ end-record.
  fields N [slot Key Ref Ds | Cs] Env (field [] F Ty Tail) :-
    field-name N Key F,
    coq.env.global Ref Head,
    std.map Ds (d\t\ lookup d Env t) Args,
    coq.mk-app Head Args Ty,
    pi x\ fields N Cs [pr Key x | Env] (Tail x).

  pred field-ref i:id, i:option constant, o:(pair id constant).
  field-ref Key (some C) (pr Key C).

  pred read-field i:list (pair id constant), i:id, o:term.
  read-field Fs Key Head :-
    std.mem Fs (pr Key C),
    coq.env.global (const C) Head.

  pred apply-fields i:list term, i:term, o:list term.
  apply-fields [] _ [].
  apply-fields [F | Fs] X [app [F, X] | Ts] :-
    apply-fields Fs X Ts.

  pred view-body i:term, i:list term, o:(term -> term).
  view-body Ctor Fs (x\ app [Ctor | Args x]) :-
    pi x\ apply-fields Fs x (Args x).

  pred parent-view i:id, i:term, i:list (pair id constant), i:inductive.
  parent-view Child ChildTy Fields Parent :-
    close Parent Cs,
    coq.env.indt Parent tt 0 0 _ [K] _,
    coq.env.global (indc K) Ctor,
    std.map Cs component-key Keys,
    std.map ["carrier" | Keys] (k\t\ read-field Fields k t) Fs,
    view-body Ctor Fs Body,
    Term = fun `child` ChildTy Body,
    coq.gref->id (indt Parent) ParentName,
    Name is Child ^ "To" ^ ParentName,
    std.assert-ok! (coq.typecheck Term Ty) ("Ill-typed view " ^ Name),
    @univpoly! => coq.env.add-const Name Term Ty @transparent! _.

  pred register-field i:list component, i:list (pair id constant), i:component.
  register-field Cs Fs (slot Key Ref Ds) :-
    if (auto-instance Cs (slot Key Ref Ds))
      (std.mem Fs (pr Key C), coq.TC.declare-instance (const C) 1)
      true.

  % The carrier is the sole external slot in this experiment.
  pred generate i:id, i:list inductive, i:list component, o:inductive.
  generate N Parents Cs I :-
    coq.univ.new U,
    coq.univ.new R,
    Carrier = sort (typ U),
    field-name N "carrier" F,
    (pi a\ fields N Cs [pr "carrier" a] (Tail a)),
    Ctor is "Make" ^ N,
    Decl = record N (sort (typ R)) Ctor (field [coercion regular] F Carrier Tail),
    std.assert-ok! (coq.typecheck-indt-decl Decl) ("Ill-typed structure " ^ N),
    (@univpoly! => coq.env.add-indt Decl I),
    coq.env.global (indt I) ChildTy,
    coq.env.projections I Projections,
    std.map Cs component-key Keys,
    std.map2 ["carrier" | Keys] Projections field-ref Fields,
    std.forall Parents
      (p\ std.assert! (parent-view N ChildTy Fields p)
        "Failed to generate parent view"),
    std.forall Cs (register-field Cs Fields).
}}.
