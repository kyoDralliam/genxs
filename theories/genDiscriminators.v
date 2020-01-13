From Coq Require Import Strings.String.
From MetaCoq.Template Require Import All.
From Genxs Require Import metacoq_utils.


Import MonadNotation.

(** Generation of discrimators *)

Definition qBool :=
  tInd {| inductive_mind := "Coq.Init.Datatypes.bool"; inductive_ind := 0 |} nil.

Quote Definition qtrue := true.
Quote Definition qfalse := false.


Definition indctor_gen_discriminators
           (debug:bool)
           (indname : qualid)
           (mindbody : mutual_inductive_body)
           (oind_index : nat)
           (oindbody : one_inductive_body)
           (ctor_index : nat)
           '(((ctor_id, _ty), _arity) : (ident × term) × nat) :=
  let discr_id := "is" ++ ctor_id in
  let discr_body :=
    let universes := nil (*FIXME*) in
    let npars := ind_npars mindbody in
    let ctx := ind_params mindbody in
    let ind0 := mkInd indname oind_index in
    let ind shift := mkApps_ctx (tInd ind0 universes) shift ctx in
    let build_branch ctor_k '(((_ , ty),arity): (ident × term) × nat) :=
        let '(_, tys, _) := decompose_prod ty in
        let body := if eq_nat ctor_k ctor_index then qtrue else qfalse in
        (arity, up (build_const (List.skipn npars tys) body))
    in
    let brnchs := utils.mapi build_branch (ind_ctors oindbody) in
    it_mkLambda_or_LetIn ctx
      (tLambda (nNamed "z")
               (ind 0)
               (tCase (ind0, npars)
                      (tLambda (nNamed "z") (ind 1) qBool)
                      (tRel 0)
                      brnchs))
  in
  t <- tmEval all discr_body ;;
  if debug
  then tmPrint t
  else
    tmMkDefinition discr_id t ;;
    tmMsg (discr_id ++ " is defined.").

Definition oneindbody_gen_discriminators
           (debug:bool)
           (indname : qualid)
           (mindbody : mutual_inductive_body)
           (oind_index : nat)
           (oindbody : one_inductive_body)
  : TemplateMonad unit :=
  monad_iteri
    (indctor_gen_discriminators debug indname mindbody oind_index oindbody)
    (ind_ctors oindbody).

Definition gen_discriminators (debug:bool) (mindname : qualid) (* Is it a kername ?*)
  : TemplateMonad unit :=
  mindbody <- tmQuoteInductive mindname ;;
  monad_iteri
    (oneindbody_gen_discriminators debug mindname mindbody)
    (ind_bodies mindbody).


(** Tests *)
Module TestGenDiscriminators.

  Inductive I (A:Type) := IX : I A | IY : nat -> I A | IZ : forall (x:nat), x+x = 2 -> I A.

  Definition isIX0 {A} (z : I A) := match z with | IX => true | _ => false end.
  Arguments isIX0 [_] _.
  Quote Definition qisIX0 := Eval unfold isIX0 in isIX0.

  Run TemplateProgram (gen_discriminators false "I").

  From Coq Require Import ssreflect.

  Definition isSome0 A (z : option A) := if z is Some _ then true else false.
  Definition isNone0 A (z : option A) := if z is None then true else false.
  Quote Definition qisSome0 := Eval unfold isSome0 in isSome0.

  Run TemplateProgram (gen_discriminators false "option").

  (* Run TemplateProgram (gen_discriminators "option"). *)

  (* FIXME: gen_discriminators does not manage indices ! *)
  Inductive J (n:nat) : nat -> Type  := X : J n 0 | Y : J n n | Z : forall k, J n k.
  Definition isX0 {n k} (z :  J n k) := match z with | X => true | _ => false end.
  Arguments isX0 [_ _] _.
  Quote Definition qisX0 := Eval unfold isX0 in isX0.

End TestGenDiscriminators.
