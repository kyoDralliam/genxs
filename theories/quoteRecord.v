From Coq Require Import List Strings.String ssreflect.
From MetaCoq.Template Require Import All.
From Genxs Require Import metacoq_utils genDiscriminators.

Set Primitive Projections.

Import MonadNotation.
Import ListNotations.


Run TemplateProgram (gen_discriminators false "option").
(* Is there any way to manage implicit arguments from MetaCoq ? *)
Arguments isSome {_} _.
Arguments isNone {_} _.

(* Currently assumes all projs to be independent *)
Definition over_oien (oien : one_inductive_entry) (projs:list ident)
  : TemplateMonad one_inductive_entry :=
  match mind_entry_lc oien with
  |  (cty :: nil)%list =>
    let '(argnames, argtys, res)  := decompose_prod cty in
    let filter '(name, _) :=
      if name is nNamed id
      then isNone (List.find (ident_eq id) projs)
      else true
    in
    let cty :=
        (* FIXME : I forgot to downshift by the arguments that are removed *)
        List.fold_right (fun '(name, ty) r => tLambda name ty r) res
                        (List.filter filter
                                     (List.combine argnames argtys))
    in
    let suffix := "_over_" ++ concat "_" projs in
    ret (Build_one_inductive_entry
           (mind_entry_typename oien ++ suffix)
           (mind_entry_arity oien)
           (mind_entry_template oien)
           (List.map (fun id => id ++ suffix) (mind_entry_consnames oien))
           (cty :: nil)%list)
  | _ => tmFail "Not a record"
  end.

Definition over_mien (mien:mutual_inductive_entry) (projs:list ident)
  : TemplateMonad mutual_inductive_entry :=
  id <- (match mind_entry_record mien with
        | Some (Some id) => ret id
        | _ => tmFail "Not a record with primitive projection"
        end) ;;
  oien <- (match mind_entry_inds mien with
           | (oien :: nil)%list => ret oien
           | _ => tmFail "Something is wrong over the internet"
           end) ;;
  oien <- over_oien oien projs ;;
  let suffix := "_over_" ++ concat "_" projs in
  ret (Build_mutual_inductive_entry
         (Some (Some (id ++ suffix)))
         (mind_entry_finite mien)
         (mind_entry_params mien)
         (oien :: nil)%list
         (mind_entry_universes mien)
         (mind_entry_private mien)).



Definition mem {A} (eq:A -> A -> bool) (a:A) (l:list A) : bool := isSome (List.find (eq a) l).

Definition over_oib (decl:mutual_inductive_body) (projs:list ident) (oid:one_inductive_body) :=
  let suffix := "_over_" ++ concat "_" projs in
  let filtered_projs := List.filter (fun '(id,_) => negb (mem ident_eq id projs)) (ind_projs oid) in
  Build_one_inductive_body
    (ind_name oid ++ suffix)
    (ind_type oid)
    (ind_kelim oid)
    (ind_ctors oid)
    filtered_projs.


Definition over_mib (decl:mutual_inductive_body) (projs:list ident) : mutual_inductive_body :=
  Build_mutual_inductive_body
    (ind_finite decl)
    (ind_npars decl)
    (ind_params decl)
    (List.map (over_oib decl projs) (ind_bodies decl))
    (ind_universes decl).


Module test.
  Parameter (X Y Z : Type).

  Record R := mkR { Rx : X ; Ry : Y ; Rz : Z }.

  Quote Recursively Definition x := R.

  Definition prog : TemplateMonad unit :=
    t <- tmQuoteInductive "R";;
      let t_over_Ry := over_mib t ("Ry" :: nil)%list in
      t <- tmEval all t_over_Ry ;;
      (* t <- tmEval all (mind_body_to_entry t_over_Ry) ;; *)
      tmPrint t (* ;; *)
      (* tmMkInductive t_over_Ry *).

  Run TemplateProgram prog.

  Definition prog2 : TemplateMonad unit :=
    t <- tmQuoteInductive "R";;
      t_over_Ry <- over_mien (mind_body_to_entry t) ("Ry" :: nil)%list ;;
      t <- tmEval all t_over_Ry ;;
      tmPrint t (* ;; *)
      (* tmMkInductive t_over_Ry *).

  Run TemplateProgram prog2.

  (* Run TemplateProgram ( *)
  (*   t <- tmQuoteInductive "R";; *)
  (*     t <- tmEval all (mind_body_to_entry t) ;; *)
  (*     tmMkInductive t;; *)
  (*     tmPrint t). *)

End test.



(** Tests *)

Axiom A : Type.
Axiom B : A -> Type.
Axiom C : forall a, B a -> Type.

Record T := mkT { t_a : A ; t_b : B t_a ; t_c : C _ t_b }.
(* Run TemplateProgram (t <- tmQuoteInductive "T";; tmPrint t). *)
(* Run TemplateProgram (x <- tmQuoteInductive "Top.T";; tmPrint x). *)


Run TemplateProgram (gen_discriminators false "recursivity_kind").


(* Definition decomposeRecord (mindbody : mutual_inductive_body) *)
(*   : TemplateMonad unit := *)
(*   assertTM (isBiFinite (ind_finite mindbody)) ;; *)
