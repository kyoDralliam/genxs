(* From mathcomp Require ssreflect.seq ssreflect.ssrbool. *)
(* From Coq Require Import Strings.String. *)
From MetaCoq.Template Require Import All.
From Genxs Require Import metacoq_utils.


Set Primitive Projections.
Import MCMonadNotation.

Section IteriInd.
  Definition inductiveIteratorT := inductive -> mutual_inductive_body -> one_inductive_body -> nat -> constructor_body -> TemplateMonad@{_ Set} unit.
  Context (h : inductiveIteratorT).

  Set Printing Universes.

  Definition oneindbody_iteri
           (ind : inductive)
           (mindbody : mutual_inductive_body)
           (oind_index : nat)
           (oindbody : one_inductive_body)
  : TemplateMonad@{_ Set} unit :=
  monad_iteri (h {| inductive_mind := ind.(inductive_mind) ; inductive_ind := oind_index |} mindbody oindbody) (ind_ctors oindbody).

  Definition mutualindbody_iteri (mindname : qualid)
  : TemplateMonad@{_ Set} unit :=
    ind <- get_inductive mindname ;;
    mindbody <- tmQuoteInductive ind.(inductive_mind) ;;
    monad_iteri (A:= one_inductive_body) (oneindbody_iteri ind mindbody) (ind_bodies mindbody).

End IteriInd.


Definition aname_ident (an : aname) (dflt : string) : string :=
    match an.(binder_name) with
    | nAnon => dflt
    | nNamed id => id
    end.


(** Naming conventions *)
Section Naming.
  Context (ctor_id : ident).
  Local Open Scope bs.

  Definition discr_id := "is" ++ ctor_id.

  Definition proj_id (argname : aname) (arg_i : nat) :=
    "proj" ++ ctor_id ++ "_" ++ aname_ident argname (string_of_nat arg_i).
End Naming.

(* Helpers for binders *)
Definition relNamed (s : string) : aname :=
  {| binder_name := nNamed s ; binder_relevance := Relevant |}.
Definition irrelNamed (s : string) : aname :=
  {| binder_name := nNamed s ; binder_relevance := Irrelevant |}.
Definition anonIrrel : aname :=
  {| binder_name := nAnon ; binder_relevance := Irrelevant |}.


(** Generation of discrimators *)

(* A discriminator for constructor K(a1,..,an) of an inductive I is a boolean-valued function
   on I that discriminates K from the other constructors of K.

   A projector for the l-th argument of a constructor K(a1,..,an) is a function that takes
   an element x of I and a proof that x is of the form K(...) and returns its l-th argument.
   The proofs consist of an application of the corresponding discriminator, wrapped to land
   in SProp to be able to use strict proof-irrelevance.
 *)

(* Quoted examples of discriminators for nat, list and eq *)
Definition qisZ := <% fun n : nat => match n with | 0 => true | _ => false end %>.
Definition qisSuc := <% fun n : nat => match n with | S _ => true | _ => false end %>.

Definition qisCons := <% fun A (l : list A) => match l with | cons _ _ => true | _ => false end %>.

Definition qisEqrefl := <% fun A x y (e : @eq A x y) => match e with | eq_refl => true end %>.


(** SProp helpers used in projectors *)

From Coq.Logic Require Import StrictProp.

Definition is_true_s (b : bool) : SProp :=
  if b then sUnit else sEmpty.

Definition toSProp {X} (p : X -> bool) (x : X) : SProp :=
  is_true_s (p x).

Definition bexfalso {A} (e : false = true) : A :=
  let B (b : bool) := if b return Type then unit else A in
  match e in _ = b return B b -> A with
  | eq_refl => fun x => x
  end tt.

Definition sexfalso {A} (e : sEmpty) : A := sEmpty_rect (fun _ => A) e.



Section Builders.
  Context (ind0 : inductive)
    (mindbody : mutual_inductive_body)
    (oindbody : one_inductive_body)
    (ctor_index : nat)
    (ctor : constructor_body).

  Let npars := ind_npars mindbody.
  Let param_ctx := ind_params mindbody.
  Let indices_ctx := ind_indices oindbody.

  Let ctx := app_context param_ctx indices_ctx.

  Context (uvs := nil) (* TODO: manage universes *)
          (ind := fun shift => mkApps_ctx (tInd ind0 uvs) shift ctx).

  (* to be used with it_mkLambda_or_LetIn;
     builds the list of variables corresponding to the ctx to be bound
     shift levels above *)
  Definition subst_from_ctx (shift : nat) (ctx : context) :=
    let fold_fun _ '(n, l) := (S n, tRel n :: l)%list in
    snd (List.fold_right fold_fun (shift , nil) ctx).

  (** Building discriminators *)
  Definition build_discriminators :=
    let principal := relNamed "principal"%bs in
    let case_info0 := mk_case_info ind0 npars Relevant in
    let boolPred : predicate term :=
      {| puinst := uvs ;
         pparams := subst_from_ctx (S (List.length indices_ctx)) param_ctx ;
         pcontext := (principal :: List.map decl_name indices_ctx)%list ;
         preturn := <% bool %> |}
    in
    let build_branch ctor_k (cb : constructor_body) : branch term :=
      {| bcontext := List.map decl_name cb.(cstr_args) ;
         bbody := if Nat.eqb ctor_k ctor_index then <% true %> else <% false %> |} in
    let brnchs := mapi build_branch (ind_ctors oindbody) in
    let body := tCase case_info0 boolPred (tRel 0) brnchs in
    it_mkLambda_or_LetIn ctx (tLambda principal (ind 0) body).


  (* Generation of the argument string for discriminators
     (all implicit but the main argument) *)
  Definition arguments_string id :=
    let args :=
      List.fold_left (fun (s:string) _ => ("{_} " ++ s)%bs) ctx "_ : simpl nomatch."%bs
    in
    ("Arguments " ++ id ++ " " ++ args)%bs.

  (* Generation of the notation for discriminators
     for constructor K of inductive I,
     [isK] : I -> bool *)
  Definition discriminator_notation id :=
    ("Notation ""'[' '" ++ id++ "' ']'"" := (toSProp " ++ discr_id id ++ ") (format ""[ " ++ id ++ " ]"").")%bs.

  (* Generation of the notation for projector
     for argument l of constructor K of inductive I,
     x : I ⊢ [K-l x] : typeof(l) *)
  Definition projector_notation id arg projector_id :=
    let common :=
    ("Notation ""'[' '" ++ id++ "' '-' '" ++ arg ++ "' x ']'"" := (" ++ projector_id ++
       String.concat "" (List.map (fun _ => " _"%bs) ctx))%bs
    in
    ((common ++ " x ltac:(assumption + easy)) (only parsing).")%bs,
      (common ++ " x _) (only printing, format ""[ " ++ id ++ " - " ++ arg ++ "  " ++ "x ]"").")%bs).

  (** Building projectors *)
  (* For constructor c_k :
    param_ctx ,,, indices_ctx ,, principal |- bodies

    bodies_i : match tRel 0 as principal' in ind0 indices_ctx'
                          return Rclause_i with
             | c_k (args) => ok_branch_i
             | _ => exfalso_branch
             end

   param_ctx ,,, args_>i |- arg_i_type

   param_ctx ,,, indices_ctx ,, principal ,, principal' ,,, indices_ctx' |-
   is_true_s (is_c_k param_ctx indices_ctx' principal') ->
   arg_i_type [bodies_>i] (*weakening !*)

   ok_branch_i := fun _ : sUnit => tRel i
   exfalso_branch := sexfalso (arg_i_type [bodies_>i] (* weakening *))

   *)
  Definition build_projectors (discriminator : term) (mp : modpath)
    : list (ident * term) :=
    let principal := relNamed "principal"%bs in
    let ctx1 := ctx ,, (vass principal (ind 0)) in

    let discr_arg := irrelNamed "discr"%bs in
    let discr_ty shift :=
      let discrBool := tApp discriminator (subst_from_ctx shift ctx1) in
      tApp <% is_true_s %> [ discrBool ]%list
    in

    let body_for_arg arg_dbi (arg : context_decl) (s : list (ident * term))
      : list (ident * term) :=

      let case_info0 := mk_case_info ind0 npars arg.(decl_name).(binder_relevance) in
      let ret_ty_in params_shift indices_principal_sub :=
        let apply_to_args '(id, _) :=
          tApp (tConst (mp, id) uvs)
               (subst_from_ctx params_shift param_ctx ++
                  indices_principal_sub ++
                  [ tRel 0 (* discriminator proof *)])
        in
        subst0 (List.map apply_to_args s) (lift params_shift #|s| arg.(decl_type))
      in

      let pred : predicate term :=
        let params := subst_from_ctx (S #|indices_ctx|) param_ctx in
        let pctx := (principal :: List.map decl_name indices_ctx)%list in

        let shift_params_return := #|pctx| + S (#|indices_ctx|) in

        let discr_ty :=
          let params_in_return := subst_from_ctx shift_params_return param_ctx in
          let indices_and_principal := List.rev (mapi (fun i _ => tRel i) pctx) in
          let discr_args := (params_in_return ++ indices_and_principal)%list in
          tApp <% is_true_s %> [ tApp discriminator discr_args ]%list
        in

        let ret_ty := ret_ty_in (S (shift_params_return)) (List.rev (mapi (fun i _ => tRel (S i)) pctx)) in

        {| puinst := uvs (* FIXME*) ;
          pparams := params ;
          pcontext := pctx ;
          preturn := tProd discr_arg discr_ty ret_ty
        |}
      in

      let build_branch ctor_k (cb : constructor_body) : branch term :=
        let correct_branch := tLambda anonIrrel <% sUnit %> (tRel (S arg_dbi)) in
        let exfalso_branch :=
          let params_shift := S (#|cb.(cstr_args)| + S (#|indices_ctx|)) in
          let cstr_term := tApp (tConstruct ind0 ctor_k uvs) (subst_from_ctx params_shift param_ctx ++ subst_from_ctx 1 cb.(cstr_args))%list in
          let ret_ty := ret_ty_in params_shift (List.map (lift0 1) cb.(cstr_indices) ++ [cstr_term])%list in
          tLambda discr_arg <% sEmpty %> (tApp <% @sexfalso %> [ret_ty ; tRel 0]%list)
        in

        {| bcontext := List.map decl_name cb.(cstr_args) ;
           bbody := if Nat.eqb ctor_k ctor_index
                    then correct_branch
                    else exfalso_branch |}
      in

      let brnchs := mapi build_branch (ind_ctors oindbody) in
      let body := tCase case_info0 pred (tRel 0) brnchs in
      ((proj_id ctor.(cstr_name) arg.(decl_name) (ctor.(cstr_arity) - S arg_dbi), body) :: s)%list
    in

    (* Retrieve the context of arguments from the closed type
       of current constructor *)
    let arg_ctx :=
      let ctor_ty := type_of_constructor mindbody ctor (ind0, 0 (*unused*)) uvs in
      let ctx_with_params := (decompose_prod_assum nil%list ctor_ty).1 in
      let last_arg_dbi := ctor.(cstr_arity) in
      List.firstn last_arg_dbi ctx_with_params
    in

    let bodys := fold_right_i body_for_arg nil%list arg_ctx in

    rev_map (fun '(id, body) => (id, it_mkLambda_or_LetIn ctx1 body)) bodys.

End Builders.


(* For debugging purpose *)
Definition mkQuoteDefinition (id : ident) (tm : term) :
  TemplateMonad unit :=
  tmDefinitionRed id (Some all) (A:=term) tm ;; ret tt.

Definition generate_discriminator : inductiveIteratorT :=
  fun ind mindbody oindbody ctor_idx ctor =>
    let discr_id := discr_id ctor.(cstr_name) in
    let discr_body := build_discriminators ind mindbody oindbody ctor_idx in
    t <- tmEval all discr_body ;;
    (* mkQuoteDefinition ("q" ++ discr_id)%bs t ;; *)
    tmMkDefinition discr_id t ;;
    tmMsg (arguments_string mindbody oindbody discr_id) ;;
    tmMsg (discriminator_notation ctor.(cstr_name)).

Definition gen_discriminators := mutualindbody_iteri generate_discriminator.


Definition constructor_arg_name (ctor : constructor_body) (i : nat) : option string :=
  match List.nth_error ctor.(cstr_args) (ctor.(cstr_arity) - S i) with
  | Some cd => Some (aname_ident cd.(decl_name) (string_of_nat i))
  | None => None
  end.

Definition generate_projector : inductiveIteratorT :=
  fun ind mindbody oindbody ctor_idx ctor =>
    let discr_id := discr_id ctor.(cstr_name) in
    let discr_body := build_discriminators ind mindbody oindbody ctor_idx in
    tmMkDefinition discr_id discr_body ;;
    tmMsg (arguments_string mindbody oindbody discr_id) ;;
    tmMsg (discriminator_notation ctor.(cstr_name)) ;;

    mp <- tmCurrentModPath tt ;;
    let discr_kn := (mp, discr_id) in
    let projs := build_projectors ind mindbody oindbody ctor_idx ctor (tConst discr_kn nil%list) mp in
    (* for debugging purpose *)
    (* monad_iter (fun '(id, body) => mkQuoteDefinition ("q" ++ id)%bs body) (List.rev projs) *)
    monad_iter (uncurry tmMkDefinition) projs ;;

    let mk_notation arg_i '(id, _) :=
      match constructor_arg_name ctor arg_i with
      | Some name =>
          let notations := projector_notation mindbody oindbody ctor.(cstr_name) name id in
          tmMsg notations.1 ;; tmMsg notations.2
      | None => ret tt
      end
    in
    monad_iteri mk_notation  projs.

Definition gen_projectors := mutualindbody_iteri generate_projector.


(** Examples of discriminators and projectors *)

Module DiscriminatorExamples.

Notation ok := (@eq_refl bool true).
Notation oks := stt.

Inductive myBool := myTrue | myFalse.

(* For discriminators only: *)
(* MetaCoq Run (gen_discriminators false "myBool"%bs). *)
MetaCoq Run (gen_projectors "myBool"%bs).

(*Copy pasted from the output of the command *)
Arguments ismyTrue _ : simpl nomatch.
Notation "'[' 'myTrue' ']'" := (toSProp ismyTrue) (format "[ myTrue ]").
Arguments ismyFalse _ : simpl nomatch.
Notation "'[' 'myFalse' ']'" := (toSProp ismyFalse) (format "[ myFalse ]").

Check oks : [myFalse] myFalse.
Fail Check oks : [myFalse] myTrue.

Inductive myList (A : Type) := myNil | myCons (hd : A) (tl : myList A) : myList A.
Arguments myNil {_}.
Arguments myCons {_} _ _.

MetaCoq Run (gen_projectors "myList"%bs).


Arguments ismyNil {_} _ : simpl nomatch.
Notation "'[' 'myNil' ']'" := (toSProp ismyNil) (format "[ myNil ]").
Arguments ismyCons {_} _ : simpl nomatch.
Notation "'[' 'myCons' ']'" := (toSProp ismyCons) (format "[ myCons ]").

Notation "'[' 'myCons' '-' 'hd' x ']'" := (projmyCons_hd _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'myCons' '-' 'hd' x ']'" := (projmyCons_hd _ x _) (only printing, format "[ myCons - hd  x ]").
Notation "'[' 'myCons' '-' 'tl' x ']'" := (projmyCons_tl _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'myCons' '-' 'tl' x ']'" := (projmyCons_tl _ x _) (only printing, format "[ myCons - tl  x ]").


Check ok : ismyNil (@myNil nat).
Check ok : ismyCons (myCons 5 myNil).
Fail Check ok : ismyNil (myCons 5 myNil).

Check oks : [myNil] (@myNil nat).
Check eq_refl : [myCons-hd myCons 5 myNil] = 5.

Check fun (v : myList bool) (h : [myCons] v) => [myCons-tl v].



Inductive mySig (A : Type) (B : A -> Type) :=
  | pair (dfst : A) (dsnd : B dfst) : mySig A B.
Arguments pair {_ _} _ _.

(* MetaCoq Run (gen_discriminators false "mySig"%bs). *)
MetaCoq Run (gen_projectors "mySig"%bs).

Arguments ispair {_} {_} _ : simpl nomatch.
Notation "'[' 'pair' ']'" := (toSProp ispair) (format "[ pair ]").

Notation "'[' 'pair' '-' 'dfst' x ']'" := (projpair_dfst _ _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'pair' '-' 'dfst' x ']'" := (projpair_dfst _ _ x _) (only printing, format "[ pair - dfst  x ]").
Notation "'[' 'pair' '-' 'dsnd' x ']'" := (projpair_dsnd _ _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'pair' '-' 'dsnd' x ']'" := (projpair_dsnd _ _ x _) (only printing, format "[ pair - dsnd  x ]").

Check ok : ispair (pair 5 (6 : (fun _ => nat) _)).



Inductive myBoolFam : bool -> Type :=
  | myIsTrue : myBoolFam true.

(* MetaCoq Run (gen_discriminators false "myBoolFam"%bs). *)
MetaCoq Run (gen_projectors "myBoolFam"%bs).

Arguments ismyIsTrue {_} _ : simpl nomatch.
Notation "'[' 'myIsTrue' ']'" := (toSProp ismyIsTrue) (format "[ myIsTrue ]").

Inductive vect (A : Type) : nat -> Type :=
| vnil : vect A 0
| vcons (hd : A) {len_tl} (tl : vect A len_tl) : vect A (S len_tl).
Arguments vnil {_}.
Arguments vcons {_} _ {_} _.
(* MetaCoq Run (gen_discriminators false "vect"%bs). *)
MetaCoq Run (gen_projectors "vect"%bs).


Arguments isvnil {_} {_} _ : simpl nomatch.
Notation "'[' 'vnil' ']'" := (toSProp isvnil) (format "[ vnil ]").

Arguments isvcons {_} {_} _ : simpl nomatch.
Notation "'[' 'vcons' ']'" := (toSProp isvcons) (format "[ vcons ]").

Notation "'[' 'vcons' '-' 'hd' x ']'" := (projvcons_hd _ _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'vcons' '-' 'hd' x ']'" := (projvcons_hd _ _ x _) (only printing, format "[ vcons - hd  x ]").
Notation "'[' 'vcons' '-' 'len_tl' x ']'" := (projvcons_len_tl _ _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'vcons' '-' 'len_tl' x ']'" := (projvcons_len_tl _ _ x _) (only printing, format "[ vcons - len_tl  x ]").
Notation "'[' 'vcons' '-' 'tl' x ']'" := (projvcons_tl _ _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'vcons' '-' 'tl' x ']'" := (projvcons_tl _ _ x _) (only printing, format "[ vcons - tl  x ]").

Check ok : isvnil (@vnil nat).
Check ok : isvcons (vcons true vnil).
Fail Check ok : isvcons (@vnil nat).


Inductive even : nat -> Type :=
| evenZ : even 0
| evenS {n} (oddn : odd n) : even (S n)
with odd : nat -> Type :=
| oddS {n} (evenn : even n) : odd (S n).

(* MetaCoq Run (gen_discriminators "even"%bs). *)
MetaCoq Run (gen_projectors "even"%bs).

Arguments ismyTrue _ : simpl nomatch.
Notation "'[' 'myTrue' ']'" := (toSProp ismyTrue) (format "[ myTrue ]").
Arguments ismyFalse _ : simpl nomatch.
Notation "'[' 'myFalse' ']'" := (toSProp ismyFalse) (format "[ myFalse ]").
Arguments ismyNil {_} _ : simpl nomatch.
Notation "'[' 'myNil' ']'" := (toSProp ismyNil) (format "[ myNil ]").
Arguments ismyCons {_} _ : simpl nomatch.
Notation "'[' 'myCons' ']'" := (toSProp ismyCons) (format "[ myCons ]").
Notation "'[' 'myCons' '-' 'hd' x ']'" := (projmyCons_hd _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'myCons' '-' 'hd' x ']'" := (projmyCons_hd _ x _) (only printing, format "[ myCons - hd  x ]").
Notation "'[' 'myCons' '-' 'tl' x ']'" := (projmyCons_tl _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'myCons' '-' 'tl' x ']'" := (projmyCons_tl _ x _) (only printing, format "[ myCons - tl  x ]").
Arguments ispair {_} {_} _ : simpl nomatch.
Notation "'[' 'pair' ']'" := (toSProp ispair) (format "[ pair ]").
Notation "'[' 'pair' '-' 'dfst' x ']'" := (projpair_dfst _ _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'pair' '-' 'dfst' x ']'" := (projpair_dfst _ _ x _) (only printing, format "[ pair - dfst  x ]").
Notation "'[' 'pair' '-' 'dsnd' x ']'" := (projpair_dsnd _ _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'pair' '-' 'dsnd' x ']'" := (projpair_dsnd _ _ x _) (only printing, format "[ pair - dsnd  x ]").
Arguments ismyIsTrue {_} _ : simpl nomatch.
Notation "'[' 'myIsTrue' ']'" := (toSProp ismyIsTrue) (format "[ myIsTrue ]").
Arguments isvnil {_} {_} _ : simpl nomatch.
Notation "'[' 'vnil' ']'" := (toSProp isvnil) (format "[ vnil ]").
Arguments isvcons {_} {_} _ : simpl nomatch.
Notation "'[' 'vcons' ']'" := (toSProp isvcons) (format "[ vcons ]").
Notation "'[' 'vcons' '-' 'hd' x ']'" := (projvcons_hd _ _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'vcons' '-' 'hd' x ']'" := (projvcons_hd _ _ x _) (only printing, format "[ vcons - hd  x ]").
Notation "'[' 'vcons' '-' 'len_tl' x ']'" := (projvcons_len_tl _ _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'vcons' '-' 'len_tl' x ']'" := (projvcons_len_tl _ _ x _) (only printing, format "[ vcons - len_tl  x ]").
Notation "'[' 'vcons' '-' 'tl' x ']'" := (projvcons_tl _ _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'vcons' '-' 'tl' x ']'" := (projvcons_tl _ _ x _) (only printing, format "[ vcons - tl  x ]").
Arguments isevenZ {_} _ : simpl nomatch.
Notation "'[' 'evenZ' ']'" := (toSProp isevenZ) (format "[ evenZ ]").
Arguments isevenS {_} _ : simpl nomatch.
Notation "'[' 'evenS' ']'" := (toSProp isevenS) (format "[ evenS ]").
Notation "'[' 'evenS' '-' 'n' x ']'" := (projevenS_n _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'evenS' '-' 'n' x ']'" := (projevenS_n _ x _) (only printing, format "[ evenS - n  x ]").
Notation "'[' 'evenS' '-' 'oddn' x ']'" := (projevenS_oddn _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'evenS' '-' 'oddn' x ']'" := (projevenS_oddn _ x _) (only printing, format "[ evenS - oddn  x ]").
Arguments isoddS {_} _ : simpl nomatch.
Notation "'[' 'oddS' ']'" := (toSProp isoddS) (format "[ oddS ]").
Notation "'[' 'oddS' '-' 'n' x ']'" := (projoddS_n _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'oddS' '-' 'n' x ']'" := (projoddS_n _ x _) (only printing, format "[ oddS - n  x ]").
Notation "'[' 'oddS' '-' 'evenn' x ']'" := (projoddS_evenn _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'oddS' '-' 'evenn' x ']'" := (projoddS_evenn _ x _) (only printing, format "[ oddS - evenn  x ]").

End DiscriminatorExamples.


