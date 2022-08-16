(* From mathcomp Require ssreflect.seq ssreflect.ssrbool. *)
(* From Coq Require Import Strings.String. *)
From MetaCoq.Template Require Import All.
From Genxs Require Import metacoq_utils.


Set Primitive Projections.
Import MCMonadNotation.

Section IteriInd.
  Universe u.
  Context (h : inductive -> mutual_inductive_body -> nat -> one_inductive_body -> nat -> constructor_body -> TemplateMonad@{_ u} unit).

  Set Printing Universes.

  Definition oneindbody_iteri
           (ind : inductive)
           (mindbody : mutual_inductive_body)
           (oind_index : nat)
           (oindbody : one_inductive_body)
  : TemplateMonad@{_ u} unit :=
  monad_iteri (h ind mindbody oind_index oindbody) (ind_ctors oindbody).

  Definition mutualindbody_iteri (mindname : qualid)
  : TemplateMonad@{_ u} unit :=
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
  Definition discr_class_id := "is_" ++ ctor_id.
  Definition discr_class_proj_id := "is" ++ ctor_id ++ "_pf".
  Definition discr_class_ctor_id := "mkIs_" ++ ctor_id.
  Definition discr_class_Etype_id := discr_class_id ++ "_Etype".
  Definition discr_class_E_id := discr_class_id ++ "_E".

  Definition proj_id (argname : aname) (arg_i : nat) :=
    "proj" ++ ctor_id ++ "_" ++ aname_ident argname (string_of_nat arg_i).
End Naming.



(** Generation of discrimators *)

Definition qBool := <% bool %>.
Definition qtrue := <% true %>.
Definition qfalse := <% false %>.

(* Definition lf := String (Ascii.ascii_of_nat 10) EmptyString. *)

Definition qeq_refl := <% @eq_refl %>.
Definition qFalse := <% False %>.
Definition qeq := <% @eq %>.

(* Examples *)
Definition qisZ := <% fun n : nat => match n with | 0 => true | _ => false end %>.
Definition qisSuc := <% fun n : nat => match n with | S _ => true | _ => false end %>.
Definition qisCons := <% fun A (l : list A) => match l with | cons _ _ => true | _ => false end %>.

Definition qisEqrefl := <% fun A x y (e : @eq A x y) =>
                            match e with | eq_refl => true end %>.


Definition relNamed (s : string) : aname :=
  {| binder_name := nNamed s ; binder_relevance := Relevant |}.
Definition irrelNamed (s : string) : aname :=
  {| binder_name := nNamed s ; binder_relevance := Irrelevant |}.
Definition anonIrrel : aname := {| binder_name := nAnon ; binder_relevance := Irrelevant |}.

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

(* Inductive foo := Foo : nat -> bool -> foo. *)

(* MetaCoq Run ( *)
(*     ind <- get_inductive "foo"%bs ;; *)
(*     mindbody <- tmQuoteInductive ind.(inductive_mind) ;; *)
(*     tmPrint mindbody). *)
(* Check <% @pair %>. *)


(* MetaCoq Run (tyEvar <- @tmQuote Type _ ;; *)
(*              tmMkDefinition "testA"%bs (tApp <% S %> [tApp <% @id %> [tyEvar; <% 0 %> ]%list ]%list)). *)

(* MetaCoq Run (t <- @tmQuote nat _ ;; tmPrint t). *)


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


  Definition arguments_string id :=
    let args :=
      List.fold_left (fun (s:string) _ => ("{_} " ++ s)%bs) ctx "_ : simpl nomatch."%bs
    in
    ("Arguments " ++ id ++ " " ++ args)%bs.

  Definition discriminator_notation id :=
    ("Notation ""'[' '" ++ id++ "' ']'"" := (toSProp " ++ discr_id id ++ ") (format ""[ " ++ id ++ " ]"").")%bs.

  Definition projector_notation id arg projector_id :=
    let common :=
    ("Notation ""'[' '" ++ id++ "' '-' '" ++ arg ++ "' x ']'"" := (" ++ projector_id ++
       String.concat "" (List.map (fun _ => " _"%bs) ctx))%bs
    in
    ((common ++ " x ltac:(assumption + easy)) (only parsing).")%bs,
      (common ++ " x _) (only printing, format ""[ " ++ id ++ " - " ++ arg ++ "  " ++ "x ]"").")%bs).

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


Definition gen_from_mind  generate (debug:bool) (mindname : qualid)
  : TemplateMonad unit :=
  ind <- get_inductive mindname ;;
  mindbody <- tmQuoteInductive ind.(inductive_mind) ;;
  let oid_gen _ oindbody :=
    ind <- get_inductive oindbody.(ind_name) ;;
    let ctor_gen := generate debug ind mindbody oindbody in
    monad_iteri ctor_gen (ind_ctors oindbody)
  in
  monad_iteri oid_gen (ind_bodies mindbody).

Definition gen_discriminators :=
  let generate (debug:bool) ind mindbody oindbody ctor_idx ctor :=
    let discr_id := discr_id ctor.(cstr_name) in
    let discr_body := build_discriminators ind mindbody oindbody ctor_idx in
    t <- tmEval all discr_body ;;
    if debug then tmPrint t
    else
      tmMkDefinition discr_id t ;;
      tmMsg (arguments_string mindbody oindbody discr_id) ;;
      tmMsg (discriminator_notation ctor.(cstr_name))
  in
  gen_from_mind generate.

Definition mkQuoteDefinition (id : ident) (tm : term) :
  TemplateMonad unit :=
  tmDefinitionRed id (Some all) (A:=term) tm ;; ret tt.


Definition constructor_arg_name (ctor : constructor_body) (i : nat) : option string :=
  match List.nth_error ctor.(cstr_args) (ctor.(cstr_arity) - S i) with
  | Some cd => Some (aname_ident cd.(decl_name) (string_of_nat i))
  | None => None
  end.

Definition gen_projectors :=
  let generate (debug:bool) ind mindbody oindbody ctor_idx ctor :=
    let discr_id := discr_id ctor.(cstr_name) in
    let discr_body := build_discriminators ind mindbody oindbody ctor_idx in
    tmMkDefinition discr_id discr_body ;;
    tmMsg (arguments_string mindbody oindbody discr_id) ;;
    tmMsg (discriminator_notation ctor.(cstr_name)) ;;

    mp <- tmCurrentModPath tt ;;
    let discr_kn := (mp, discr_id) in
    let projs := build_projectors ind mindbody oindbody ctor_idx ctor (tConst discr_kn nil%list) mp in
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
    monad_iteri mk_notation  projs
  in
  gen_from_mind generate.


Module DiscriminatorExamples.

Notation ok := (@eq_refl bool true).
Notation oks := stt.

Inductive myBool := myTrue | myFalse.

(* MetaCoq Run (gen_discriminators false "myBool"%bs). *)
MetaCoq Run (gen_projectors false "myBool"%bs).
Arguments ismyTrue _ : simpl nomatch.
Notation "'[' 'myTrue' ']'" := (toSProp ismyTrue) (format "[ myTrue ]").
Arguments ismyFalse _ : simpl nomatch.
Notation "'[' 'myFalse' ']'" := (toSProp ismyFalse) (format "[ myFalse ]").

Check oks : [myFalse] myFalse.
Fail Check oks : [myFalse] myTrue.

Inductive myList (A : Type) := myNil | myCons (hd : A) (tl : myList A) : myList A.
Arguments myNil {_}.
Arguments myCons {_} _ _.

(* MetaCoq Run (gen_discriminators false "myList"%bs). *)
MetaCoq Run (gen_projectors false "myList"%bs).

(* Definition qhd := Eval cbv in projmyCons_hd. *)
(* MetaCoq Run (tmMkDefinition "phd"%bs qhd). *)

(* Definition qtl := Eval cbv in projmyCons_tl. *)
(* MetaCoq Run (tmMkDefinition "ptl"%bs qtl). *)

(* MetaCoq Run (list <- get_inductive "myList"%bs ;; *)
(*              ind <- tmQuoteInductive list.(inductive_mind) ;; *)
(*              tmPrint ind). *)

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


(* Definition myCons_hd {A : Type} (l : myList A) : ismyCons l -> A := *)
(*   match l with *)
(*   | myNil => bexfalso *)
(*   | myCons hd _ => fun _ => hd *)
(*   end. *)

(* Definition myCons_hd_s {A : Type} (l : myList A) : [myCons] l -> A := *)
(*   match l with *)
(*   | myNil => sexfalso *)
(*   | myCons hd _ => fun _ => hd *)
(*   end. *)

(* Notation "'[' 'myCons' '-' 'hd' l ']'" := *)
(*   (myCons_hd_s l ltac:(assumption)) (only parsing). *)
(* Notation "'[' 'myCons' '-' 'hd' l ']'" := *)
(*   (myCons_hd_s l _) (only printing). *)

(* Check fun (l : myList nat) (h : [myCons] l) => Nat.eqb [myCons-hd l] 5. *)


Inductive mySig (A : Type) (B : A -> Type) :=
  | pair (dfst : A) (dsnd : B dfst) : mySig A B.
Arguments pair {_ _} _ _.

(* MetaCoq Run (gen_discriminators false "mySig"%bs). *)
MetaCoq Run (gen_projectors false "mySig"%bs).

Arguments ispair {_} {_} _ : simpl nomatch.
Notation "'[' 'pair' ']'" := (toSProp ispair) (format "[ pair ]").

Notation "'[' 'pair' '-' 'dfst' x ']'" := (projpair_dfst _ _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'pair' '-' 'dfst' x ']'" := (projpair_dfst _ _ x _) (only printing, format "[ pair - dfst  x ]").
Notation "'[' 'pair' '-' 'dsnd' x ']'" := (projpair_dsnd _ _ x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'pair' '-' 'dsnd' x ']'" := (projpair_dsnd _ _ x _) (only printing, format "[ pair - dsnd  x ]").

(* Definition qdfst := Eval cbv in projpair_dfst. *)
(* MetaCoq Run (tmMkDefinition "pdfst"%bs qdfst). *)

(* Definition qdsnd := Eval cbn in projpair_dsnd. *)

(* MetaCoq Run (tmMkDefinition "pdsnd'"%bs qdsnd'). *)
(* MetaCoq Run (mp <- tmCurrentModPath tt ;; tmPrint mp). *)
(* Check <% pfst %>. *)
Check ok : ispair (pair 5 (6 : (fun _ => nat) _)).


(* Definition pair_dfst (A : Type) (B : A -> Type) (x : mySig A B) *)
(*   : [pair] x -> A := *)
(*   match x with *)
(*   | pair dfst dsnd => fun _ => dfst *)
(*   end. *)

(* Arguments pair_dfst {_} {_} _ _. *)
(* Notation "'[' 'pair' '-' 'dfst' x ']'" := *)
(*   (pair_dfst x ltac:(assumption)) (only parsing). *)
(* Notation "'[' 'pair' '-' 'dfst' x ']'" := *)
(*   (pair_dfst x _) (only printing). *)

(* Definition pair_dsnd (A : Type) (B : A -> Type) (x : mySig A B) *)
(*   : forall (h : [pair] x), B [pair-dfst x] := *)
(*   match x with *)
(*   | pair dfst dsnd => fun _ => dsnd *)
(*   end. *)

(* Arguments pair_dsnd {_} {_} _ _. *)
(* Notation "'[' 'pair' '-' 'dsnd' x ']'" := *)
(*   (pair_dsnd x ltac:(assumption + easy)) (only parsing). *)
(* Notation "'[' 'pair' '-' 'dsnd' x ']'" := *)
(*   (pair_dsnd x _) (only printing). *)

(* Eval cbn in let p : mySig nat (fun _ => nat) := pair 5 6 in *)
(*             [pair-dsnd p]. *)


Inductive myBoolFam : bool -> Type :=
  | myIsTrue : myBoolFam true.
(* MetaCoq Run (gen_discriminators false "myBoolFam"%bs). *)
MetaCoq Run (gen_projectors false "myBoolFam"%bs).

Arguments ismyIsTrue {_} _ : simpl nomatch.
Notation "'[' 'myIsTrue' ']'" := (toSProp ismyIsTrue) (format "[ myIsTrue ]").

Inductive vect (A : Type) : nat -> Type :=
| vnil : vect A 0
| vcons (hd : A) {len_tl} (tl : vect A len_tl) : vect A (S len_tl).
Arguments vnil {_}.
Arguments vcons {_} _ {_} _.
(* MetaCoq Run (gen_discriminators false "vect"%bs). *)
MetaCoq Run (gen_projectors false "vect"%bs).

(* MetaCoq Run (tmMkDefinition "projvcons_hd"%bs qprojvcons_hd). *)
(* MetaCoq Run (tmMkDefinition "projvcons_len_tl"%bs qprojvcons_len_tl). *)

(* Definition qprojvcons_tl0 := Eval cbv in qprojvcons_tl. *)
(* MetaCoq Run (tmMkDefinition "projvcons_tl"%bs qprojvcons_tl0). *)

(* Definition pvcons_tl A n (v : vect A n) : *)
(*   forall (h : is_true_s (isvcons A n v)), vect A (projvcons_len_tl A n v h) := *)
(*   match v with *)
(*   | vnil => fun e : sEmpty => sexfalso e *)
(*   | vcons _ _ tl => fun _ => tl *)
(*   end. *)

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

(* MetaCoq Run (gen_discriminators false "even"%bs). *)
MetaCoq Run (gen_projectors false "even"%bs).
Arguments isevenZ {_} _ : simpl nomatch.
Arguments isevenS {_} _ : simpl nomatch.
Arguments isoddS {_} _ : simpl nomatch.

End DiscriminatorExamples.


