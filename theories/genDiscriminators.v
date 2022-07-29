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

  (*
  Let pr_name := nNamed "principal".

  (** Building discriminator classes *)
  Definition build_discr_class (dicriminator_kn:ident) :=
    let discriminator := tConst dicriminator_kn nil in
    let proj_ty (shift:nat) :=
        mkApp (tConst "Coq.Init.Datatypes.is_true" nil)
              (mkApp (mkApps_ctx discriminator (1+shift) ctx) (tRel shift))
    in
    let proj := (discr_class_proj_id ctor_id, proj_ty 1) in

    let ctor :=
        let class_ty :=
            mkApp (mkApps_ctx (tRel (npars + 2)) 2 ctx) (tRel 1) in
        let ctor_ty :=
            it_mkProd_or_LetIn ctx (tProd pr_name (ind 0) (tProd (* nAnon *) (nNamed (discr_class_proj_id ctor_id)) (proj_ty 0) class_ty))
        in
        (discr_class_ctor_id ctor_id, ctor_ty, 1 (* arity *))
    in

    let class_body :=
        Build_one_inductive_body (discr_class_id ctor_id)
                                (it_mkProd_or_LetIn ctx (tProd pr_name (ind 0) prop))
                                [:: InProp ; InSet ; InType]
                                [:: ctor]
                                [:: proj]
    in
    let ind_uvs := Monomorphic_ctx (LevelSetProp.of_list nil, ConstraintSet.empty) in
    Build_mutual_inductive_body
      BiFinite
      (1 + npars)
      (mkdecl pr_name None (ind 0) :: ctx)
      [:: class_body]
      ind_uvs.


  Definition rebuild_ctor ctor_idx shift_ctx nargs shift_args :=
    let ctor := tConstruct ind0 ctor_idx [::] (* FIXME *) in
    let ctor_ctx := mkApps_ctx ctor shift_ctx ctx in
    mkApps ctor_ctx (rev [seq tRel i | i <- iota shift_args nargs]).


  Quote Definition qeqrefl_true := (eq_refl true).

  Let pf_inst_name := nNamed "pf_inst".

  Context (discrclass_kn:ident).
  Let discrclass_ind0 := mkInd discrclass_kn 0.
  Let discrclass_ty shift principal :=
    mkApp (mkApps_ctx (tInd discrclass_ind0 [::] (*FIXME universes *)) shift ctx) principal.

  Let discrclass_ctor shift ind_ctor :=
    let ctor := tConstruct discrclass_ind0 0 [::] (* FIXME*) in
    mkApps ctor ([seq tRel i | i <- iota shift npars] ++ [:: ind_ctor ; qeqrefl_true]).

  (** Generation of the type of elimination for the discr class *)
  Definition build_discr_class_Etype :=
    let body :=
      let build_branch ctor_k '(((_ , ty),arity): (ident × term) × nat) :=
        let '(argtys, nargtys) :=
          let '(_, tys, _) := decompose_prod ty in
          let argtys := List.skipn npars tys in
          (fun shift =>mapi (fun i ty => lift shift i ty) argtys, List.length argtys)
        in
        let re_ctor shift := rebuild_ctor ctor_k (shift+2+nargtys) nargtys shift in
        let class_ty shift := discrclass_ty (shift+2+nargtys) (re_ctor shift) in
        let body :=
          if eq_nat ctor_k ctor_index then
            let re_class_ctor := discrclass_ctor (3+nargtys) (re_ctor 1) in
            mkApps qeq (class_ty 1 :: tRel 0 :: re_class_ctor :: nil)
          else qFalse
        in
        let brnch := build_const (argtys 2) (tLambda pf_inst_name (class_ty 0) body) in
        (nargtys, brnch)
      in
      let branches := utils.mapi build_branch (ind_ctors oindbody) in
      let motive := tLambda pr_name (ind 2) (tProd pf_inst_name (discrclass_ty 3 (tRel 0)) prop) in
      tCase (ind0, npars) motive (tRel 1) branches
    in
    let comm_cut := tProd pf_inst_name (discrclass_ty 1 (tRel 0)) (mkApp body (tRel 0)) in
    it_mkLambda_or_LetIn ctx (tLambda pr_name (ind 0) comm_cut).

  Quote Definition qnotF := notF.

  (* Record bidule (A:Type) (m : option A) := { bb : if m then nat else bool }. *)

  (* Quote Definition rid := (fun A m (H:bidule A m) => bb _ _ H). *)


  Quote Definition qeq_true_true := (true = true).
  Quote Definition quip_true := (@Eqdep_dec.UIP_refl_bool true).
  Quote Definition qf_equal := (@f_equal).

  Definition build_discr_class_E (discr_Ety_kn:ident) :=
    let build_branch ctor_k '(((_ , ty),arity): ctor_t) :=
      let '(argtys, nargtys) :=
        let '(_, tys, _) := decompose_prod ty in
        let argtys := List.skipn npars tys in
        (fun shift =>mapi (fun i ty => lift shift i ty) argtys, List.length argtys)
      in
      let re_ctor shift := rebuild_ctor ctor_k (shift+1+nargtys) nargtys shift in (* sy *)
      let class_ty shift := discrclass_ty (shift+1+nargtys) (re_ctor shift) in
      let discrclass_pf := tProj (discrclass_ind0, 1+npars, 0) (tRel 0) in (* is_pf *)
      let same_brnch :=
        let re_class_ctor := discrclass_ctor (2+nargtys) (re_ctor 1) in
        mkApps qf_equal [:: qeq_true_true; class_ty 1; re_class_ctor ; discrclass_pf; qeqrefl_true; mkApp quip_true discrclass_pf]
      in
      let diff_brnch := mkApp qnotF discrclass_pf in
      let body := if eq_nat ctor_k ctor_index then same_brnch else diff_brnch in
      let brnch := build_const (argtys 1) (tLambda pf_inst_name (class_ty 0) body) in
      (nargtys, brnch)
    in
    let brnchs := utils.mapi build_branch (ind_ctors oindbody) in
    let discrEty := tConst discr_Ety_kn [::] (* FIXME universes *) in
    let body := tCase (ind0, npars) (tRel 0) (mkApps_ctx discrEty 2 ctx) brnchs in
    it_mkLambda_or_LetIn ctx (tLambda pr_name (ind 0) body).

  (* Definition is_someE0 := (fun A (m:option A) => *)
  (*   match m as m0 return @is_Some_Etype A m0 with *)
  (*   | Some y => fun H0 : @is_Some A (Some y) => *)
  (*                let sy := Some y in *)
  (*                let ispf := @isSome_pf A sy H0 in *)
  (*                let tr := true in *)
  (*                @f_equal (@eq bool tr tr) *)
  (*                         (@is_Some A sy) *)
  (*                         (@mkIs_Some A sy) *)
  (*                         ispf *)
  (*                         (@eq_refl bool tr) *)
  (*                         (@Eqdep_dec.UIP_refl_bool tr ispf) *)
  (*   | None => fun H0 : @is_Some A None => @notF (@isSome_pf A None H0) *)
  (*   end). *)
 *)

  Definition arguments_string id :=
    let args :=
      List.fold_left (fun (s:string) _ => ("{_} " ++ s)%bs) ctx "_ : simpl nomatch."%bs
    in
    ("Arguments " ++ id ++ " " ++ args)%bs.

  Definition discriminator_notation id :=
    ("Notation ""'[' '" ++ id++ "' ']'"" := (toSProp " ++ discr_id id ++ ") (format ""[ " ++ id ++ " ]"").")%bs.
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


From Coq.Logic Require Import StrictProp.

Polymorphic Definition toSProp {X} (p : X -> bool) (x : X) : SProp :=
  if p x then sUnit else sEmpty.

Module DiscriminatorExamples.

Notation ok := eq_refl.
Notation oks := stt.

Inductive myBool := myTrue | myFalse.
MetaCoq Run (gen_discriminators false "myBool"%bs).
Arguments ismyTrue _ : simpl nomatch.
Notation "'[' 'myTrue' ']'" := (toSProp ismyTrue) (format "[ myTrue ]").
Arguments ismyFalse _ : simpl nomatch.
Notation "'[' 'myFalse' ']'" := (toSProp ismyFalse) (format "[ myFalse ]").

Check oks : [myFalse] myFalse.
Fail Check oks : [myFalse] myTrue.

Inductive myList (A : Type) := myNil | myCons (hd : A) (tl : myList A) : myList A.
Arguments myNil {_}.
Arguments myCons {_} _ _.

MetaCoq Run (gen_discriminators false "myList"%bs).

Arguments ismyNil {_} _ : simpl nomatch.
Notation "'[' 'myNil' ']'" := (toSProp ismyNil) (format "[ myNil ]").
Arguments ismyCons {_} _ : simpl nomatch.
Notation "'[' 'myCons' ']'" := (toSProp ismyCons) (format "[ myCons ]").


Check ok : ismyNil (@myNil nat).
Check ok : ismyCons (myCons 5 myNil).
Fail Check ok : ismyNil (myCons 5 myNil).

Definition bexfalso {A} (e : false = true) : A :=
  let B (b : bool) := if b return Type then unit else A in
  match e in _ = b return B b -> A with
  | eq_refl => fun x => x
  end tt.

Definition sexfalso {A} (e : sEmpty) : A := sEmpty_rect (fun _ => A) e.

Definition myCons_hd {A : Type} (l : myList A) : ismyCons l -> A :=
  match l with
  | myNil => bexfalso
  | myCons hd _ => fun _ => hd
  end.

Definition myCons_hd_s {A : Type} (l : myList A) : [myCons] l -> A :=
  match l with
  | myNil => sexfalso
  | myCons hd _ => fun _ => hd
  end.

Notation "'[' 'myCons' '-' 'hd' l ']'" :=
  (myCons_hd_s l ltac:(assumption)) (only parsing).
Notation "'[' 'myCons' '-' 'hd' l ']'" :=
  (myCons_hd_s l _) (only printing).

Check fun (l : myList nat) (h : [myCons] l) => Nat.eqb [myCons-hd l] 5.


Inductive mySig (A : Type) (B : A -> Type) :=
  | pair (dfst : A) (dsnd : B dfst) : mySig A B.
Arguments pair {_ _} _ _.

MetaCoq Run (gen_discriminators false "mySig"%bs).
Arguments ispair {_} {_} _ : simpl nomatch.

Check ok : ispair (pair 5 (6 : (fun _ => nat) _)).

Notation "'[' 'pair' ']' " := ispair.

Definition pair_dfst (A : Type) (B : A -> Type) (x : mySig A B)
  : [pair] x -> A :=
  match x with
  | pair dfst dsnd => fun _ => dfst
  end.

Arguments pair_dfst {_} {_} _ _.
Notation "'[' 'pair' '-' 'dfst' x ']'" :=
  (pair_dfst x ltac:(assumption)) (only parsing).
Notation "'[' 'pair' '-' 'dfst' x ']'" :=
  (pair_dfst x _) (only printing).

Definition pair_dsnd (A : Type) (B : A -> Type) (x : mySig A B)
  : forall (h : [pair] x), B [pair-dfst x] :=
  match x with
  | pair dfst dsnd => fun _ => dsnd
  end.

Arguments pair_dsnd {_} {_} _ _.
Notation "'[' 'pair' '-' 'dsnd' x ']'" :=
  (pair_dsnd x ltac:(assumption + easy)) (only parsing).
Notation "'[' 'pair' '-' 'dsnd' x ']'" :=
  (pair_dsnd x _) (only printing).

Eval cbn in let p : mySig nat (fun _ => nat) := pair 5 6 in
            [pair-dsnd p].


Inductive myBoolFam : bool -> Type :=
  | myIsTrue : myBoolFam true.
MetaCoq Run (gen_discriminators false "myBoolFam"%bs).

Inductive vect (A : Type) : nat -> Type :=
| vnil : vect A 0
| vcons (hd : A) {len_tl} (tl : vect A len_tl) : vect A (S len_tl).
Arguments vnil {_}.
Arguments vcons {_} _ {_} _.
MetaCoq Run (gen_discriminators false "vect"%bs).
Arguments isvnil {_} {_} _ : simpl nomatch.
Arguments isvcons {_} {_} _ : simpl nomatch.

Check ok : isvnil (@vnil nat).
Check ok : isvcons (vcons true vnil).
Fail Check ok : isvcons (@vnil nat).


Inductive even : nat -> Type :=
| evenZ : even 0
| evenS {n} (oddn : odd n) : even (S n)
with odd : nat -> Type :=
| oddS {n} (evenn : even n) : odd (S n).

MetaCoq Run (gen_discriminators false "even"%bs).
Arguments isevenZ {_} _ : simpl nomatch.
Arguments isevenS {_} _ : simpl nomatch.
Arguments isoddS {_} _ : simpl nomatch.

End DiscriminatorExamples.


Definition gen_discr_class :=
  let generate (debug:bool) ind mindbody oind_index oindbody ctor_idx ctor_id :=
    discr_name <- tmEval all (discr_id ctor_id) ;;
    discr_kn <- get_const discr_name;;
    let discr_class_mid := build_discr_class ind mindbody ctor_id discr_kn in
    let mindentry := mind_body_to_entry discr_class_mid in
    if debug then
      t <- tmEval all discr_class_mid ;;
      tmPrint t ;;
      t <- tmEval all mindentry ;;
      tmPrint t
    else
      tmMkInductive mindentry ;;
      (* class_id <- tmEval all (discr_class_id ctor_id) ;; *)
      (* tmExistingInstance class_id;; *)
      tmMsg ("Existing Class " ++ discr_class_id ctor_id ++ ".")
  in gen_from_mind generate.



(** Generation of the type of elimination for the discr class *)
Definition gen_discr_class_Etype :=
  let generate (debug:bool) ind mindbody oind_index oindbody ctor_idx ctor_id :=
    discrclass_name <- tmEval all (discr_class_id ctor_id) ;;
    discrclass_ind <- get_inductive discrclass_name;;
    let discr_class_Etype :=
      build_discr_class_Etype ind mindbody oindbody ctor_idx (* ctor_id *) (inductive_mind discrclass_ind)
    in
    if debug then t <- tmEval all discr_class_Etype ;; tmPrint t
    else
      tmMkDefinition (discr_class_Etype_id ctor_id) discr_class_Etype ;;
      tmMsg (arguments_string (discr_class_Etype_id ctor_id)
                              (ind_npars mindbody))
  in
  gen_from_mind generate.


Definition gen_discr_class_E :=
  let generate (debug:bool) ind mindbody oind_index oindbody ctor_idx ctor_id :=
    discrclass_name <- tmEval all (discr_class_id ctor_id) ;;
    discrclass_ind <- get_inductive discrclass_name;;
    discrclass_Ety_name <- tmEval all (discr_class_Etype_id ctor_id) ;;
    discrclass_Ety_kn <- get_const discrclass_Ety_name;;
    let discr_class_E :=
      build_discr_class_E ind mindbody oindbody ctor_idx (* ctor_id *) (inductive_mind discrclass_ind) discrclass_Ety_kn
    in
    if debug then t <- tmEval all discr_class_E ;; tmPrint t
    else
      (* tmMkDefinition (discr_class_E_id ctor_id) discr_class_E ;; *)
      tmMsg (arguments_string (discr_class_E_id ctor_id) (ind_npars mindbody))
  in
  gen_from_mind generate.


(** Tests *)
From Coq Require Import ssreflect.
Module TestGenDiscriminators.

  Inductive myBool := myTrue | myFalse.
  Run TemplateProgram (gen_discriminators false "myBool").
  Arguments ismyTrue _ : simpl nomatch.
  Arguments ismyFalse _ : simpl nomatch.

  Run TemplateProgram (gen_discr_class false "myBool").
  Existing Class is_myTrue.
  Existing Class is_myFalse.

  (** Bool *)
  Run TemplateProgram (gen_discriminators false "bool").
  (* Arguments istrue _ : simpl nomatch. *)
  (* Arguments isfalse _ : simpl nomatch. *)
  (* Class is_true0 (b:bool) := mkIs_true0 { istrue_pf0 : istrue b }. *)
  (* Run TemplateProgram (t <- tmQuoteInductive "is_true0";; tmPrint t). *)
  Run TemplateProgram (gen_discr_class true "bool").
  Existing Class is_true.
  Existing Class is_false.
  Run TemplateProgram (gen_discr_class_Etype false "bool").
  Arguments is_true_Etype _ : simpl nomatch.
  Arguments is_false_Etype _ : simpl nomatch.


  Run TemplateProgram (t <- tmAbout "is_true_Etype";; tmPrint t).
  Run TemplateProgram (s <- tmEval all (discr_class_Etype_id "true") ;; t <- get_const s;; tmPrint t).
  Run TemplateProgram (gen_discr_class_E true "bool").

  Record T := { t : nat }.
  Quote Definition Tproj := (fun (x:T) => t x).
  Run TemplateProgram (t <- tmUnquote Tproj ;; tmPrint t).

  Record T1 (b:bool) := mkT1 { t1 : Datatypes.is_true (istrue b) }.
  Existing Class T1.
  Quote Definition T1proj := (fun (x:T1 false) => notF (t1 _ x)).

  Run TemplateProgram (t <- tmUnquote T1proj ;; tmPrint t).

  Check mkIs_true true eq_refl.
  (* Set Printing All. *)
  (* Set Printing Universes. *)
  Quote Definition is_false_E_b2_0 := (* (isfalse_pf true). *)
    (fun pf_inst (* : is_false true *) =>  @isfalse_pf true pf_inst).
  Run TemplateProgram (t <- tmUnquote is_false_E_b2_0 ;; tmPrint t).


  Quote Definition is_true_E_b2_0 :=
    (fun (pf_inst : is_true false) => notF (istrue_pf _ pf_inst)).

  Run TemplateProgram (t <- tmUnquote is_true_E_b2_0 ;; tmPrint t).

  Definition is_true_E_b2 :=
    (tLambda (nNamed "pf_inst")
            (tApp
               (tInd
                  {|
                  inductive_mind := "Top.TestGenDiscriminators.is_true";
                  inductive_ind := 0 |} [::])
               [:: tConstruct
                     {|
                     inductive_mind := "Coq.Init.Datatypes.bool";
                     inductive_ind := 0 |} 1 [::]])
            (tApp (tConst "Coq.ssr.ssrbool.notF" [::])
               [:: tProj
                     ({|
                      inductive_mind := "Top.TestGenDiscriminators.is_true";
                      inductive_ind := 0 |}, 1, 0)
                     (tRel 0)])).

  (* Record is_true (principal : bool) : Prop := mkIs_true *)
  (*   { istrue_pf : Datatypes.is_true (istrue principal) }. *)

  Run TemplateProgram (t <- tmUnquote is_true_E_b2 ;; tmPrint t).
  Run TemplateProgram (t <- tmUnquote is_true_E ;; tmPrint t).

(* (tLambda (nNamed "principal") *)
(*    (tInd {| inductive_mind := "bool"; inductive_ind := 0 |} [::]) *)
(*    (tCase ({| inductive_mind := "bool"; inductive_ind := 0 |}, 0) *)
(*       (tRel 0) (tConst "Top.TestGenDiscriminators.is_false_Etype" [::]) *)
(*       [:: (0, *)
(*           tLambda (nNamed "pf_inst") *)
(*             (tApp *)
(*                (tInd *)
(*                   {| *)
(*                   inductive_mind := "Top.TestGenDiscriminators.is_false"; *)
(*                   inductive_ind := 0 |} [::]) *)
(*                [:: tConstruct *)
(*                      {| inductive_mind := "bool"; inductive_ind := 0 |} 0 *)
(*                      [::]]) *)
(*             (tApp (tConst "Coq.ssr.ssrbool.notF" [::]) *)
(*                [:: tProj *)
(*                      ({| *)
(*                       inductive_mind := "Top.TestGenDiscriminators.is_false"; *)
(*                       inductive_ind := 0 |}, 1, 0) *)
(*                      (tRel 0)])); *)
(*           (0, *)
(*           tLambda (nNamed "pf_inst") *)
(*             (tApp *)
(*                (tInd *)
(*                   {| *)
(*                   inductive_mind := "Top.TestGenDiscriminators.is_false"; *)
(*                   inductive_ind := 0 |} [::]) *)
(*                [:: tConstruct *)
(*                      {| inductive_mind := "bool"; inductive_ind := 0 |} 1 *)
(*                      [::]]) *)
(*             (tApp (tConst "Coq.Init.Logic.f_equal" [::]) *)
(*                [:: tApp *)
(*                      (tInd *)
(*                         {| *)
(*                         inductive_mind := "Coq.Init.Logic.eq"; *)
(*                         inductive_ind := 0 |} [::]) *)
(*                      [:: tInd *)
(*                            {| *)
(*                            inductive_mind := "Coq.Init.Datatypes.bool"; *)
(*                            inductive_ind := 0 |} [::]; *)
(*                          tConstruct *)
(*                            {| *)
(*                            inductive_mind := "Coq.Init.Datatypes.bool"; *)
(*                            inductive_ind := 0 |} 0 [::]; *)
(*                          tConstruct *)
(*                            {| *)
(*                            inductive_mind := "Coq.Init.Datatypes.bool"; *)
(*                            inductive_ind := 0 |} 0 [::]]; *)
(*                    tApp *)
(*                      (tInd *)
(*                         {| *)
(*                         inductive_mind := "Top.TestGenDiscriminators.is_false"; *)
(*                         inductive_ind := 0 |} [::]) *)
(*                      [:: tConstruct *)
(*                            {| inductive_mind := "bool"; inductive_ind := 0 |} *)
(*                            1 [::]]; *)
(*                    tApp *)
(*                      (tConstruct *)
(*                         {| *)
(*                         inductive_mind := "Top.TestGenDiscriminators.is_false"; *)
(*                         inductive_ind := 0 |} 0 [::]) *)
(*                      [:: tConstruct *)
(*                            {| inductive_mind := "bool"; inductive_ind := 0 |} *)
(*                            1 [::]; *)
(*                          tApp *)
(*                            (tConstruct *)
(*                               {| *)
(*                               inductive_mind := "Coq.Init.Logic.eq"; *)
(*                               inductive_ind := 0 |} 0 [::]) *)
(*                            [:: tInd *)
(*                                  {| *)
(*                                  inductive_mind := "Coq.Init.Datatypes.bool"; *)
(*                                  inductive_ind := 0 |} [::]; *)
(*                                tConstruct *)
(*                                  {| *)
(*                                  inductive_mind := "Coq.Init.Datatypes.bool"; *)
(*                                  inductive_ind := 0 |} 0 [::]]]; *)
(*                    tProj *)
(*                      ({| *)
(*                       inductive_mind := "Top.TestGenDiscriminators.is_false"; *)
(*                       inductive_ind := 0 |}, 1, 0) *)
(*                      (tRel 0); *)
(*                    tApp *)
(*                      (tConstruct *)
(*                         {| *)
(*                         inductive_mind := "Coq.Init.Logic.eq"; *)
(*                         inductive_ind := 0 |} 0 [::]) *)
(*                      [:: tInd *)
(*                            {| *)
(*                            inductive_mind := "Coq.Init.Datatypes.bool"; *)
(*                            inductive_ind := 0 |} [::]; *)
(*                          tConstruct *)
(*                            {| *)
(*                            inductive_mind := "Coq.Init.Datatypes.bool"; *)
(*                            inductive_ind := 0 |} 0 [::]]; *)
(*                    tApp (tConst "Coq.Logic.Eqdep_dec.UIP_refl_bool" [::]) *)
(*                      [:: tConstruct *)
(*                            {| *)
(*                            inductive_mind := "Coq.Init.Datatypes.bool"; *)
(*                            inductive_ind := 0 |} 0 [::]; *)
(*                          tProj *)
(*                            ({| *)
(*                             inductive_mind := "Top.TestGenDiscriminators.is_false"; *)
(*                             inductive_ind := 0 |}, 1, 0) *)
(*                            (tRel 0)]]))])) *)












  Run TemplateProgram (gen_discriminators false "option").
  Class is_none0 {A:Type} (m:option A) := mkIs_None0 { isNone_pf0 : isNone A m }.
  Run TemplateProgram (t <- tmQuoteInductive "is_none0";; tmPrint t).
  Class is_Some0 {A:Type} (m:option A) := mkIs_Some0 { isSome_pf0 : isSome A m }.
  Run TemplateProgram (t <- tmQuoteInductive "is_Some0";; tmPrint t).
  Run TemplateProgram (gen_discr_class false "option").
  Existing Class is_Some.
  (* FIXME : print the two following lines in gen_discr_class*)
  Arguments is_Some {_} _.
  Arguments isSome_pf {_} {_} {_}.
  Existing Class is_None.
  Run TemplateProgram (gen_discr_class_Etype false "option").
  Arguments is_Some_Etype {_} _ : simpl nomatch.
  Arguments is_None_Etype {_} _ : simpl nomatch.


  Quote Definition is_SomeEty0 := (fun (A:Type) m =>
    forall H : @is_Some A m, (match m with None => fun _ => False | Some v => fun H => H = mkIs_Some A (Some v) eq_refl end) H).

  (* From Genxs Require Import etaRecord. *)
  (* Run TemplateProgram (gen_eta_instance "is_Some0"). *)


  (* Definition is_Some_pf := fun A (m : option A) (H : is_Some A m) => match H with mkIs_Some pf => pf end. *)

  (* Definition eta_is_Some A (a:A) (H: is_Some A (Some a)) : H = mkIs_Some A (Some a) (is_Some_pf A (Some a) H) := *)
  (*   match H as h return h = mkIs_Some _ _ (is_Some_pf _ _ h) with mkIs_Some pf => eq_refl end. *)

  (* Definition is_someE' := (fun {A} {m:option A} => *)
  (*   match m as m0 return is_Some_Etype A m0 with *)
  (*   | Some y => fun H0 : is_Some A (Some y) => eq_trans (eta_is_Some _ _ H0) (f_equal (mkIs_Some _ (Some y)) (Eqdep_dec.UIP_refl_bool _ _)) *)
  (*                (* match H0 as H return H = mkIs_Some _ (Some y) eq_refl with *) *)
  (*                (* | mkIs_Some pf => f_equal (mkIs_Some _ (Some y)) (Eqdep_dec.UIP_refl_bool _ _) *) *)
  (*                (* end *) *)
  (*   | None => fun H0 : is_Some _ None => notF (is_Some_pf _ _ H0) *)
  (*   end : is_Some_Etype A m). *)

  Definition is_someE0 := (fun A (m:option A) =>
    match m as m0 return @is_Some_Etype A m0 with
    | Some y => fun H0 : @is_Some A (Some y) =>
                 let sy := Some y in
                 let tr := true in
                 let ispf := @isSome_pf A sy H0 in
                 @f_equal (@eq bool tr tr)
                          (@is_Some A sy)
                          (@mkIs_Some A sy)
                          ispf
                          (@eq_refl bool tr)
                          (@Eqdep_dec.UIP_refl_bool tr ispf)
    | None => fun H0 : @is_Some A None => @notF (@isSome_pf A None H0)
    end).

  Definition build_gen


  Definition is_someE0 := (fun A (m:option A) =>
    match m as m0 return @is_Some_Etype A m0 with
    | Some y => fun H0 : @is_Some A (Some y) =>
                 @f_equal (@eq bool true true)
                          (@is_Some A (Some y))
                          (@mkIs_Some A (Some y))
                          (@isSome_pf A (Some y) H0)
                          (@eq_refl bool true)
                          (@Eqdep_dec.UIP_refl_bool true (@isSome_pf A (Some y) H0))
    | None => fun H0 : @is_Some A None => @notF (@isSome_pf A None H0)
    end).

  Run TemplateProgram (gen_discriminators false "prod").
  Class is_pair0 (A B : Type) (p : A * B) := mkIs_pair0 { ispair_pf0 : ispair A B p }.

  Run TemplateProgram (t <- tmQuoteInductive "is_pair0";; tmPrint t).
  Run TemplateProgram (gen_discr_class false "prod").
  Existing Class is_pair.
  Run TemplateProgram (gen_discr_class_Etype false "option").



  Inductive I (A:Type) := IX : I A | IY : nat -> I A | IZ : forall (x:nat), x+x = 2 -> I A.

  Definition isIX0 {A} (z : I A) := match z with | IX => true | _ => false end.
  Arguments isIX0 [_] _.
  Quote Definition qisIX0 := Eval unfold isIX0 in isIX0.

  Run TemplateProgram (gen_discriminators false "I").
  Run TemplateProgram (gen_discr_class false "I").
  Existing Class is_IX.
  Existing Class is_IY.
  Existing Class is_IZ.

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
