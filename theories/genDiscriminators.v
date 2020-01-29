From mathcomp Require Import ssreflect.seq.
From Coq Require Import Strings.String.
From MetaCoq.Template Require Import All.
From Genxs Require Import metacoq_utils.



Import MonadNotation.

Section IteriInd.
  Let ctor_t := (ident × term) × nat.
  Context (h : inductive -> mutual_inductive_body -> nat -> one_inductive_body -> nat -> ctor_t -> TemplateMonad unit).


  Definition oneindbody_iteri
           (ind : inductive)
           (mindbody : mutual_inductive_body)
           (oind_index : nat)
           (oindbody : one_inductive_body)
  : TemplateMonad unit :=
  monad_iteri (h ind mindbody oind_index oindbody) (ind_ctors oindbody).

  Definition mutualindbody_iteri (mindname : qualid)
  : TemplateMonad unit :=
    ind <- get_inductive mindname ;;
    mindbody <- tmQuoteInductive mindname ;;
    monad_iteri (oneindbody_iteri ind mindbody) (ind_bodies mindbody).

End IteriInd.


(** Naming conventions *)
Section Naming.
  Context (ctor_id : ident).

  Definition discr_id := "is" ++ ctor_id.
  Definition discr_class_id := "is_" ++ ctor_id.
  Definition discr_class_proj_id := "is" ++ ctor_id ++ "_pf".
  Definition discr_class_ctor_id := "mkIs_" ++ ctor_id.
  Definition discr_class_Etype_id := discr_class_id ++ "_Etype".

End Naming.



(** Generation of discrimators *)

Definition qBool :=
  tInd {| inductive_mind := "Coq.Init.Datatypes.bool"; inductive_ind := 0 |} nil.

Quote Definition qtrue := true.
Quote Definition qfalse := false.

Definition lf := String (Ascii.ascii_of_nat 10) EmptyString.

Definition indctor_gen_discriminators
           (debug:bool)
           (indname : qualid)
           (mindbody : mutual_inductive_body)
           (oind_index : nat)
           (oindbody : one_inductive_body)
           (ctor_index : nat)
           '(((ctor_id, _ty), _arity) : (ident × term) × nat) :=
  let discr_id := discr_id ctor_id in
  let ctx := ind_params mindbody in
  let discr_body :=
    let universes := nil (*FIXME*) in
    let npars := ind_npars mindbody in
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
    let args :=
        List.fold_left (fun s _ => "{_} " ++ s) ctx "_ : simpl nomatch."
    in
    tmMsg (discr_id ++ " is defined. You may want to execute"
                    ++ lf ++ "Arguments " ++ discr_id ++ " " ++ args).


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

(** Building discriminator classes *)

Definition build_discr_class
           (indname : qualid)
           (mindbody : mutual_inductive_body)
           (oind_index : nat)
           (oindbody : one_inductive_body)
           (ctor_index : nat)
           '(((ctor_id, _ty), _arity) : (ident × term) × nat)
           (dicriminator_kn:ident) :=
  let pr_name := nNamed "principal" in
  let prop :=
      tSort (Universe.make'' (Level.lProp, false) nil)
  in

  let universes := nil (*FIXME*) in
  let npars := ind_npars mindbody in
  let ctx := ind_params mindbody in
  let ind0 := mkInd indname oind_index in
  let ind shift := mkApps_ctx (tInd ind0 universes) shift ctx in


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
          it_mkProd_or_LetIn ctx (tProd pr_name (ind 0) (tProd nAnon (* (nNamed "pf") *) (proj_ty 0) class_ty))
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
  let ind_uvs :=
      Monomorphic_ctx (LevelSetProp.of_list nil, ConstraintSet.empty)
  in
  Build_mutual_inductive_body
    BiFinite
    (1 + npars)
    (mkdecl pr_name None (ind 0) :: ctx)
    [:: class_body]
    ind_uvs.


Definition indctor_gen_discr_class
           (debug:bool)
           (indname : qualid)
           (mindbody : mutual_inductive_body)
           (oind_index : nat)
           (oindbody : one_inductive_body)
           (ctor_index : nat)
           ctor
  :=
    let '((ctor_id, ty), arity) := ctor in
    discr_name <- tmEval all (discr_id ctor_id) ;;
    discr_kn <- get_const discr_name;;
    let discr_class_mid := build_discr_class indname mindbody oind_index oindbody ctor_index ctor discr_kn in
    let mindentry := mind_body_to_entry discr_class_mid in
    if debug then
      t <- tmEval all discr_class_mid ;;
      tmPrint t
    else
      tmMkInductive mindentry ;;
      (* class_id <- tmEval all (discr_class_id ctor_id) ;; *)
      (* tmExistingInstance class_id;; *)
      tmMsg ("Existing Class " ++ discr_class_id ctor_id ++ ".").

Definition oid_gen_discr_class
           (debug:bool)
           (indname : qualid)
           (mindbody : mutual_inductive_body)
           (oind_index : nat)
           (oindbody : one_inductive_body)
  : TemplateMonad unit :=
  monad_iteri
    (indctor_gen_discr_class debug indname mindbody oind_index oindbody)
    (ind_ctors oindbody).

Definition gen_discr_class (debug:bool) (mindname : qualid) (* Is it a kername ?*)
  : TemplateMonad unit :=
  mindbody <- tmQuoteInductive mindname ;;
  monad_iteri
    (oid_gen_discr_class debug mindname mindbody)
    (ind_bodies mindbody).


(** Generation of the type of elimination for the discr class *)
Quote Definition qeq_refl := @eq_refl.
Quote Definition qFalse := False.
Quote Definition qeq := @eq.

Definition build_discr_class_Etype
           (indname : qualid)
           (mindbody : mutual_inductive_body)
           (oind_index : nat)
           (oindbody : one_inductive_body)
           (ctor_index : nat)
           '(((ctor_id, _ty), _arity) : (ident × term) × nat)
           (discrclass_kn:ident) :=
  let pr_name := nNamed "principal" in
  let prop := tSort (Universe.make'' (Level.lProp, false) nil) in
  let pf_inst_name := nNamed "pf_inst" in

  let universes := nil (*FIXME*) in
  let npars := ind_npars mindbody in
  let ctx := ind_params mindbody in
  let ind0 := mkInd indname oind_index in
  let ind shift := mkApps_ctx (tInd ind0 universes) shift ctx in

  let discrclass_ind := mkInd discrclass_kn 0 in
  let class_ty shift principal :=
    mkApp (mkApps_ctx (tInd discrclass_ind [::] (*FIXME*)) shift ctx) principal
  in

  let body :=
    let build_branch ctor_k '(((_ , ty),arity): (ident × term) × nat) :=
      let '(argtys, nargtys) :=
        let '(_, tys, _) := decompose_prod ty in
        let argtys := List.skipn npars tys in
        (fun shift =>mapi (fun i ty => lift shift i ty) argtys, List.length argtys)
      in
      let re_ctor shift :=
        let ctor := tConstruct ind0 ctor_k [::] (* FIXME *) in
        mkApps (mkApps_ctx ctor (shift+2+nargtys) ctx) (rev [seq tRel i | i <- iota shift nargtys])
      in
      let class_ty shift := class_ty (shift+2+nargtys) (re_ctor shift) in
      let body :=
        if eq_nat ctor_k ctor_index then
          (* let refl_ctor := mkApps qeq_refl (ind (nargtys + 2) :: re_ctor :: nil) in *)
          let refl_ctor := mkApps qeq_refl (qBool :: qtrue :: nil) in
          let discr_class_ctor := tConstruct discrclass_ind 0 [::] (* FIXME*)in
          let re_class_ctor := mkApps discr_class_ctor ([seq tRel i | i <- iota (3+nargtys) npars] ++ [:: re_ctor 1 ; refl_ctor]) in
          mkApps qeq (class_ty 1 :: tRel 0 :: re_class_ctor :: nil)
        else qFalse
      in
      let brnch := build_const (argtys 2) (tLambda pf_inst_name (class_ty 0) body) in
      (nargtys, brnch)
    in
    let branches := utils.mapi build_branch (ind_ctors oindbody) in
    let motive := tLambda pr_name (ind 2) (tProd pf_inst_name (class_ty 3 (tRel 0)) prop) in
    tCase (ind0, npars) motive (tRel 1) branches
  in
  let comm_cut := tProd pf_inst_name (class_ty 1 (tRel 0)) (mkApp body (tRel 0)) in
  it_mkLambda_or_LetIn ctx (tLambda pr_name (ind 0) comm_cut).


Definition gen_discr_class_Etype (debug:bool) (mindname : qualid)
  : TemplateMonad unit :=
  mindbody <- tmQuoteInductive mindname ;;
  let oid_gen oind_index oindbody :=
    let ctor_gen ctor_idx ctor :=
      let '((ctor_id, ty), arity) := ctor in
      discrclass_name <- tmEval all (discr_class_id ctor_id) ;;
      discrclass_ind <- get_inductive discrclass_name;;
      let discr_class_Etype :=
        build_discr_class_Etype mindname mindbody oind_index oindbody ctor_idx ctor (inductive_mind discrclass_ind)
      in
      if debug then t <- tmEval all discr_class_Etype ;; tmPrint t
      else
        tmMkDefinition (discr_class_Etype_id ctor_id) discr_class_Etype ;;
        tmMsg ("Arguments " ++ discr_class_Etype_id ctor_id ++ ".") (*FIXME*)
    in
    monad_iteri ctor_gen (ind_ctors oindbody)
  in
  monad_iteri oid_gen (ind_bodies mindbody).

(** Tests *)
Module TestGenDiscriminators.
  Set Primitive Projections.

  Inductive myBool := myTrue | myFalse.
  Run TemplateProgram (gen_discriminators false "myBool").
  Arguments ismyTrue _ : simpl nomatch.
  Arguments ismyFalse _ : simpl nomatch.

  Run TemplateProgram (gen_discr_class false "myBool").
  Existing Class is_myTrue.
  Existing Class is_myFalse.

  Run TemplateProgram (gen_discriminators false "bool").
  Class is_true0 (b:bool) := mkIs_true0 { istrue_pf0 : istrue b }.
  Run TemplateProgram (t <- tmQuoteInductive "is_true0";; tmPrint t).
  Run TemplateProgram (gen_discr_class false "bool").
  Run TemplateProgram (gen_discr_class_Etype false "bool").

  Run TemplateProgram (gen_discriminators false "option").
  Class is_none0 {A:Type} (m:option A) := mkIs_None0 { isNone_pf0 : isNone A m }.
  Run TemplateProgram (t <- tmQuoteInductive "is_none0";; tmPrint t).
  Class is_Some0 {A:Type} (m:option A) := mkIs_Some0 { isSome_pf0 : isSome A m }.
  Run TemplateProgram (t <- tmQuoteInductive "is_Some0";; tmPrint t).
  Run TemplateProgram (gen_discr_class false "option").
  Existing Class is_Some.
  Existing Class is_None.
  Run TemplateProgram (gen_discr_class_Etype false "option").

  Quote Definition is_SomeEty0 := (fun (A:Type) m =>
    forall H : is_Some A m, (match m with None => fun _ => False | Some v => fun H => H = mkIs_Some A (Some v) eq_refl end) H).

  From Genxs Require Import etaRecord.
  Run TemplateProgram (gen_eta_instance "is_Some0").


  Quote Definition is_someE' := (fun {A} {m:option A} =>
    match m with
    | Some y => fun H0 : is_some (Some y) =>
                f_equal (mkIsSome _ (Some y)) (Eqdep_dec.UIP_refl_bool _ _)
    | None => fun H0 : is_some None => notF is_some_pf
    end :
    forall H : is_some m, (if m is Some v then fun H => H = ⦅v⦆ else fun _ => False) H).

  Run TemplateProgram (gen_discriminators false "prod").
  Class is_pair0 (A B : Type) (p : A * B) := mkIs_pair0 { ispair_pf0 : ispair A B p }.

  Run TemplateProgram (t <- tmQuoteInductive "is_pair0";; tmPrint t).
  Run TemplateProgram (gen_discr_class false "prod").
  Existing Class is_pair.


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
