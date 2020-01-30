From mathcomp Require Import ssreflect.seq ssreflect.ssrbool.
From Coq Require Import Strings.String.
From MetaCoq.Template Require Import All.
From Genxs Require Import metacoq_utils.


Set Primitive Projections.
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
  Definition discr_class_E_id := discr_class_id ++ "_E".

End Naming.



(** Generation of discrimators *)

Definition qBool :=
  tInd {| inductive_mind := "Coq.Init.Datatypes.bool"; inductive_ind := 0 |} nil.

Quote Definition qtrue := true.
Quote Definition qfalse := false.

Definition lf := String (Ascii.ascii_of_nat 10) EmptyString.

Definition arguments_string id npars :=
  let args :=
    List.fold_left (fun s _ => "{_} " ++ s) (iota 0 npars) "_ : simpl nomatch."
  in
  "Arguments " ++ id ++ " " ++ args.

Quote Definition qeq_refl := @eq_refl.
Quote Definition qFalse := False.
Quote Definition qeq := @eq.

Section Builders.
  Let ctor_t := (ident × term) × nat.
  Context (indname : qualid)
           (mindbody : mutual_inductive_body)
           (oind_index : nat)
           (oindbody : one_inductive_body)
           (ctor_index : nat)
           (* (ctor : ctor_t) *)
           (* (ctor_id := fst (fst ctor)). *)
           (ctor_id : ident).

  Let npars := ind_npars mindbody.
  Let ctx := ind_params mindbody.
  Context (uvs := nil)
          (ind0 := mkInd indname oind_index)
          (ind := fun shift => mkApps_ctx (tInd ind0 uvs) shift ctx).

  Let prop := tSort (Universe.make'' (Level.lProp, false) nil).


  (** Building discriminators *)
  Definition build_discriminators :=
    let discr_id := discr_id ctor_id in
    let build_branch ctor_k '(((_ , ty),arity): (ident × term) × nat) :=
      let '(_, tys, _) := decompose_prod ty in
      let body := if eq_nat ctor_k ctor_index then qtrue else qfalse in
      (arity, up (build_const (List.skipn npars tys) body))
    in
    let brnchs := utils.mapi build_branch (ind_ctors oindbody) in
    let body := tCase (ind0, npars)
                      (tLambda (nNamed "z") (ind 1) qBool)
                      (tRel 0)
                      brnchs
    in
    it_mkLambda_or_LetIn ctx (tLambda (nNamed "z") (ind 0) body).

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
End Builders.

Definition gen_from_mind  generate (debug:bool) (mindname : qualid)
  : TemplateMonad unit :=
  mindbody <- tmQuoteInductive mindname ;;
  let oid_gen oind_index oindbody :=
    let ctor_gen ctor_idx ctor :=
      let '((ctor_id, ty), arity) := ctor in
      generate debug mindname mindbody oind_index oindbody ctor_idx ctor_id
    in
    monad_iteri ctor_gen (ind_ctors oindbody)
  in
  monad_iteri oid_gen (ind_bodies mindbody).


Definition gen_discriminators :=
  let generate (debug:bool) mindname mindbody oind_index oindbody ctor_idx ctor_id :=
    let discr_id := discr_id ctor_id in
    let discr_body := build_discriminators mindname mindbody oind_index oindbody ctor_idx ctor_id in
    t <- tmEval all discr_body ;;
    if debug then tmPrint t
    else
      tmMkDefinition discr_id t ;;
      tmMsg (arguments_string discr_id (ind_npars mindbody))
  in
  gen_from_mind generate.

Definition gen_discr_class :=
  let generate (debug:bool) mindname mindbody oind_index oindbody ctor_idx ctor_id :=
    discr_name <- tmEval all (discr_id ctor_id) ;;
    discr_kn <- get_const discr_name;;
    let discr_class_mid := build_discr_class mindname mindbody oind_index ctor_id discr_kn in
    let mindentry := mind_body_to_entry discr_class_mid in
    if debug then
      t <- tmEval all discr_class_mid ;;
      tmPrint t
    else
      tmMkInductive mindentry ;;
      (* class_id <- tmEval all (discr_class_id ctor_id) ;; *)
      (* tmExistingInstance class_id;; *)
      tmMsg ("Existing Class " ++ discr_class_id ctor_id ++ ".")
  in gen_from_mind generate.



(** Generation of the type of elimination for the discr class *)
Definition gen_discr_class_Etype :=
  let generate (debug:bool) mindname mindbody oind_index oindbody ctor_idx ctor_id :=
    discrclass_name <- tmEval all (discr_class_id ctor_id) ;;
    discrclass_ind <- get_inductive discrclass_name;;
    let discr_class_Etype :=
      build_discr_class_Etype mindname mindbody oind_index oindbody ctor_idx (* ctor_id *) (inductive_mind discrclass_ind)
    in
    if debug then t <- tmEval all discr_class_Etype ;; tmPrint t
    else
      tmMkDefinition (discr_class_Etype_id ctor_id) discr_class_Etype ;;
      tmMsg (arguments_string (discr_class_Etype_id ctor_id)
                              (ind_npars mindbody))
  in
  gen_from_mind generate.


Definition gen_discr_class_E :=
  let generate (debug:bool) mindname mindbody oind_index oindbody ctor_idx ctor_id :=
    discrclass_name <- tmEval all (discr_class_id ctor_id) ;;
    discrclass_ind <- get_inductive discrclass_name;;
    discrclass_Ety_name <- tmEval all (discr_class_Etype_id ctor_id) ;;
    discrclass_Ety_kn <- get_const discrclass_Ety_name;;
    let discr_class_E :=
      build_discr_class_E mindname mindbody oind_index oindbody ctor_idx (* ctor_id *) (inductive_mind discrclass_ind) discrclass_Ety_kn
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
  Set Primitive Projections.

  Inductive myBool := myTrue | myFalse.
  Run TemplateProgram (gen_discriminators false "myBool").
  Arguments ismyTrue _ : simpl nomatch.
  Arguments ismyFalse _ : simpl nomatch.

  Run TemplateProgram (gen_discr_class false "myBool").
  Existing Class is_myTrue.
  Existing Class is_myFalse.

  (** Bool *)
  Run TemplateProgram (gen_discriminators false "bool").
  Arguments istrue _ : simpl nomatch.
  Arguments isfalse _ : simpl nomatch.
  Class is_true0 (b:bool) := mkIs_true0 { istrue_pf0 : istrue b }.
  Run TemplateProgram (t <- tmQuoteInductive "is_true0";; tmPrint t).
  Run TemplateProgram (gen_discr_class false "bool").
  Existing Class is_true.
  Existing Class is_false.
  Run TemplateProgram (gen_discr_class_Etype false "bool").
  Arguments is_true_Etype _ : simpl nomatch.
  Arguments is_false_Etype _ : simpl nomatch.

  Run TemplateProgram (t <- tmAbout "is_true_Etype";; tmPrint t).
  Run TemplateProgram (s <- tmEval all (discr_class_Etype_id "true") ;; t <- get_const s;; tmPrint t).
  Run TemplateProgram (gen_discr_class_E false "bool").

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
