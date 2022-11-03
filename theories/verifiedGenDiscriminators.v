From Coq Require Import ssreflect ssrbool ssrfun.
From MetaCoq.PCUIC Require Import PCUICAst.


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


Module Constants.
  Module Template.
    From MetaCoq.Template Require Import config All.

    MetaCoq Quote Recursively Definition bool_full_prog := bool.
    Definition qBool := <% bool %>.
    Definition qtrue := <% true %>.
    Definition qfalse := <% false %>.
    
    MetaCoq Quote Recursively Definition selim_full_prog :=
     (fun x : is_true_s false => @sexfalso bool x).
    Definition qsUnit := <% sUnit %>.
    Definition qsEmpty := <% sEmpty %>.
    Definition qsexfalso := <% (@sexfalso) %>.
    Definition qis_true_s := <% is_true_s %>.
  End Template.
  
  From MetaCoq.PCUIC Require Import TemplateToPCUIC.

  (* From MetaCoq.Template Require Import config utils AstUtils Primitive EnvMap.
  From MetaCoq.Template Require TemplateProgram. *)
  From MetaCoq.PCUIC Require Import PCUICAst PCUICPrimitive PCUICCases PCUICProgram.
 

  Definition extract_gctx : PCUICProgram.pcuic_program -> global_env_ext :=
    fun p => (p.1.1.(PCUICProgram.trans_env_env), p.1.2).

  Definition boolΣ := Eval cbv in extract_gctx (trans_template_program Template.bool_full_prog).
  Definition sig := empty_trans_env ContextSet.empty Retroknowledge.empty.

  Definition get_some {A} (x : option A) : match x with | Some _ => A | None => unit end :=
    match x with | Some x => x | None => tt end.

  Definition get_ind (x : global_decl) : 
    match x return Type with | InductiveDecl _ => mutual_inductive_body | ConstantDecl _ => unit end :=
    match x with | InductiveDecl x => x | ConstantDecl _ => tt end.

  Definition boolDecl := Eval cbn in (get_some (List.hd_error boolΣ.1.(declarations))).
  Definition bool_ind := Eval cbn in mkInd boolDecl.1 0.
  Definition bool_mib := Eval cbn in get_ind boolDecl.2.
  Definition bool_oib := Eval cbn in get_some (List.hd_error bool_mib.(ind_bodies)).

  Lemma bool_declared : declared_inductive boolΣ.1 bool_ind bool_mib bool_oib.
  Proof. split; reflexivity. Qed.

  Definition qBool := Eval cbn in trans sig Template.qBool.
  Definition qtrue := Eval cbn in trans sig Template.qtrue.
  Definition qfalse := Eval cbn in trans sig Template.qfalse.
  
  Definition selimΣ := Eval cbv in extract_gctx (trans_template_program Template.selim_full_prog).
  (* Eval cbn in (List.map (fun x => x.1.2) selimΣ.1.(declarations)). *)

  Definition qsUnit := Eval cbn in trans sig Template.qsUnit.
  Definition qsEmpty := Eval cbn in trans sig Template.qsEmpty.
  Definition qsexfalso := Eval cbn in trans sig Template.qsexfalso.
  Definition qis_true_s := Eval cbn in trans sig Template.qis_true_s.

  From MetaCoq.PCUIC Require Import PCUICTyping.

  From MetaCoq.Template Require Export config.
  #[global]
  Instance cf : checker_flags := Build_checker_flags true true false true.

  Section WtyBoolean.
  Context (Σ : global_env_ext) 
          (declBool: declared_inductive Σ.1 bool_ind bool_mib bool_oib).

    Lemma qBoolWty : Σ ;;; [] |- qBool : tSort Universe.type0.
    Proof.
      eapply type_Cumul.
      - eapply type_Ind; [constructor|exact declBool|reflexivity].
      - econstructor. 1: constructor.
        intros ? <-%LevelExprSetFact.singleton_1; apply global_ext_levels_InSet.
      - apply cumul_Refl.
    Qed.  

    Lemma qtrueWty : Σ ;;; [] |- qtrue : qBool.
    Proof.
      econstructor. 2: exact qBoolWty.
      - eapply type_Construct. 1: constructor.
        1: split;[exact declBool| reflexivity].
        reflexivity.
      - apply cumul_Refl.
    Qed.  

    Lemma qfalseWty : Σ ;;; [] |- qfalse : qBool.
    Proof.
      econstructor. 2: exact qBoolWty.
      - eapply type_Construct. 1: constructor.
        1: split;[exact declBool| reflexivity].
        reflexivity.
      - apply cumul_Refl.
    Qed.  

  End WtyBoolean.

End Constants.

(* No idea which import are required... *)
From MetaCoq.PCUIC Require Import PCUICTyping PCUICArities PCUICInductives PCUICSpine
  PCUICWeakeningTyp PCUICUnivSubstitutionConv PCUICValidity PCUICGeneration
  PCUICAst PCUICPrimitive PCUICCases PCUICProgram TemplateToPCUIC
  PCUICSubstitution PCUICConversion PCUICInductiveInversion
  PCUICContextSubst PCUICOnFreeVars PCUICSR PCUICTactics.

From Genxs Require Import toMetacoq.

Section Builders.
  Context (ind0 : inductive)
    (mindbody : mutual_inductive_body)
    (oindbody : one_inductive_body)
    (ctor_index : nat)
    (ctor : constructor_body).

  Let npars := ind_npars mindbody.
  Let param_ctx := ind_params mindbody.
  Let indices_ctx := ind_indices oindbody.

  Context (uvs := abstract_instance (ind_universes mindbody)) (* or polymorphic_instance ? Are they the same ? *)
          (ctx := param_ctx ,,, indices_ctx)
          (ind := fun shift => mkApps (tInd ind0 uvs) 
                                      (to_extended_list_k ctx shift)).

  Definition principal := relNamed "principal"%bs.

  (** Building discriminators *)

  Definition build_discriminators :=
    let pparams := to_extended_list_k param_ctx (#|indices_ctx| + 1) in
    let build_branch ctor_k _ : term :=
      if Nat.eqb ctor_k ctor_index then Constants.qtrue else Constants.qfalse 
    in
    let brnchs := mapi build_branch (ind_ctors oindbody) in
    let body := make_case ind0 mindbody oindbody pparams uvs (tRel 0) Constants.qBool brnchs in
    it_mkLambda_or_LetIn ctx (tLambda principal (ind 0) body).

  Import Constants.

  Section WtyDiscriminator.
    Context (Σ : global_env) 
      (declBool: declared_inductive Σ bool_ind bool_mib bool_oib)
      (declInd : declared_inductive Σ ind0 mindbody oindbody)
      (Σext := (Σ,ind_universes mindbody))
      (wfΣ : wf_ext Σext).
      
    Definition discr_ty := it_mkProd_or_LetIn ctx (tProd principal (ind 0) qBool).


    Lemma indWty Γ : wf_local_rel Σext ([],,,ctx) Γ ->
      Σext;;; ([],,, ctx),,, Γ |- ind #|Γ| : tSort (ind_sort oindbody).
    Proof. 
      have wfΣ' := (wfΣ : wf Σ).
      pose proof (wfΣwk := declared_inductive_wf_ext_wk _ _ _ wfΣ (proj1 declInd)).

      move: (declInd)=> /(PCUICWeakeningEnvTyp.on_declared_inductive (Σ:=Σext.1)) [on_ind on_body].
      move: (onArity on_body) => [lind].
      rewrite (PCUICGlobalMaps.ind_arity_eq on_body).
      move=> /PCUICSpine.type_it_mkProd_or_LetIn_inv [uparams [? [slparams + _ _]]].
      move=> /PCUICSpine.type_it_mkProd_or_LetIn_inv [uindxs [? [slindxs + _ _]]].
      move=> indsortTyp.

      move: (typed_subst_abstract_instance _ _ _ _ wfΣwk indsortTyp) => /= <-.
      rewrite -/uvs /ind.
      move=> wfΓrel.
      apply: isType_mkApps_Ind.
      1: exact declInd.
      1: apply: consistent_instance_ext_abstract_instance=> //.

      assert (wfctx : wf_local Σext ([],,, ctx)).
      {
        rewrite /ctx app_context_assoc.
        apply: (typing_wf_local indsortTyp).
      }
      have wfΓ : wf_local Σext (([],,,ctx),,,Γ) by apply: All_local_rel_app.

      epose proof (s0 := spine_subst_to_extended_list_k wfctx).
      epose proof (s1 := spine_subst_weakening wfΓ s0).
      rewrite -[#|Γ|](Nat.add_0_r) (PCUICLiftSubst.lift_to_extended_list_k _ 0 #|Γ|).

      have -> : ctx@[uvs] = lift_context #|Γ| 0 (lift_context #|ctx| 0 ctx).
      2: apply: s1.

      rewrite app_context_nil_l in wfctx.
      rewrite (subst_instance_id _ ctx wfΣwk wfctx).
      rewrite -PCUICClosed.lift_context_add.
      symmetry; apply: PCUICWeakeningConv.closed_ctx_lift.
      by apply: PCUICClosedTyp.closed_wf_local.
    Qed.  


    Lemma ind0Wty : Σext;;; [],,, ctx |- ind 0 : tSort (ind_sort oindbody).
    Proof. by apply: (indWty []). Qed.


    Lemma discr_tyWty : ∑ l, Σext ;;; [] |- discr_ty : tSort l.
    Proof.
      have wfΣ' := (wfΣ : wf Σ).
      move: (declInd)=> /(PCUICWeakeningEnvTyp.on_declared_inductive (Σ:=Σext.1)) [_ on_body].
      move: (onArity on_body) => [lind].
      rewrite (PCUICGlobalMaps.ind_arity_eq on_body).
      move=> /PCUICSpine.type_it_mkProd_or_LetIn_inv [uparams [? [? + _ _]]].
      move=> /PCUICSpine.type_it_mkProd_or_LetIn_inv [uindxs [_ [? _ _ _]]].
      pose (l := sort_of_products (uindxs ++ uparams) (Universe.sort_of_product (ind_sort oindbody) Universe.type0)).
      exists l.
      rewrite /discr_ty.
      apply type_it_mkProd_or_LetIn_sorts.
      1: by apply: sorts_local_ctx_app.
      econstructor; first exact ind0Wty.
      set (Γ := _ ,, _); apply: (weakening0 Γ (qBoolWty _ _))=> //. 
      apply: wf_local_ass; [apply: (typing_wf_local ind0Wty)| apply: isType_intro; exact ind0Wty].
    Qed.  

    Context (canElimToType : is_allowed_elimination (global_ext_constraints Σext) (ind_kelim oindbody) Universe.type0)
            (isInductiveInd : isCoFinite (ind_finite mindbody) = false)
            (indRelevance : ind_relevance oindbody = Relevant).


    Lemma discriminatorWty : Σext ;;; [] |- build_discriminators : discr_ty.
    Proof.
      have wfΣ' := (wfΣ : wf Σ).
      pose proof (wfΣwk := declared_inductive_wf_ext_wk _ _ _ wfΣ (proj1 declInd)).
      cbv delta [build_discriminators].
      match goal with
      | [|- context c [ _ ;;; _ |- ?t : _ ]] => let_to_set t (* ltac:(fun _ => idtac) *)
      end.
      cbv zeta; rewrite -/brnchs.
      apply: PCUICGeneration.type_it_mkLambda_or_LetIn.
      apply: type_Lambda; first exact ind0Wty.
      set (Γ := _ ,, _).
      have ΣΓ : wf_local Σext Γ by 
        (apply: wf_local_ass; [apply: (typing_wf_local ind0Wty)| apply: isType_intro; exact ind0Wty]).

      set qBool' := lift0 (S #|ind_indices oindbody|) qBool.
      have qBooleq : qBool = qBool' by reflexivity.
      rewrite qBooleq.

      have ?: #|ind_ctors oindbody| = #|brnchs| by rewrite /brnchs mapi_length.

      apply: type_Case_simple_subst_helper=> //.
      + rewrite /pparams PCUICAstUtils.to_extended_list_k_length /param_ctx.
        symmetry; apply: PCUICGlobalEnv.declared_minductive_ind_npars; exact: proj1 declInd.
      + econstructor; first apply: type_Rel=> //.
        2:{
          rewrite /decl_type /= /ind PCUICLiftSubst.lift_mkApps /=.
          rewrite -PCUICLiftSubst.lift_to_extended_list_k/=.
          rewrite /ctx PCUICContexts.to_extended_list_k_app /pparams.
          reflexivity.
        }
        move: (indWty [vass principal (ind 0)] (All_local_app_rel (Γ:=[],,,ctx) (Γ' := [_]) ΣΓ).2).
        change (?x ,,, [?y]) with (x ,, y).
        rewrite -/Γ /ind /= /ctx /pparams.
        rewrite PCUICContexts.to_extended_list_k_app. apply.
      + apply: (weakening0 _ (qBoolWty _ _))=> //.
      + assumption.
      + apply: forall_nth_error_All2i=> // i cb t incstor.
        rewrite {1}/brnchs nth_error_mapi incstor=> [=] <-.
        move=> ????; unshelve econstructor.
        1: exact qBool.
        3: eassumption.
        2: reflexivity.
        rewrite [bbody _]/= /build_branch.
        case: (i =? ctor_index).
        apply: (weakening0 _ (qtrueWty _ _))=> //.
        apply: (weakening0 _ (qfalseWty _ _))=> //.
    Qed.

  End WtyDiscriminator.


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


  (* TODO : move and prove lemmas *)
  Definition fold_right_i [A B] (f : nat -> B -> A -> A) (a0 : A) :=
    (fix fold_right_i n (l : list B) : A :=
    match l with
    | []%list => a0
    | (hd :: tl)%list => f n hd (fold_right_i (S n) tl)
    end) 0.


  (** Building projectors *)
  (* For constructor c_k :
    param_ctx ,,, indices_ctx ,, principal |- bodies

    bodies_i : match tRel 0 as principal' in ind0 indices_ctx'
                          return Rclause_i with
             | c_k (args) => ok_branch_i
             | _ => exfalso_branch
             end

   param_ctx ,,, args_>i |- arg_i_type

   param_ctx ,,, indices_ctx ,, principal ,,,
    firstn (i-1) (lift0 (S #|indices_ctx|) cstr_args) ,,,
    indices_ctx' ,, principal' |-
   is_true_s (is_c_k param_ctx indices_ctx' principal') ->
   lift (S #|indices_ctx'|) #|param_ctx ,,, indices_ctx ,, principal| (lift0 (S #|indices_ctx|) (List.nth i cstr_arg))

   ok_branch_i := fun _ : sUnit => tRel i
   exfalso_branch := sexfalso (arg_i_type [bodies_>i] (* weakening *))

   *)
  Definition build_projector_subst (discriminator : term)
    : list term :=
    let principal := relNamed "principal"%bs in
    let ctx1 := ctx ,, (vass principal (ind 0)) in

    let discr_arg := irrelNamed "discr"%bs in
    let discr_ty shift :=
      let discrBool := mkApps discriminator (to_extended_list_k ctx1 shift) in
      tApp Constants.qis_true_s discrBool
    in

    let projector_body_for_arg (arg_dbi : nat) (arg : context_decl) (subprojs : list term) : term :=
      let pparams := to_extended_list_k param_ctx (#|indices_ctx| + 1 + #|subprojs|) in
      let rettyp :=
        let discr_ty :=
          let params := to_extended_list_k param_ctx (#|indices_ctx| + 1 + #|subprojs| + #|indices_ctx| + 1) in
          let indices := to_extended_list_k indices_ctx 1 in
          let discr_args := (params ++ indices ++ [tRel 0])%list in
          tApp Constants.qis_true_s (mkApps discriminator discr_args)
        in
        let ret_ty := 
          lift0 (#|indices_ctx| + 1) (lift (#|indices_ctx| + 1) #|subprojs| arg.(decl_type))
        in
        tProd discr_arg discr_ty ret_ty
      in
      let build_branch ctor_k (cb : constructor_body) : term :=
        let correct_branch := tLambda anonIrrel Constants.qsUnit (tRel (S arg_dbi)) in
        let exfalso_branch :=
          let params_shift := S (#|cb.(cstr_args)| + #|subprojs| + S (#|indices_ctx|)) in
          let cstr_term := 
            mkApps (tConstruct ind0 ctor_k uvs) 
                   (to_extended_list_k param_ctx params_shift
                   ++ to_extended_list_k cb.(cstr_args) 1)
          in
          let ret_ty := 
            lift0 (S #|cb.(cstr_args)|) (lift (#|indices_ctx| + 1) #|subprojs| arg.(decl_type)) 
          in
          tLambda discr_arg Constants.qsEmpty (mkApps Constants.qsexfalso [ret_ty ; tRel 0]%list)
        in
        if Nat.eqb ctor_k ctor_index then correct_branch else exfalso_branch
      in
      let brnchs := mapi build_branch (ind_ctors oindbody) in
      make_case ind0 mindbody oindbody pparams uvs (tRel 0) rettyp brnchs
    in

    (* Retrieve the context of arguments from the closed type
       of current constructor *)
    let arg_ctx :=
      let ctor_ty := type_of_constructor mindbody ctor (ind0, 0 (*unused*)) uvs in
      let ctx_with_params := (PCUICAstUtils.decompose_prod_assum nil%list ctor_ty).1 in
      List.firstn #|cstr_args ctor| ctx_with_params
    in

    let fold_fun argdbi argdecl subprojs :=
      match argdecl.(decl_body) with
      | None => projector_body_for_arg argdbi argdecl subprojs 
      | Some b => b 
      end :: subprojs
    in

    fold_right_i fold_fun nil%list arg_ctx.


End Builders.

     
        
