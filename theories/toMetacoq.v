From Coq Require Import ssreflect ssrbool ssrfun.

From MetaCoq.Template Require Import config.

From MetaCoq.PCUIC Require Import PCUICTyping PCUICArities PCUICInductives PCUICSpine
  PCUICWeakeningTyp PCUICUnivSubstitutionConv PCUICValidity PCUICGeneration
  PCUICAst PCUICPrimitive PCUICCases PCUICProgram TemplateToPCUIC
  PCUICSubstitution PCUICConversion PCUICInductiveInversion
  PCUICContextSubst PCUICOnFreeVars PCUICSR PCUICTactics.

From Equations Require Import Equations.


Definition make_case_pred (ind : inductive) (mib : mutual_inductive_body) (oib : one_inductive_body) (pparams : list term) (puinst : Instance.t) (rettyp : term) : predicate term :=
  (* let pnames := {| binder_name := nNamed (ind_name oib); binder_relevance := oib.(ind_relevance) |} :: forget_types oib.(ind_indices) in *)
  {| pparams := pparams; puinst := puinst
  ;  pcontext := ind_predicate_context ind mib oib
   (* pre_case_predicate_context_gen ind mib oib pparams puinst *)
  ;  preturn := rettyp |}.

Definition make_br ind mib (* pparams puinst *) cdecl t :=
  (* let bnames := forget_types cdecl.(cstr_args) in *)
  {| bcontext := cstr_branch_context ind mib cdecl ;
  (* case_branch_context_gen ind mib pparams puinst bnames cdecl; *)
   bbody := t |}.

Definition make_case (ind : inductive) (mib : mutual_inductive_body) (oib : one_inductive_body) (pparams : list term) (puinst : Instance.t) (discr : term) (rettyp : term) (brs : list term) :=
  let ci := {| ci_ind := ind; ci_npar := mib.(ind_npars); ci_relevance := oib.(ind_relevance) |} in
  let p := make_case_pred ind mib oib pparams puinst rettyp in
  let brs := map2 (make_br ind mib (*pparams puinst *)) oib.(ind_ctors) brs in
  tCase ci p discr brs.


(* Sets the definition of let-bindings in the hypotheses context *)
(* Problem with folding of terms that mention another term being set *)
Ltac let_to_set t :=
  let h := eval cbv beta in t in
  match h with
  | let x := ?u in @?v x => set x := u ; let_to_set (v x)
  | _ => idtac
  end.

Lemma map2_map_l {A B C D} (f : A -> B) (g : B -> C -> D) (l : list A) (l' : list C) :
  map2 g (List.map f l) l' =
  map2 (fun x y => g (f x) y) l l'.
Proof.
  induction l in l' |- *; destruct l'; simpl; auto.
  * cbn. now f_equal.
Qed.

Lemma map2_diag {A B} (f : A -> A -> B) (l : list A) :
  map2 f l l = map (fun x => f x x) l.
Proof.
  elim: l=> [//|? ? /= -> //].
Qed. 


Lemma map2_snd {A B} (l : list A) (l' : list B) : 
  map2 (fun x y => x) l l' = firstn #|l'| l.
Proof.
  elim: l l'=> [|x xs ih] [|y ys] //=; congruence.
Qed.

Lemma All2_map2_right_inv {A B C} R (g : A -> B -> C) l l' : #|l| = #|l'| ->  All2 R l (map2 g l l') ->  All2 (fun x y => R x (g x y)) l l'.
Proof. 
  elim: l l'=> [|x xs ih] [|y ys] //= [=] eq z; try depelim z ; try constructor=> //.
  by apply: ih.
Qed.

Lemma All2_map2_right {A B C} R (g : A -> B -> C) l l' : All2 (fun x y => R x (g x y)) l l' -> All2 R l (map2 g l l').
Proof.
  elim: l l'=> [|x xs ih] [|y ys] //= z; try constructor ; try depelim z=>//.
  by apply: ih.
Qed.

Lemma All2i_map2_right {A B C} k R (g : A -> B -> C) l l' : All2i (fun i x y => R i x (g x y)) k l l' -> All2i R k l (map2 g l l').
Proof.
  elim: l l' k=> [|x xs ih] [|y ys] //= k z; try constructor ; try depelim z=>//.
  by apply: ih.
Qed.

Lemma All2i_Alli_mix_left {A B k Q R} {l : list A} {l' : list B} 
  : Alli Q k l -> All2i R k l l' -> All2i (fun i x y => Q i x * R i x y) k l l'.
Proof.
  move=> + h; elim: h=> [n|n x y xs ys r rs ih] q; depelim q; constructor=> //.
  by apply: ih.
Qed.


Lemma forget_types_inst_case_context pparams puinst Γ:
  forget_types (inst_case_context pparams puinst Γ) = forget_types Γ.
Proof. 
  rewrite /inst_case_context /subst_context forget_types_fold_context_k forget_types_subst_instance //.
Qed.   

Lemma sorts_local_ctx_app P Σ Γ Δ1 Δ2 us1 us2 :
  sorts_local_ctx P Σ Γ Δ1 us1 ->
  sorts_local_ctx P Σ (Γ ,,, Δ1) Δ2 us2 ->
  sorts_local_ctx P Σ Γ (Δ1 ,,, Δ2) (us2 ++ us1).
Proof.
  elim: Δ2 us2 Δ1 us1=> [|+ Δ2 ih].
  1: move=> [|u us2] //=.
  move=> [? [bdy|] ty] us2 Δ1 us1 /=.
  - rewrite app_context_assoc=> ? [? [??]] ; split=> //.
    by apply: ih.
  - case: us2=> [|u us2] // ? [??] /=.
    rewrite app_context_assoc; split=> //.
    by apply: ih.
Qed.  

Lemma weakening0 {cf : checker_flags} Σ Γ t T :
  wf Σ.1 -> wf_local Σ Γ -> 
  Σ ;;; [] |- t : T -> Σ ;;; Γ |- lift0 #|Γ| t : lift0 #|Γ| T.
Proof.
  rewrite -{1 2}[Γ]app_context_nil_l; apply: weakening.
Qed. 

Arguments weakening0 {_ _} _ {_ _ _ _} _.

Lemma closed_ctx_app Γ Δ : 
  closed_ctx (Γ ,,, Δ) ->
  closedn_ctx #|Γ| Δ.
Proof.
  rewrite PCUICClosed.test_context_k_app=> /andP [//].
Qed.


(* Unused *)
Lemma weakening_type_local_ctx {cf:checker_flags} Σ Γ Δ Δ' ctxs : 
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Δ) ->
  type_local_ctx (lift_typing typing) Σ Γ Δ' ctxs ->
  type_local_ctx (lift_typing typing) Σ (Γ ,,, Δ) (lift_context #|Δ| 0 Δ') ctxs.
Proof.
  induction Δ'; simpl; auto.
  destruct a as [na [b|] ty]; simpl; intuition auto.
  + simpl; rewrite PCUICLiftSubst.lift_context_snoc /= Nat.add_0_r;
    repeat split; tas.  
    - apply infer_typing_sort_impl with id a0; intros Hs.
      now eapply weakening_typing in Hs.
    - now eapply weakening_typing in b1.
  + rewrite PCUICLiftSubst.lift_context_snoc /= Nat.add_0_r.
      intuition auto.
      eapply weakening_typing in b; eauto.
Qed.

Lemma wf_local_expand_lets0 {cf : checker_flags} {Σ : global_env_ext} :
  wf Σ ->
  forall Δ Γ : context,
  wf_local Σ (Δ,,, Γ) ->
  wf_local Σ (smash_context [] Δ,,, expand_lets_ctx Δ Γ).
Proof.
  move=> ? Δ ?.
  rewrite -{1}[Δ]app_context_nil_l -{1}[smash_context _ _]app_context_nil_l.
  apply: wf_local_expand_lets.  
Qed.

Lemma map_lift_map_lift k0 k1 n0 n1 l :
 k1 <= n1 + n0 -> n1 <= k1 -> map (lift k0 k1) (map (lift n0 n1) l) = map (lift (k0 + n0) n1) l.
Proof.
  move=> *; rewrite !map_map; apply: map_ext=> ?; by apply: PCUICLiftSubst.simpl_lift.
Qed.



Section WithCheckerFlags.
  Context `{cf : checker_flags}.

  Lemma AritiesToGeneration_typing_spine Σ Δ T s U :
    PCUICArities.typing_spine Σ Δ T s U -> 
    PCUICGeneration.typing_spine Σ Δ T s U.
  Proof using cf.
    move=> z; depind z; econstructor=> //; try eassumption.
    all: by apply: PCUICConversion.cumulAlgo_cumulSpec.
  Qed.

  Lemma spine_subst_vass Σ Γ s t σ Δ na A :
    wf Σ.1 ->
    spine_subst Σ Γ s σ Δ ->
    isType Σ (Γ ,,, Δ) A ->
    Σ ;;; Γ |- t : subst0 σ A ->
    spine_subst Σ Γ (s ++ [t]) (t :: σ) (Δ ,, vass na A).
  Proof using cf. 
    move=> wfΣ sss Atyp ttyp; move: (sss)=> [????].
    change (?x ,, ?y) with (x ,,, [ y ]).
    apply: spine_subst_app=> //=.
    + apply: PCUICContextSubst.context_subst_length2; eassumption.
    + apply: localenv_cons_abs=> //.
    + rewrite /skipn /subst_context /fold_context_k /= /map_decl /=.
      constructor=> //=.
      * apply: localenv_cons_abs=> //.
        apply: isType_subst; eassumption.
      * apply: (PCUICContextSubst.context_subst_ass [] [] [] na _ t); constructor.
      * econstructor; first constructor.
        by rewrite PCUICLiftSubst.subst_empty.
  Qed.  

  Lemma spine_subst_vass' Σ Γ s t σ Δ na A :
    wf Σ.1 ->
    spine_subst Σ Γ s σ Δ ->
    wf_local Σ (Γ ,,, Δ ,, vass na A) ->
    (* Σ ;;; Γ ,,, Δ |- A *)
    (spine_subst Σ Γ s σ Δ ->
      (* isType Σ (Γ ,,, Δ) A -> *)
      isType Σ Γ (subst0 σ A) ->
      Σ ;;; Γ |- t : subst0 σ A) ->
    spine_subst Σ Γ (s ++ [t]) (t :: σ) (Δ ,, vass na A).
  Proof using cf. 
    move=> wfΣ sss Atyp /(_ sss) ttyp; apply: spine_subst_vass=> //.
    2: apply: ttyp; apply: isType_subst; first (apply: inst_subslet; eassumption).
    all: exact (wf_local_nth_isType (n := 0) Atyp eq_refl).
  Qed.  

  Lemma isType_lift {Σ : global_env_ext} {n Γ Δ ty} 
    (isdecl : n <= #|Γ|):
    wf Σ -> wf_local Σ (Γ ,,, lift_context n 0 Δ) ->
    isType Σ (skipn n Γ ,,, Δ) ty ->
    isType Σ (Γ,,, lift_context n 0 Δ) (lift n #|Δ| ty).
  Proof using cf.
    intros wfΣ wfΓ wfty. rewrite <- (firstn_skipn n Γ) in wfΓ |- *.
    assert (n = #|firstn n Γ|).
    { rewrite firstn_length_le; auto with arith. }
    apply infer_typing_sort_impl with id wfty; intros Hs.
    rewrite {3 4}H.
    eapply (weakening_typing (Γ := skipn n Γ) (Γ' := Δ) (Γ'' := firstn n Γ) (T := tSort _)); 
      eauto with wf.
  Qed.


End WithCheckerFlags.



Section CaseDefinitions.
  Context
    `{cf : checker_flags}
    (ind : inductive) 
    (mib : mutual_inductive_body) 
    (oib : one_inductive_body) 
    (pparams : list term) 
    (puinst : Instance.t).
  
  Definition inddecl_name := 
    {| binder_name := nNamed (ind_name oib) ; binder_relevance := ind_relevance oib |}.

  Definition indpred_ctx :=
    let indxctx := subst_context (List.rev pparams) 0 (expand_lets_ctx mib.(ind_params) oib.(ind_indices))@[puinst] in
    let indty := mkApps (tInd ind puinst) (map (lift0 #|ind_indices oib|) pparams ++ to_extended_list oib.(ind_indices)) in
    indxctx ,, vass (inddecl_name) indty.
  
  Lemma pre_case_predicate_context_gen_indpred_ctx Σ Γ :
    spine_subst Σ Γ pparams (List.rev pparams) (smash_context [] (ind_params mib)@[puinst]) ->
    consistent_instance_ext Σ (ind_universes mib) puinst ->
    pre_case_predicate_context_gen ind mib oib pparams puinst = indpred_ctx.
  Proof using cf.
    move=> pparamssubst ?.
    rewrite /pre_case_predicate_context_gen /ind_predicate_context /indpred_ctx /inst_case_context.
    rewrite PCUICUnivSubst.subst_instance_cons subst_context_snoc. f_equal.
    rewrite /vass /inddecl_name subst_instance_length expand_lets_ctx_length.
    rewrite {1}/subst_instance /= /subst_decl /map_decl /=; f_equal.
    rewrite PCUICUnivSubst.subst_instance_mkApps PCUICLiftSubst.subst_mkApps.
    f_equal => /=; first (f_equal; apply: subst_instance_id_mdecl; eassumption).
    rewrite PCUICUnivSubst.map_subst_instance_to_extended_list_k.
    rewrite PCUICContexts.to_extended_list_k_app.
    rewrite map_app; f_equal.
    - rewrite expand_lets_ctx_length Nat.add_0_r. 
      rewrite -{2}[#|_|]Nat.add_0_r PCUICLiftSubst.lift_to_extended_list_k map_map.
      erewrite map_ext; last (move=> ?; rewrite subst_lift_subst; reflexivity).
      rewrite -map_map; f_equal.
      rewrite -(PCUICLiftSubst.map_subst_instance_to_extended_list_k puinst) subst_instance_smash.
      apply: spine_subst_subst_to_extended_list_k; eassumption.
    - rewrite -PCUICSubstitution.to_extended_list_k_map_subst ?expand_lets_ctx_length //.
      rewrite to_extended_list_k_expand_lets //.
  Qed.



End CaseDefinitions.



Section WithCheckerFlags.
  Context `{cf: checker_flags}.

  Lemma isType_it_mkProd_or_LetIn {Σ} {wfΣ : wf Σ.1} {Γ Γ' us t} : 
    sorts_local_ctx (lift_typing typing) Σ Γ Γ' us ->
    isType Σ (Γ ,,, Γ') t ->
    isType Σ Γ (it_mkProd_or_LetIn Γ' t).
  Proof using cf.
    move=> equs [s ttyp]; exists (sort_of_products us s).
    apply: type_it_mkProd_or_LetIn_sorts=> //.
  Qed.  

  Lemma wf_local_validity Σ Γ Δ : 
    wf Σ.1 ->
    wf_local Σ (Γ ,,, Δ) -> 
    ∑ us, sorts_local_ctx (lift_typing typing) Σ Γ Δ us.
  Proof using cf.
    move=> wfΣ wfΓΔ.
    apply: validity_wf_local.
    enough (h : wf_local_rel Σ Γ Δ).
    apply: All_local_env_impl; first exact h.
    1: move=> ?? [?|] //= ?; split=> //; apply: validity; eassumption.
    by apply: (wf_local_app_inv _).2.
  Qed.

  Lemma inductive_ind_ind_bodies_length
    Σ ind mib oib
    (wfΣ : wf Σ)
    (inddecl: declared_inductive Σ ind mib oib) :
    inductive_ind ind < #|ind_bodies mib|.
  Proof using cf.
    move: (declared_inductive_lookup inddecl).
    rewrite /lookup_inductive (PCUICLookup.declared_minductive_lookup (PCUICGlobalEnv.declared_inductive_minductive inddecl)).
    remember (nth_error _ _) as o eqn:eo; symmetry in eo.
    move: o eo=> [io|] // /nth_error_Some_length //.
  Qed.

  Lemma declared_ind_declared_constructors {Σ ind mib oib} :
    declared_inductive Σ ind mib oib ->
    Alli (fun i => declared_constructor Σ (ind, i) mib oib) 0 (ind_ctors oib).
  Proof using.
    move=> inddecl.
    apply: forall_nth_error_Alli=> /= i x eq.
    apply: PCUICLookup.lookup_constructor_declared=> /=.
    rewrite /PCUICLookup.lookup_constructor (PCUICLookup.declared_inductive_lookup inddecl) eq //.
  Qed.

End WithCheckerFlags.

(**************************)
(* Section  mk_ctx_subst  *)
(**************************)

Lemma context_subst_subst_expand_lets inst s Δ t k :
  context_subst Δ inst s ->
  subst s k t = subst (List.rev inst) k (expand_lets_k Δ k t).
Proof.
  move=> /[dup] H /context_subst_subst_extended_subst ->.
  apply: PCUICSigmaCalculus.map_subst_expand_lets_k.
  rewrite List.rev_length.
  apply: context_subst_assumptions_length; eassumption.
Qed.


Lemma make_context_subst_context_assumptions Δ args s :
  context_assumptions Δ = #|args| -> 
  ∑ s', make_context_subst Δ args s = Some s'.
Proof.
  elim: Δ args s=> [|[?[?|]?] Δ ih].
  + move=> []//=;eexists; reflexivity.
  + move=> /= ??; apply:ih.
  + move=> /= [//|hd tl /=] s [=]. apply: ih.
Qed.

Definition mk_ctx_subst Δ args := Option.default [] (make_context_subst (List.rev Δ) args []).

Lemma mk_ctx_subst_spec {Δ args} : 
  context_assumptions Δ = #|args| -> 
  context_subst Δ args (mk_ctx_subst Δ args). 
Proof.
  rewrite /mk_ctx_subst -context_assumptions_rev.
  move=> /(make_context_subst_context_assumptions _ _ []) [? /[dup] ? ->] /=.
  rewrite -[Δ]rev_involutive.
  by apply: make_context_subst_spec.
Qed. 


Lemma mk_ctx_subst_spec' `{cf : checker_flags} {Σ Γ Δ args} (c : ctx_inst Σ Γ args (List.rev Δ)) :
  mk_ctx_subst Δ args = ctx_inst_sub c.
Proof.
  apply: context_subst_fun.
  - apply: mk_ctx_subst_spec; by rewrite (ctx_inst_length c) context_assumptions_rev.
  - move: (ctx_inst_sub_spec c)=> /make_context_subst_spec.
    rewrite {1}rev_involutive //.
Qed.

Lemma mk_ctx_subst_length Δ l : 
  context_assumptions Δ = #|l| -> #|mk_ctx_subst Δ l| = #|Δ|.
Proof.
  move=> /mk_ctx_subst_spec /PCUICContextSubst.context_subst_length //.
Qed.

(****************************)
(* Lemmas on Case branches  *)
(****************************)

Definition case_branch_context ind mib p (b : branch term) cdecl :=
  case_branch_context_gen ind mib (pparams p) (puinst p) (forget_types (bcontext b)) cdecl.

Definition instantiate_cstr_indices ind mib params puinst cdecl :=
  let upars := (ind_params mib)@[puinst] in
  let arglen := #|cstr_args cdecl| in
  let inds := inds (inductive_mind ind) puinst (ind_bodies mib) in
  map (subst (List.rev params) arglen)
    (map (expand_lets_k upars arglen)
      (map (subst inds (#|ind_params mib| + arglen))
        (map (subst_instance puinst) (cstr_indices cdecl)))).


Definition case_branch_type_only_gen ind mib params puinst ptm i cdecl :=
  let cstr := tConstruct ind i puinst in
  let args := to_extended_list (cstr_args cdecl) in
  let cstrapp := mkApps cstr (map (lift0 #|cstr_args cdecl|) params ++ args) in
  let indices := instantiate_cstr_indices ind mib params puinst cdecl in
  mkApps (lift0 #|cstr_args cdecl| ptm) (indices ++ [cstrapp]).

Definition case_branch_type_only ind mib p ptm i cdecl :=
  case_branch_type_only_gen ind mib (pparams p) (puinst p) ptm i cdecl.

Lemma case_branch_type_gen_split ind mib oib params puinst ptm names i cdecl :
  case_branch_type_gen ind mib oib params puinst names ptm i cdecl =
  (case_branch_context_gen ind mib params puinst names cdecl,
  case_branch_type_only_gen ind mib params puinst ptm i cdecl).
Proof. reflexivity. Qed.

Lemma case_branch_type_split ind mib oib p b ptm i cdecl :
  case_branch_type ind mib oib p b ptm i cdecl =
  (case_branch_context ind mib p b cdecl, case_branch_type_only ind mib p ptm i cdecl).
Proof. reflexivity. Qed.

Definition case_branch_type_subst_gen ind mib params puinst predctx rettyp i cdecl :=
  let cstr := tConstruct ind i puinst in
  let args := to_extended_list (cstr_args cdecl) in
  let cstrapp := mkApps cstr (map (lift0 #|cstr_args cdecl|) params ++ args) in
  let indices := instantiate_cstr_indices ind mib params puinst cdecl in
  let ctx := lift_context #|cstr_args cdecl| 0 predctx in
  let s := mk_ctx_subst ctx (indices ++ [cstrapp]) in
  subst0 s (lift #|cstr_args cdecl| #|predctx| rettyp).

Definition case_branch_type_subst ind mib p predctx rettyp i cdecl :=
  case_branch_type_subst_gen ind mib (pparams p) (puinst p) predctx rettyp i cdecl.


(****************************)
(* Random Lemmas            *)
(****************************)

Inductive snoc_view {A : Type} : list A -> Type :=
| snoc_view_nil : snoc_view nil
| snoc_view_snoc l x : snoc_view (l ++ [x]).

Lemma snocP {A} (l : list A) : snoc_view l.
Proof.
  elim: l=> [|a l]; first constructor.
  case=> [|l' z];
  [exact: (snoc_view_snoc nil) | exact: (snoc_view_snoc (a :: l'))].
Qed.

Lemma expand_lets_k_nil k t : expand_lets_k [] k t = t.
Proof. by rewrite /expand_lets_k /= PCUICLiftSubst.subst_empty PCUICLiftSubst.lift0_id. Qed.

Lemma closedn_ctx_subst n Δ l s :
  context_subst Δ l s ->
  closedn_ctx n Δ ->
  forallb (closedn n) l ->
  forallb (closedn n) s.
Proof.
  move=> z; depind z=> //= /andP[/=? d].
  - rewrite forallb_app=> /andP[?] /andP[/= -> _] /=; by apply: IHz.
  - move=> ?.
    have ? : forallb (closedn n) s by apply: IHz.
    apply/andP; split=> //; apply: PCUICClosed.closedn_subst0=> //.
    move: d=> /andP /= []; rewrite (context_subst_length z) Nat.add_comm //.
Qed.



(****************************)
(* Iterated beta reduction  *)
(****************************)

Section IteratedBetaReduction.
  Context `{cf : checker_flags}.

  Lemma red_betas0 (Σ:global_env_ext) (wfΣ:wf Σ) Γ (Δ : context) l t t' : 
    #|l| = context_assumptions Δ ->
    closedn #|Γ,,, Δ| t ->
    closed_ctx (Γ ,,, Δ) ->
    PCUICReduction.red Σ.1 (Γ ,,, Δ) t t' ->
    PCUICReduction.red Σ.1 Γ (mkApps (it_mkLambda_or_LetIn Δ t) l) (subst0 (List.rev l) (expand_lets Δ t')).
  Proof using cf.
    elim: Δ t t' l=> [|[na[a|]ty] ls ih] /= t t' l.
    - move=> /length_nil -> * /=.
      rewrite PCUICLiftSubst.subst_empty PCUICSigmaCalculus.expand_lets_nil //.
    - move=> /ih ih0 clt clctx red. rewrite -/([_] ++ _).
      move: (clctx); rewrite Nat.add_0_r => /andP [clctx0 cld].
      rewrite expand_lets_app /= -/(expand_lets ls).
      refine (ih0 _ _ _ _ _)=> //.
      1: apply: PCUICClosed.closedn_mkLambda_or_LetIn=> //.
      rewrite /mkLambda_or_LetIn /= /expand_lets /expand_lets_k /=.
      rewrite PCUICLiftSubst.subst_empty PCUICLiftSubst.lift0_p.
      apply: PCUICReduction.red_step; first exact: PCUICReduction.red_zeta.
      rewrite PCUICLiftSubst.lift0_id.
      refine (substitution_untyped_red (Σ:=Σ) (Γ := Γ,,, ls) (Δ := [_]) (Γ':=nil) (M := t) (N:=t') _ _ _ red).
      + apply: untyped_subslet_def_tip=> //.
      + rewrite -PCUICClosedTyp.is_open_term_closed //.
      + rewrite on_free_vars_ctx_on_ctx_free_vars -PCUICClosedTyp.is_closed_ctx_closed //.
    - move: l=> /snocP [//|/=l x].
      rewrite app_length /= Nat.add_comm PCUICAstUtils.mkApps_app /= => [=] eq.
      move: (eq)=> /ih ih0 clt clctx red.
      move: (clctx); rewrite Nat.add_0_r => /andP [clctx0 cld].
      etransitivity.
      1:{
        apply: PCUICReduction.red_app; last reflexivity.
        apply: ih0.
        + apply: PCUICClosed.closedn_mkLambda_or_LetIn=> //.
        + assumption.
        + apply: red_abs_alt; first reflexivity; eassumption.
      }
      apply: PCUICReduction.red_step=> /=; first apply: PCUICReduction.red_beta.
      set t0 := (t in PCUICReduction.red _ _ t _).
      set t1 := (t in PCUICReduction.red _ _ _ t).
      have -> // : t0 = t1.
      rewrite {}/t0 {}/t1.
      rewrite /subst1 -PCUICLiftSubst.subst_app_simpl -(rev_app_distr _ [x]).
      f_equal; rewrite -/([_]++ls) expand_lets_app /= /expand_lets.  
      rewrite {-1}/expand_lets_k /=subst_rel0_lift_id //.
  Qed.

  Lemma red_betas (Σ:global_env_ext) (wfΣ:wf Σ) Γ (Δ : context) l t : 
    #|l| = context_assumptions Δ ->
    closedn #|Γ,,, Δ| t ->
    closed_ctx (Γ ,,, Δ) ->
    PCUICReduction.red Σ.1 Γ (mkApps (it_mkLambda_or_LetIn Δ t) l) (subst0 (mk_ctx_subst Δ l) t).
  Proof using cf.
    move=> eql.
    move: (mk_ctx_subst_spec (eq_sym eql))=> /(context_subst_subst_expand_lets _ _ _ t 0) ->.
    move=> *; apply: red_betas0=> //.
  Qed.  

  Lemma red_betas_typed (Σ:global_env_ext) (wfΣ:wf Σ) Γ (Δ : context) l t T : 
    #|l| = context_assumptions Δ ->
    Σ ;;; Γ ,,, Δ |- t : T ->
    PCUICReduction.red Σ.1 Γ (mkApps (it_mkLambda_or_LetIn Δ t) l) (subst0 (mk_ctx_subst Δ l) t).
  Proof using cf.
    move=> eql ty; apply: red_betas=> //.
    1: apply: PCUICClosedTyp.subject_closed; eassumption.
    apply: PCUICClosedTyp.closed_wf_local; apply: typing_wf_local; eassumption.
  Qed.  

  Lemma conv_betas (Σ : global_env_ext) (wfΣ: wf Σ) Γ Δ l t :
    closedn #|Γ ,,, Δ| t ->
    closed_ctx (Γ ,,, Δ) ->
    forallb (closedn #|Γ|) l ->
    context_assumptions Δ = #|l|  -> 
    Σ ;;; Γ |- mkApps (it_mkLambda_or_LetIn Δ t) l =s subst0 (mk_ctx_subst Δ l) t.
  Proof using cf.
    move=> tws /[dup] ?.
    rewrite PCUICClosed.closedn_ctx_app=> /andP[??] lcl eqlen.
    apply: cumulAlgo_cumulSpec.
    apply PCUICContextConversion.ws_cumul_pb_red.
    set (u:= mkApps _ _).
    set (w := subst0 _ _).
    exists w, w; split; last reflexivity.
    + constructor.
      * by rewrite  -PCUICClosedTyp.is_closed_ctx_closed.
      * rewrite /u -PCUICClosedTyp.is_open_term_closed PCUICClosed.closedn_mkApps lcl andb_true_r.
        apply: PCUICClosed.closedn_it_mkLambda_or_LetIn => //.
        by rewrite Nat.add_comm -app_length.
      * apply: red_betas=> //.
    + constructor.
      * by rewrite  -PCUICClosedTyp.is_closed_ctx_closed.
      * rewrite -PCUICClosedTyp.is_open_term_closed.
        move: (eqlen)=> /mk_ctx_subst_spec /closedn_ctx_subst h.
        apply: PCUICClosed.closedn_subst0; first by apply: h.
        rewrite mk_ctx_subst_length //.
        by rewrite Nat.add_comm -app_length.
      * reflexivity.
  Qed.


  Lemma conv_betas_typed (Σ : global_env_ext) (wfΣ: wf Σ) Γ Δ l t :
    isType Σ (Γ ,,, Δ) t ->
    ctx_inst Σ Γ l (List.rev Δ) -> 
    Σ ;;; Γ |- mkApps (it_mkLambda_or_LetIn Δ t) l =s subst0 (mk_ctx_subst Δ l) t.
  Proof using cf.
    move=> [ps tWty] instl. 
    pose proof (wfΓ := typing_wf_local tWty).
    pose proof (ss := ctx_inst_spine_subst wfΓ instl).
    pose proof (eqsubst := mk_ctx_subst_spec' instl).
    rewrite eqsubst.
    apply: cumulAlgo_cumulSpec.
    apply: PCUICWellScopedCumulativity.wt_cumul_pb_ws_cumul_pb.
    constructor.
    + have?: Σ ;;; Γ |- it_mkLambda_or_LetIn Δ t : it_mkProd_or_LetIn Δ (tSort ps)
      by apply: PCUICGeneration.type_it_mkLambda_or_LetIn; eassumption.
      exists ps; apply: PCUICSpine.type_mkApps; first eassumption.
      apply: typing_spine_it_mkProd_or_LetIn_close=> //=; first eassumption.
      apply: isType_it_mkProd_or_LetIn. 2: exact: validity tWty.
      exact (wf_local_validity _ _ _ _ wfΓ).π2.
    + apply:isType_subst; last (exists ps; eassumption).
      exact: inst_subslet ss.
    + apply: PCUICCumulativity.red_conv.
      rewrite -eqsubst. apply: red_betas_typed; last eassumption.
      rewrite (ctx_inst_length instl) context_assumptions_rev //.
  Qed.
      
End IteratedBetaReduction.

(************************************************)
(* Beta-reduction of match's motive in branches *)
(************************************************)

Section CaseBranchTypeBeta.
  Context `{cf : checker_flags}.
  Lemma pre_case_branch_context_gen_length ind mib params puinst cb :
    #|cstr_args cb| =  #|pre_case_branch_context_gen ind mib cb params puinst|.
  Proof using. rewrite /pre_case_branch_context_gen; by len. Qed.

  Lemma case_branch_context_unfold ind mib oib params puinst rettyp cb t :
    let p := make_case_pred ind mib oib params puinst rettyp in
    case_branch_context ind mib p (make_br ind mib cb t) cb =
    pre_case_branch_context_gen ind mib cb params puinst.
  Proof using.
    move=> p.
    rewrite /case_branch_context -/(PCUICCases.case_branch_context ind mib p _ cb).
    rewrite PCUICCasesContexts.inst_case_branch_context_eq //.
    reflexivity.
  Qed.
    

  Lemma case_branch_type_beta (Σ : global_env_ext) Γ ind mib params puinst predctx rettyp i cb :
    wf Σ ->
    closedn #|Γ ,,, predctx| rettyp ->
    closed_ctx (Γ ,,, predctx) ->
    let cstr_ctx := pre_case_branch_context_gen ind mib cb params puinst in 
    closed_ctx (Γ ,,, cstr_ctx) ->
    #|cstr_indices cb| + 1 = context_assumptions predctx ->
    PCUICReduction.red Σ.1 (Γ ,,, cstr_ctx)
      (case_branch_type_only_gen ind mib params puinst (it_mkLambda_or_LetIn predctx rettyp) i cb)
      (case_branch_type_subst_gen ind mib params puinst predctx rettyp i cb).
  Proof using cf.
    rewrite /case_branch_type_only_gen /case_branch_type_subst_gen.
    rewrite PCUICLiftSubst.lift_it_mkLambda_or_LetIn Nat.add_0_r.
    set cstr_ctx := (pre_case_branch_context_gen _ _ _ _ _).
    set Δ := (lift_context _ _ _).
    move=> wfΣ clret clpred clcstr indxseq.
    apply: red_betas; first (rewrite /instantiate_cstr_indices /Δ; by len).
    - have -> : #|Γ ,,, cstr_ctx ,,, Δ| = #|Γ ,,, predctx| + #|cstr_args cb|
      by rewrite /Δ !app_length /cstr_ctx /pre_case_branch_context_gen; len; lia.
      by apply: PCUICClosed.closedn_lift.
    - rewrite PCUICClosed.closedn_ctx_app clcstr /= /Δ app_length.
      have -> : #|cstr_args cb| = #|cstr_ctx| by rewrite /cstr_ctx /pre_case_branch_context_gen; len; lia.
      apply: PCUICClosed.closedn_ctx_lift.
      by apply: closed_ctx_app.
  Qed.
    

  Lemma case_branch_type_conv_beta (Σ : global_env_ext) Γ ind mib oib params puinst predctx rettyp i cb :
    wf Σ ->
    closedn #|Γ ,,, predctx| rettyp ->
    closed_ctx (Γ ,,, predctx) ->
    let cstr_ctx := pre_case_branch_context_gen ind mib cb params puinst in 
    closed_ctx (Γ ,,, cstr_ctx) ->
    forallb (closedn #|Γ|) params ->
    #|params| = ind_npars mib ->
    #|cstr_indices cb| + 1 = context_assumptions predctx ->
    declared_inductive Σ ind mib oib ->
    declared_constructor Σ (ind,i) mib oib cb ->
    Σ ;;; Γ ,,, cstr_ctx |-
      case_branch_type_only_gen ind mib params puinst (it_mkLambda_or_LetIn predctx rettyp) i cb =s
      case_branch_type_subst_gen ind mib params puinst predctx rettyp i cb.
  Proof using cf.
    rewrite /case_branch_type_only_gen /case_branch_type_subst_gen.
    rewrite PCUICLiftSubst.lift_it_mkLambda_or_LetIn Nat.add_0_r.
    set cstr_ctx := (pre_case_branch_context_gen _ _ _ _ _).
    set Δ := (lift_context _ _ _).
    move=> wfΣ clret clpred clcstr clpar pareq indxseq declind declctor.
    pose proof (declmind := proj1 declind).
    have eqcstrctx : #|cstr_args cb| = #|cstr_ctx| by rewrite /cstr_ctx /pre_case_branch_context_gen; len; lia.
    apply: conv_betas.
    - have -> : #|Γ ,,, cstr_ctx ,,, Δ| = #|Γ ,,, predctx| + #|cstr_args cb|
      by rewrite /Δ !app_length eqcstrctx; len; lia.
      by apply: PCUICClosed.closedn_lift.
    - rewrite PCUICClosed.closedn_ctx_app clcstr /= /Δ app_length eqcstrctx.
      apply: PCUICClosed.closedn_ctx_lift.
      by apply: closed_ctx_app.
    - rewrite forallb_app; apply/andP; split.
      + rewrite /instantiate_cstr_indices !forallb_map. 
        apply: All_forallb.
        apply: All_impl; first (apply: on_constructor_closed_indices; eassumption).
        move=> x /=.
        rewrite -PCUICClosedTyp.is_open_term_closed eqcstrctx !app_length=> clx.
        rewrite Nat.add_comm. 
        apply: PCUICClosed.closedn_subst; first by rewrite forallb_rev.
        set G := (_ @[_]). have -> : #|List.rev params| = context_assumptions G.
        1: by rewrite /G context_assumptions_subst_instance -(PCUICGlobalEnv.declared_minductive_ind_npars declmind) List.rev_length.
        rewrite PCUICClosed.closedn_expand_lets_eq {}/G.
        1:{
          rewrite PCUICClosed.closedn_subst_instance_context. 
          apply: (PCUICClosed.closedn_ctx_upwards 0); last lia.
          apply: PCUICClosedTyp.declared_inductive_closed_params declind.
        }
        rewrite subst_instance_length -Nat.add_assoc [X in _ + X]Nat.add_comm.
        apply: PCUICClosed.closedn_subst. 
        1:{
          apply: forallb_impl; last apply: PCUICClosed.closed_inds.
          move=> ???; apply: PCUICLiftSubst.closed_upwards; first eassumption; lia.
        }
        rewrite inds_length PCUICClosed.closedn_subst_instance.
        apply: PCUICLiftSubst.closed_upwards; first eassumption. 
        rewrite arities_context_length eqcstrctx; lia.
      + rewrite /= andb_true_r PCUICClosed.closedn_mkApps /= forallb_app ; apply/andP; split.
        * rewrite forallb_map. apply: forallb_impl; last eassumption.
          move=> x _ clx; rewrite app_length eqcstrctx Nat.add_comm.
          by apply: PCUICClosed.closedn_lift.
        * apply: forallb_impl; last apply: PCUICClosed.closedn_to_extended_list.
          move=> ? _ ?; apply: PCUICLiftSubst.closed_upwards; first eassumption. 
          rewrite app_length eqcstrctx ; lia.
    - rewrite /Δ /instantiate_cstr_indices; by len.
  Qed. 


  Lemma case_branch_type_beta_typed (Σ : global_env_ext) Γ ind mib params puinst predctx rettyp i cb :
    wf Σ ->
    isType Σ (Γ ,,, predctx) rettyp ->
    let cstr_ctx := pre_case_branch_context_gen ind mib cb params puinst in 
    wf_local Σ (Γ,,, cstr_ctx) ->
    #|cstr_indices cb| + 1 = context_assumptions predctx ->
    PCUICReduction.red Σ.1 (Γ ,,, cstr_ctx)
      (case_branch_type_only_gen ind mib params puinst (it_mkLambda_or_LetIn predctx rettyp) i cb)
      (case_branch_type_subst_gen ind mib params puinst predctx rettyp i cb).
  Proof using cf.
    rewrite /case_branch_type_only_gen /case_branch_type_subst_gen.
    rewrite PCUICLiftSubst.lift_it_mkLambda_or_LetIn Nat.add_0_r.
    set cstr_ctx := (pre_case_branch_context_gen _ _ _ _ _).
    set Δ := (lift_context _ _ _).
    move=> wfΣ [ps retWty] wfcstr_ctx ?.
    apply: red_betas_typed; first by rewrite /Δ /instantiate_cstr_indices; len; lia. 
    rewrite /Δ; have -> : #|cstr_args cb| = #|cstr_ctx| by rewrite /cstr_ctx /pre_case_branch_context_gen; len.
    apply: weakening_typing; eassumption.
  Qed.

End CaseBranchTypeBeta.


(*****************) 
(* Random lemmas *)
(*****************) 

Section RandomLemmas.
  Context `{cf: checker_flags}.
  
  Lemma closed_subslet {Σ} {wfΣ : wf Σ.1} {Γ s Δ} : subslet Σ Γ s Δ -> forallb (closedn #|Γ|) s.
  Proof using cf.
    move=> z; depind z=> //=; rewrite IHz andb_true_r;
    apply: PCUICClosedTyp.subject_closed; eassumption.
  Qed.


  Lemma closed_spine_subst {Σ} {wfΣ : wf Σ.1} {Γ inst s Δ} :
    spine_subst Σ Γ inst s Δ -> forallb (closedn #|Γ|) s.
  Proof using cf. move=> /inst_subslet; apply: closed_subslet.  Qed.

  Lemma closed_spine_subst_inst {Σ} {wfΣ : wf Σ.1} {Γ inst s Δ} :
    spine_subst Σ Γ inst s Δ -> forallb (closedn #|Γ|) inst.
  Proof using cf. 
    move=> /spine_subst_smash /closed_spine_subst; by rewrite forallb_rev.
  Qed.  

  Lemma cstr_indices_length {Σ} {wfΣ : wf Σ} {ind mib oib cb} :
    declared_constructor Σ ind mib oib cb ->
    #|cstr_indices cb| = context_assumptions (ind_indices oib).
  Proof using cf.
    move=> declctor.
    unshelve epose proof (X := PCUICWeakeningEnvTyp.on_declared_constructor declctor).
    move: X => [] _ [] ? [_] /on_cindices /ctx_inst_length.
    rewrite context_assumptions_rev context_assumptions_lift; apply.
  Qed.

  Lemma isType_mkApps_Ind_inv_spine
    (ind : inductive) 
    (mib : mutual_inductive_body) 
    (oib : one_inductive_body) 
    (pparams : list term) 
    (puinst : Instance.t) 
    (indices : list term)
    (Σ : global_env_ext) Γ :
    wf_ext Σ ->
    declared_inductive Σ ind mib oib ->
    #|pparams| = ind_npars mib ->
    isType Σ Γ (mkApps (tInd ind puinst) (pparams ++ indices)) ->
    ∑ s, spine_subst Σ Γ (pparams ++ indices) s (ind_params mib,,, ind_indices oib)@[puinst].
  Proof using cf.
    move=> wfΣ inddecl pparamslen discrtypok.
    have Γwf : wf_local Σ Γ by apply: (typing_wf_local discrtypok.π2).
    move: (inddecl)=> /(PCUICWeakeningEnvTyp.on_declared_inductive (Σ:=Σ.1)) [on_ind on_body].
    have wfΣ1 := (wfΣ : wf Σ.1).
    have wfΣwk := declared_inductive_wf_ext_wk _ _ _ wfΣ (proj1 inddecl).

    move: (discrtypok)=> /(isType_mkApps_Ind_inv wfΣ inddecl Γwf).
    rewrite firstn_app_left // skipn_all_app_eq //.
    move=> [parsubst [indxsubst]].
    match goal with [|- ?t -> _] => let_to_set t end.
    move=> [sspparams ssindices _ indiceslen puinstok].

    exists (indxsubst ++ parsubst).

    rewrite subst_instance_app_ctx.
    have indxsubstlen : #|(ind_indices oib)@[puinst]| = #|indxsubst|.
    {
      rewrite -(subst_context_length parsubst 0 _).
      symmetry. apply: PCUICSubstitution.subslet_length. 
      exact (ssindices.(inst_subslet)).
    }
    apply: spine_subst_app.
    * rewrite pparamslen context_assumptions_subst_instance.
      apply: PCUICGlobalEnv.declared_minductive_ind_npars; exact: proj1 inddecl.
    * rewrite -app_context_assoc-subst_instance_app_ctx; apply: weaken_wf_local=> //.
      set (Δ := _ ,,, _). destruct Σ as [Σ1 Σ2].
      refine (PCUICUnivSubstitutionTyp.typing_subst_instance_wf_local Σ1 Σ2 Δ puinst (ind_universes mib) _ _ _)=> //.
      move: (onArity on_body) => [lind].
      rewrite (PCUICGlobalMaps.ind_arity_eq on_body).
      move=> /PCUICSpine.type_it_mkProd_or_LetIn_inv [uparams [? [slparams + _ _]]].
      move=> /PCUICSpine.type_it_mkProd_or_LetIn_inv [uindxs [? [slindxs + _ _]]].
      move=> indsortTyp.
      pose proof (h := typing_wf_local indsortTyp); move: h.
      rewrite app_context_nil_l //.
    * rewrite skipn_all_app_eq //.
    * rewrite firstn_app_left // skipn_all_app_eq //.
  Qed.

End RandomLemmas.



Lemma type_Case_helper 
  `{cf : checker_flags}
  (ind : inductive) 
  (mib : mutual_inductive_body) 
  (oib : one_inductive_body) 
  (pparams : list term) 
  (puinst : Instance.t) 
  (discr : term) 
  (rettyp : term) 
  (brs : list term)
  (indices : list term)
  (ps : Universe.t) (Σ : global_env_ext) Γ :
  wf_ext Σ ->

  declared_inductive Σ ind mib oib ->

  #|pparams| = ind_npars mib ->
  
  Σ;;; Γ |- discr : mkApps (tInd ind puinst) (pparams ++ indices) ->

  let p := make_case_pred ind mib oib pparams puinst rettyp in
  let predctx := case_predicate_context ind mib oib p in


  (wf_local Σ (Γ,,, predctx) -> Σ ;;; Γ,,, predctx |- preturn p : tSort ps) ->

  (* consistent_instance_ext Σ (ind_universes mib) puinst -> *)

  is_allowed_elimination Σ (ind_kelim oib) ps ->

  isCoFinite (ind_finite mib) = false ->

  #|brs| = #|ind_ctors oib| ->

  let ptm := it_mkLambda_or_LetIn predctx rettyp in

  All2i
    (fun (i : nat) (cdecl : constructor_body) (brt : term) =>
      let br := make_br ind mib (* pparams puinst *) cdecl brt in
      let brctxty := case_branch_type ind mib oib p br ptm i cdecl in
        wf_local Σ (Γ,,, brctxty.1) ->
        typing Σ (Γ,,, brctxty.1) brctxty.2 (tSort ps) ->
        typing Σ (Γ,,, brctxty.1) (bbody br) brctxty.2
    )
    0 (ind_ctors oib) brs ->

  (* Why do we create a β-redex rather than substituting the indices and term ? *)
  let subst_rettyp := mkApps ptm (indices ++ [discr]) in

  Σ ;;; Γ |- make_case ind mib oib pparams puinst discr rettyp brs : subst_rettyp.
Proof.
  move=> wfΣ inddecl pparamslen discrtyp p predctx ptyp (* puinstok *) pselimok isfinite brslen ptm brstyp srettyp.
  set ci := {| ci_ind := ind ; ci_npar := ind_npars mib ; ci_relevance := ind_relevance oib |}.

  have wfΣ1 := (wfΣ : wf Σ.1).
  have Γwf : wf_local Σ Γ by apply: (typing_wf_local discrtyp).
  
  have wfpredp : wf_predicate mib oib p.
  {
    do 2 constructor=> //=.
    rewrite /expand_lets_ctx /expand_lets_k_ctx /subst_context /lift_context !forget_types_fold_context_k.
    apply: PCUICEquality.eq_context_gen_binder_annot; reflexivity.
  } 

  pose proof (discrtypok := validity discrtyp).

  have predctxwf : wf_local Σ (Γ ,,, predctx)
  by rewrite /predctx -[ind]/(ci_ind ci); apply: wf_case_predicate_context=> //=; eassumption.

  specialize (ptyp predctxwf).

  have puinstok : consistent_instance_ext Σ (ind_universes mib) puinst.
  by move: (discrtypok)=> /(isType_mkApps_Ind_inv wfΣ inddecl Γwf) [? [?] [?? _ ?]]//.

  have [s ssparamsindxs] : ∑ s, spine_subst Σ Γ (pparams ++ indices) s
                        (ind_params mib,,, ind_indices oib)@[puinst]
  by (apply: isType_mkApps_Ind_inv_spine => //; eassumption).

  apply: type_Case=> //.
  - apply: ptyp.
  - rewrite -/ci -/predctx. constructor=> //=; first reflexivity.
    apply: (spine_subst_ctx_inst ssparamsindxs).
  - have wfbrs : wf_branches oib (map2 (make_br ind mib) (ind_ctors oib) brs).
    {
      rewrite /wf_branches.
      elim: (ind_ctors oib) {brstyp}brs brslen=> [|decl ctors ih] //= [|br brs] //=.
      move=> [=] /ih h; constructor=> // {h}.
      hnf=>/=.
      rewrite /cstr_branch_context /expand_lets_ctx /expand_lets_k_ctx.
      rewrite /subst_context /lift_context !forget_types_fold_context_k.
      apply: PCUICEquality.eq_context_gen_binder_annot.
      apply: All2_fold_refl; reflexivity.
    }
  
    constructor=> //.

    apply: All2i_map2_right.
    rewrite -/ci -/p -/ptm -/predctx.
    apply Forall2_All2 in wfbrs.
    apply All2_map2_right_inv in wfbrs=> //.
    pose proof (declctors := declared_ind_declared_constructors inddecl).
    epose proof (alls := All2i_All2_mix_left wfbrs (All2i_Alli_mix_left declctors brstyp)).

    apply: (All2i_impl alls) => i x y.

    move=> [wfbr [declctor]]. 
    set (br := make_br _ _ _  _). rewrite -/br in wfbr. 
    set (brctxty := case_branch_type _ _ _ _ _ _ _ _).

    move=> bodytyp.
    split; first (apply: All2_refl; reflexivity).
    unshelve epose proof (X := wf_case_branch_type (Γ:=Γ)(p:=p) (ci:=ci) ps indices inddecl discrtypok wfpredp ptyp _ i x br declctor wfbr).
    1: reflexivity.
    move: X=> [] *. split=> //. split=> //.
    apply: bodytyp=> //.
Qed.



Lemma type_Case_subst_helper 
  `{cf : checker_flags}
  (ind : inductive) 
  (mib : mutual_inductive_body) 
  (oib : one_inductive_body) 
  (pparams : list term) 
  (puinst : Instance.t) 
  (discr : term) 
  (rettyp : term) 
  (brs : list term)
  (indices : list term)
  (ps : Universe.t) (Σ : global_env_ext) Γ :
  wf_ext Σ ->

  declared_inductive Σ ind mib oib ->

  #|pparams| = ind_npars mib ->
  
  Σ;;; Γ |- discr : mkApps (tInd ind puinst) (pparams ++ indices) ->

  let p := make_case_pred ind mib oib pparams puinst rettyp in
  let predctx := case_predicate_context ind mib oib p in


  (wf_local Σ (Γ,,, predctx) -> Σ ;;; Γ,,, predctx |- preturn p : tSort ps) ->

  is_allowed_elimination Σ (ind_kelim oib) ps ->

  isCoFinite (ind_finite mib) = false ->

  #|brs| = #|ind_ctors oib| ->


  All2i
    (fun (i : nat) (cdecl : constructor_body) (brt : term) =>
      let br := make_br ind mib cdecl brt in
      let brctx := case_branch_context ind mib p br cdecl in
      let brty := case_branch_type_subst ind mib p predctx rettyp i cdecl in
      wf_local Σ (Γ,,, brctx) ->
      typing Σ (Γ,,, brctx) brty (tSort ps) ->
      typing Σ (Γ,,, brctx) (bbody br) brty
    )
    0 (ind_ctors oib) brs ->

  let subst_rettyp := subst0 (mk_ctx_subst predctx (indices ++ [discr])) rettyp in

  Σ ;;; Γ |- make_case ind mib oib pparams puinst discr rettyp brs : subst_rettyp.
Proof.
  move=> wfΣ inddecl pparamslen discrtyp p predctx predWty elimok finok brslen brsok substrettyp.

  set ci := {| ci_ind := ind ; ci_npar := ind_npars mib ; ci_relevance := ind_relevance oib |}.

  have wfΣ1 := (wfΣ : wf Σ.1).
  have Γwf : wf_local Σ Γ by apply: (typing_wf_local discrtyp).
  
  have wfpredp : wf_predicate mib oib p.
  {
    do 2 constructor=> //=.
    rewrite /expand_lets_ctx /expand_lets_k_ctx /subst_context /lift_context !forget_types_fold_context_k.
    apply: PCUICEquality.eq_context_gen_binder_annot; reflexivity.
  } 


  pose proof (discrtypok := validity discrtyp).

  have predctxwf : wf_local Σ (Γ ,,, predctx)
  by rewrite /predctx -[ind]/(ci_ind ci); apply: wf_case_predicate_context=> //=; eassumption.


  move: (discrtypok)=> /(isType_mkApps_Ind_inv wfΣ inddecl Γwf).
  rewrite firstn_app_left // skipn_all_app_eq //.
  move=> [parsubst [indxsubst]].
  move=> [sspparams ssindices _ indiceslen puinstok].

  set ptm := it_mkLambda_or_LetIn predctx rettyp.
  set redex_rettyp := mkApps ptm (indices ++ [discr]).
  

  have ?: closedn #|Γ,,, predctx| rettyp
  by apply: PCUICClosedTyp.subject_closed; exact: (predWty predctxwf).
  have ?: closed_ctx (Γ,,, predctx)
  by apply: PCUICClosedTyp.closed_wf_local; exact: predctxwf.
  
  have mk_caseWtyp : Σ;;; Γ |- make_case ind mib oib pparams puinst discr rettyp brs : redex_rettyp.
  {
    apply: type_Case_helper=> //; try eassumption.
    pose proof (declctors := declared_ind_declared_constructors inddecl).
    apply: (All2i_impl (All2i_Alli_mix_left declctors brsok)) => i x t [declctor h] br.
    rewrite case_branch_type_split.
    set brctx := (x in (x, _)).
    set brty := (x in (_, x)).
    move=> /= wf wfty.

    have ?: closed_ctx (Γ,,, pre_case_branch_context_gen ind mib x pparams puinst)
    by apply: PCUICClosedTyp.closed_wf_local; rewrite -(case_branch_context_unfold _ _ oib _ _ rettyp _ t).
    
    have ?: #|cstr_indices x| + 1 = context_assumptions predctx.
    {
      rewrite /predctx PCUICCasesContexts.inst_case_predicate_context_eq; first reflexivity.
      rewrite (cstr_indices_length declctor); len.
    }

    econstructor; try eassumption.
    + apply: (h wf).
      eapply subject_reduction; try eassumption.
      rewrite case_branch_context_unfold.
      apply: case_branch_type_beta=> //.
    + apply: cumul_Sym.
      rewrite /brctx case_branch_context_unfold.
      apply: case_branch_type_conv_beta=> //; try eassumption.
      exact: closed_spine_subst_inst sspparams.
  }
  

  specialize (predWty predctxwf).

  have ?: #|indices ++ [discr]| = context_assumptions predctx.
  by len; rewrite indiceslen /predctx PCUICCasesContexts.inst_case_predicate_context_eq;
     first reflexivity; len.

  have red_rettyp : PCUICReduction.red Σ.1 Γ redex_rettyp substrettyp
  by apply: red_betas=> //.

  econstructor.
  1: exact: mk_caseWtyp.
  - apply: subject_reduction; last exact red_rettyp.
    exact: (validity mk_caseWtyp).π2.
  - apply: convSpec_cumulSpec.
    apply: conv_betas=> //.
    rewrite forallb_app /= (PCUICClosedTyp.subject_closed discrtyp) !andb_true_r.
    apply: closed_spine_subst_inst ssindices.
Qed.

Lemma type_Case_simple_subst_helper 
  `{cf : checker_flags}
  (ind : inductive) 
  (mib : mutual_inductive_body) 
  (oib : one_inductive_body) 
  (pparams : list term) 
  (puinst : Instance.t) 
  (discr : term) 
  (rettyp : term) 
  (brs : list term)
  (indices : list term)
  (ps : Universe.t) (Σ : global_env_ext) Γ :
  wf_ext Σ ->

  declared_inductive Σ ind mib oib ->

  #|pparams| = ind_npars mib ->
  
  Σ;;; Γ |- discr : mkApps (tInd ind puinst) (pparams ++ indices) ->

  let rettyp' := lift0 (S #|ind_indices oib|) rettyp in

  let p := make_case_pred ind mib oib pparams puinst rettyp' in
  let predctx := case_predicate_context ind mib oib p in


  Σ ;;; Γ |- rettyp : tSort ps ->

  is_allowed_elimination Σ (ind_kelim oib) ps ->

  isCoFinite (ind_finite mib) = false ->

  #|brs| = #|ind_ctors oib| ->


  All2i
    (fun (i : nat) (cdecl : constructor_body) (brt : term) =>
      let br := make_br ind mib cdecl brt in
      let brctx := case_branch_context ind mib p br cdecl in
      let brty := lift0 #|brctx| rettyp in
      wf_local Σ (Γ,,, brctx) ->
      typing Σ (Γ,,, brctx) brty (tSort ps) ->
      typing Σ (Γ,,, brctx) (bbody br) brty
    )
    0 (ind_ctors oib) brs ->


  Σ ;;; Γ |- make_case ind mib oib pparams puinst discr rettyp' brs : rettyp.
Proof.
  move=> wfΣ inddecl pparamslen discrtyp rettyp' p predctx predWty elimok finok brslen brsok.

  set ci := {| ci_ind := ind ; ci_npar := ind_npars mib ; ci_relevance := ind_relevance oib |}.

  have wfΣ1 := (wfΣ : wf Σ.1).
  have Γwf : wf_local Σ Γ by apply: (typing_wf_local discrtyp).
  
  have wfpredp : wf_predicate mib oib p.
  {
    do 2 constructor=> //=.
    rewrite /expand_lets_ctx /expand_lets_k_ctx /subst_context /lift_context !forget_types_fold_context_k.
    apply: PCUICEquality.eq_context_gen_binder_annot; reflexivity.
  } 


  pose proof (discrtypok := validity discrtyp).

  have predctxwf : wf_local Σ (Γ ,,, predctx)
  by rewrite /predctx -[ind]/(ci_ind ci); apply: wf_case_predicate_context=> //=; eassumption.


  move: (discrtypok)=> /(isType_mkApps_Ind_inv wfΣ inddecl Γwf).
  rewrite firstn_app_left // skipn_all_app_eq //.
  move=> [parsubst [indxsubst]].
  move=> [sspparams ssindices _ indiceslen puinstok].

  have predctxlen : S #|ind_indices oib| = #|predctx|
  by rewrite /predctx PCUICCasesContexts.inst_case_predicate_context_eq; first reflexivity; len.

  have ? : context_assumptions predctx = S #|indices|
  by rewrite /predctx PCUICCasesContexts.inst_case_predicate_context_eq; try reflexivity; len.

  set subst_rettyp' := subst0 (mk_ctx_subst predctx (indices ++ [discr])) rettyp'.
  have -> : rettyp = subst_rettyp'.
  by rewrite /subst_rettyp' /rettyp' PCUICLiftSubst.simpl_subst_k // mk_ctx_subst_length //; len.

  apply: type_Case_subst_helper=> //; try eassumption.
  - rewrite -/predctx=> ? /=.
    have -> : tSort ps = lift0 (S #|ind_indices oib|) (tSort ps) by reflexivity.
    apply: weakening_gen=> //.
  - pose proof (declctors := declared_ind_declared_constructors inddecl).
    apply: (All2i_impl (All2i_Alli_mix_left declctors brsok)) => i x t [declctor h] br brctx brty wfctx wfty.
    move: (h wfctx). rewrite -/brctx -/br.
    set brty' := (lift0 _ _).
    have <- : brty = brty'; last by apply.
    rewrite /brty' /brty /rettyp' /case_branch_type_subst /case_branch_type_subst_gen /=.
    rewrite -/predctx -predctxlen. set s := (_ ++ _).
    rewrite PCUICLiftSubst.simpl_lift. 1,2: lia.
    rewrite PCUICContexts.subst_lift_above.
    + rewrite mk_ctx_subst_length /s; len.
      rewrite /predctx PCUICCasesContexts.inst_case_predicate_context_eq; first reflexivity.
      rewrite (cstr_indices_length declctor); len.
    + f_equal. rewrite /brctx case_branch_context_unfold; len.
Qed.


(* Trying to factor some of the redundancy in the proofs for the
  3 different typing rules for match.

  Idea of the approach : Employ sections to share parameters
  and some bindings, lemmas + Let to add shared intermediate
  steps, and a wrapping module + a module signature defined
  from the module to only export the final lemmas.
  
  Problems:
  - intermediate Lemmas are not added to the context 
    (mediated through Let, but annoying).
  - section variables cannot be cleared/shadowed
  - Let bindings in sections are automatically expanded in the final lemma
  - the trick to automatically copy the type of a lemma in a module type does not manage implicits/typeclasses
*)


(* Notation typeof x := ltac:(let t := type of x in exact t) (only parsing). *)

(* Simple example of the hiding trick *)
(* 
Module AImpl.
  Definition a : nat -> nat := fun x => x.
End AImpl.

Module Type AIntf.
  Parameter a : typeof AImpl.a.
End AIntf.

Module A : AIntf := AImpl.

Print A.a.
 *)

(*

Module type_CaseLemmas.
Section type_Case.
  Context `{cf : checker_flags}
  (ind : inductive) 
  (mib : mutual_inductive_body) 
  (oib : one_inductive_body) 
  (pparams : list term) 
  (puinst : Instance.t) 
  (discr : term) 
  (brs : list term)
  (indices : list term)
  (ps : Universe.t) 
  (Σ : global_env_ext) 
  (Γ : context)
  (wfΣ : wf_ext Σ)

  (inddecl : declared_inductive Σ ind mib oib)
  (pselimok : is_allowed_elimination Σ (ind_kelim oib) ps)
  (isfinite : isCoFinite (ind_finite mib) = false)

  (pparamslen : #|pparams| = ind_npars mib)
  (brslen : #|brs| = #|ind_ctors oib|)

  (discrtyp : Σ;;; Γ |- discr : mkApps (tInd ind puinst) (pparams ++ indices)).


  Let ci := {| ci_ind := ind ; ci_npar := ind_npars mib ; ci_relevance := ind_relevance oib |}.

  Let wfΣ1 := (wfΣ : wf Σ.1).

  Lemma Γwf0 : wf_local Σ Γ.
  Proof. apply: (typing_wf_local discrtyp). Qed.
  Let Γwf := Γwf0.

  Lemma discrtypok0 : isType Σ Γ (mkApps (tInd ind puinst) (pparams ++ indices)).
  Proof. exact: validity discrtyp. Qed.
  Let discrtypok := discrtypok0.
 
  Lemma puinstok0 : consistent_instance_ext Σ (ind_universes mib) puinst.
  Proof.
    move: (discrtypok)=> /(isType_mkApps_Ind_inv wfΣ inddecl Γwf) [? [?] [?? _ ?]]//.
  Qed.
  Let puinstok := puinstok0.


  Section GeneralCase.
  Context 
    (rettyp : term) 
    (p := make_case_pred ind mib oib pparams puinst rettyp)
    (predctx := case_predicate_context ind mib oib p)
    (ptm := it_mkLambda_or_LetIn predctx rettyp)

    (ptyp : wf_local Σ (Γ,,, predctx) -> Σ ;;; Γ,,, predctx |- preturn p : tSort ps).

  Lemma wfpredp0 : wf_predicate mib oib p.
  Proof.
    do 2 constructor=> //=.
    rewrite /expand_lets_ctx /expand_lets_k_ctx /subst_context /lift_context !forget_types_fold_context_k.
    apply: PCUICEquality.eq_context_gen_binder_annot; reflexivity.
  Qed.
  Let wfpredp := wfpredp0.

  Lemma predctxwf0 : wf_local Σ (Γ ,,, predctx).
  Proof.
    rewrite /predctx -[ind]/(ci_ind ci); apply: wf_case_predicate_context=> //=; eassumption.
  Qed.
  Let predctxwf := predctxwf0.
  
  Let ptyp' := ptyp predctxwf.

  Let declctors := declared_ind_declared_constructors inddecl.

  Lemma type_Case_helper
    (brstyp :
      let brwty (i : nat) (cdecl : constructor_body) (brt : term) :=
        let br := make_br ind mib (* pparams puinst *) cdecl brt in
        let brctxty := case_branch_type ind mib oib p br ptm i cdecl in
          wf_local Σ (Γ,,, brctxty.1) ->
          typing Σ (Γ,,, brctxty.1) brctxty.2 (tSort ps) ->
          typing Σ (Γ,,, brctxty.1) (bbody br) brctxty.2
      in All2i brwty 0 (ind_ctors oib) brs)
    (subst_rettyp := mkApps ptm (indices ++ [discr])) :
    Σ ;;; Γ |- make_case ind mib oib pparams puinst discr rettyp brs : subst_rettyp.
  Proof using Γwf wfΣ wfpredp puinstok ptyp' ptyp pselimok predctxwf pparamslen
  isfinite inddecl discrtypok discrtyp declctors brslen.
    have [s ssparamsindxs] : ∑ s, spine_subst Σ Γ (pparams ++ indices) s
                          (ind_params mib,,, ind_indices oib)@[puinst]
    by apply: isType_mkApps_Ind_inv_spine => //; first eassumption.

    apply: type_Case=> //.
    - apply: ptyp'.
    - rewrite -/ci -/predctx. constructor=> //=; first reflexivity.
      apply: (spine_subst_ctx_inst ssparamsindxs).
    - have wfbrs : wf_branches oib (map2 (make_br ind mib) (ind_ctors oib) brs).
      {
        rewrite /wf_branches.
        elim: (ind_ctors oib) {brstyp}brs brslen=> [|decl ctors ih] //= [|br brs'] //=.
        move=> [=] /ih h; constructor=> // {h}.
        hnf=>/=.
        rewrite /cstr_branch_context /expand_lets_ctx /expand_lets_k_ctx.
        rewrite /subst_context /lift_context !forget_types_fold_context_k.
        apply: PCUICEquality.eq_context_gen_binder_annot.
        apply: All2_fold_refl; reflexivity.
      }
    
      constructor=> //; rewrite -/ci -/p -/ptm -/predctx.

      apply Forall2_All2 in wfbrs.
      apply All2_map2_right_inv in wfbrs=> //.
      epose proof (alls := All2i_All2_mix_left wfbrs (All2i_Alli_mix_left declctors brstyp)).

      apply: All2i_map2_right; apply: (All2i_impl alls) => i x y.

      move=> [wfbr [declctor]]. 
      set (br := make_br _ _ _  _). rewrite -/br in wfbr. 
      set (brctxty := case_branch_type _ _ _ _ _ _ _ _).

      move=> bodytyp.
      split; first (apply: All2_refl; reflexivity).
      unshelve epose proof (X := wf_case_branch_type (Γ:=Γ)(p:=p) (ci:=ci) ps indices inddecl discrtypok wfpredp ptyp' _ i x br declctor wfbr).
      1: reflexivity.
      move: X=> [] *. split=> //. split=> //.
      apply: bodytyp=> //.
  Qed.

  Lemma type_Case_subst_helper 
    (brstyp :
      let brwty (i : nat) (cdecl : constructor_body) (brt : term) :=  
        let br := make_br ind mib cdecl brt in
        let brctx := case_branch_context ind mib p br cdecl in
        let brty := case_branch_type_subst ind mib p predctx rettyp i cdecl in
        wf_local Σ (Γ,,, brctx) ->
        typing Σ (Γ,,, brctx) brty (tSort ps) ->
        typing Σ (Γ,,, brctx) (bbody br) brty
      in All2i brwty 0 (ind_ctors oib) brs)
    (substrettyp := subst0 (mk_ctx_subst predctx (indices ++ [discr])) rettyp) :
    Σ ;;; Γ |- make_case ind mib oib pparams puinst discr rettyp brs : substrettyp.
  Proof using Γwf wfΣ1 wfΣ wfpredp puinstok ptyp' ptyp pselimok predctxwf pparamslen
              isfinite inddecl discrtypok discrtyp declctors brslen.
    move: (discrtypok)=> /(isType_mkApps_Ind_inv wfΣ inddecl Γwf).
    rewrite firstn_app_left // skipn_all_app_eq //.
    move=> [parsubst [indxsubst]].
    move=> [sspparams ssindices _ indiceslen _].

    set redex_rettyp := mkApps ptm (indices ++ [discr]).

    have ?: closedn #|Γ,,, predctx| rettyp
    by apply: PCUICClosedTyp.subject_closed; exact: ptyp'.
    have ?: closed_ctx (Γ,,, predctx)
    by apply: PCUICClosedTyp.closed_wf_local; exact: predctxwf.
    
    have mk_caseWtyp : Σ;;; Γ |- make_case ind mib oib pparams puinst discr rettyp brs : redex_rettyp.
    {
      apply: type_Case_helper=> //; try eassumption.
      apply: (All2i_impl (All2i_Alli_mix_left declctors brstyp)) => i x t [declctor h] br.
      rewrite case_branch_type_split.
      set brctx := (x in (x, _)).
      set brty := (x in (_, x)).
      move=> /= wf wfty.

      have ?: closed_ctx (Γ,,, pre_case_branch_context_gen ind mib x pparams puinst)
      by apply: PCUICClosedTyp.closed_wf_local; rewrite -(case_branch_context_unfold _ _ oib _ _ rettyp _ t).
      
      have ?: #|cstr_indices x| + 1 = context_assumptions predctx.
      {
        rewrite /predctx PCUICCasesContexts.inst_case_predicate_context_eq; first reflexivity.
        rewrite (cstr_indices_length declctor); len.
      }

      econstructor; try eassumption.
      + apply: (h wf).
        eapply subject_reduction; try eassumption.
        rewrite case_branch_context_unfold.
        apply: case_branch_type_beta=> //.
      + apply: cumul_Sym.
        rewrite /brctx case_branch_context_unfold.
        apply: case_branch_type_conv_beta=> //; try eassumption.
        exact: closed_spine_subst_inst sspparams.
    }

    have ?: #|indices ++ [discr]| = context_assumptions predctx.
    by len; rewrite indiceslen /predctx PCUICCasesContexts.inst_case_predicate_context_eq;
      first reflexivity; len.

    have red_rettyp : PCUICReduction.red Σ.1 Γ redex_rettyp substrettyp
    by apply: red_betas=> //.

    econstructor.
    1: exact: mk_caseWtyp.
    - apply: subject_reduction; last exact red_rettyp.
      exact: (validity mk_caseWtyp).π2.
    - apply: convSpec_cumulSpec.
      apply: conv_betas=> //.
      rewrite forallb_app /= (PCUICClosedTyp.subject_closed discrtyp) !andb_true_r.
      apply: closed_spine_subst_inst ssindices.
  Qed.

  End GeneralCase.

  Lemma type_Case_simple_subst_helper 
    (rettyp : term)
    (rettyp' := lift0 (S #|ind_indices oib|) rettyp)
    (p := make_case_pred ind mib oib pparams puinst rettyp')
    (predctx := case_predicate_context ind mib oib p)
    (predWty : Σ ;;; Γ |- rettyp : tSort ps)
    (brsok :
      let brwty (i : nat) (cdecl : constructor_body) (brt : term) :=
        let br := make_br ind mib cdecl brt in
        let brctx := case_branch_context ind mib p br cdecl in
        let brty := lift0 #|brctx| rettyp in
        wf_local Σ (Γ,,, brctx) ->
        typing Σ (Γ,,, brctx) brty (tSort ps) ->
        typing Σ (Γ,,, brctx) (bbody br) brty
      in All2i brwty 0 (ind_ctors oib) brs) :
    Σ ;;; Γ |- make_case ind mib oib pparams puinst discr rettyp' brs : rettyp.
  Proof using Γwf wfΣ1 wfΣ puinstok pselimok pparamslen isfinite indices inddecl
              discrtypok discrtyp brslen.
    have wfpredp : wf_predicate mib oib p.
    {
      do 2 constructor=> //=.
      rewrite /expand_lets_ctx /expand_lets_k_ctx /subst_context /lift_context !forget_types_fold_context_k.
      apply: PCUICEquality.eq_context_gen_binder_annot; reflexivity.
    } 

    have predctxwf : wf_local Σ (Γ ,,, predctx)
    by rewrite /predctx -[ind]/(ci_ind ci); apply: wf_case_predicate_context=> //=; eassumption.


    move: (discrtypok)=> /(isType_mkApps_Ind_inv wfΣ inddecl Γwf).
    rewrite firstn_app_left // skipn_all_app_eq //.
    move=> [parsubst [indxsubst]].
    move=> [sspparams ssindices _ indiceslen _].

    have predctxlen : S #|ind_indices oib| = #|predctx|
    by rewrite /predctx PCUICCasesContexts.inst_case_predicate_context_eq; first reflexivity; len.

    have ? : context_assumptions predctx = S #|indices|
    by rewrite /predctx PCUICCasesContexts.inst_case_predicate_context_eq; try reflexivity; len.

    set subst_rettyp' := subst0 (mk_ctx_subst predctx (indices ++ [discr])) rettyp'.
    have -> : rettyp = subst_rettyp'.
    by rewrite /subst_rettyp' /rettyp' PCUICLiftSubst.simpl_subst_k // mk_ctx_subst_length //; len.

    apply: type_Case_subst_helper=> //; try eassumption.
    - rewrite -/predctx=> ? /=.
      have -> : tSort ps = lift0 (S #|ind_indices oib|) (tSort ps) by reflexivity.
      apply: weakening_gen=> //.
    - pose proof (declctors := declared_ind_declared_constructors inddecl).
      apply: (All2i_impl (All2i_Alli_mix_left declctors brsok)) => i x t [declctor h] br brctx brty wfctx wfty.
      move: (h wfctx). rewrite -/brctx -/br.
      set brty' := (lift0 _ _).
      have <- : brty = brty'; last by apply.
      rewrite /brty' /brty /rettyp' /case_branch_type_subst /case_branch_type_subst_gen /=.
      rewrite -/predctx -predctxlen. set s := (_ ++ _).
      rewrite PCUICLiftSubst.simpl_lift. 1,2: lia.
      rewrite PCUICContexts.subst_lift_above.
      + rewrite mk_ctx_subst_length /s; len.
        rewrite /predctx PCUICCasesContexts.inst_case_predicate_context_eq; first reflexivity.
        rewrite (cstr_indices_length declctor); len.
      + f_equal. rewrite /brctx case_branch_context_unfold; len.
  Qed.
End type_Case.
End type_CaseLemmas.

Module Type SIG_type_Case.
  Parameter type_Case_helper : typeof (@type_CaseLemmas.type_Case_helper). 
  Parameter type_Case_subst_helper : typeof (@type_CaseLemmas.type_Case_subst_helper).
  Parameter type_Case_simple_subst_helper : typeof (@type_CaseLemmas.type_Case_simple_subst_helper).
End SIG_type_Case.

Module type_CaseH : SIG_type_Case := type_CaseLemmas.

Print type_CaseH.type_Case_helper.


  *)