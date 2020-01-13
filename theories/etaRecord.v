From Coq Require Import Strings.String ssreflect ssrbool ssrfun.
From MetaCoq.Template Require Import All.
From Genxs Require Import metacoq_utils.

Set Primitive Projections.

Class Eta_exp A := { eta_exp : A -> A}.
Class Eta A `{Eta_exp A} := { eta : forall (a:A), a = eta_exp a }.

Run TemplateProgram (def_kername "Eta_exp" "Eta_exp_kername").
Run TemplateProgram (def_kername "Eta" "Eta_kername").

Definition eta_oib (ind:inductive)
           (mib:mutual_inductive_body)
           (oib:one_inductive_body)
  : term * term :=
  let uvs := match ind_universes mib with
             | _ => nil (*FIXME: universes *)
             end in

  let ctx := ind_params mib in
  let indful := mkApps_ctx (tInd ind uvs) 0 ctx in

  let ctor := mkApps_ctx (tConstruct ind 0 uvs) 1 ctx in
  let body :=
      let map_fun idx_proj _proj :=
          tProj (ind, ind_npars mib, idx_proj) (tRel 0)
      in
      tApp ctor (mapi map_fun (ind_projs oib))
  in
  let eta0 := tLambda nAnon indful body in
  let eta_exp0 :=
      tApp (tConstruct (mkInd Eta_exp_kername 0) 0 nil) (indful :: eta0 :: nil)%list
  in
  (it_mkLambda_or_LetIn ctx eta0,
   it_mkLambda_or_LetIn ctx eta_exp0).

Definition eta_eq_oib (ind:inductive)
           (mib:mutual_inductive_body)
           (oib: one_inductive_body)
           (existing_eta_exp : term)
  : term * term :=
  let uvs := match ind_universes mib with
             | _ => nil (*FIXME: universes *)
             end in

  let ctx := ind_params mib in
  let indful shift := mkApps_ctx (tInd ind uvs) shift ctx in

  let eta :=
    let ctor := mkApps_ctx (tConstruct ind 0 uvs) 1 ctx in
    (* let body := *)
      let map_fun idx_proj _proj :=
          tProj (ind, ind_npars mib, idx_proj) (tRel 0)
      in
      tApp ctor (mapi map_fun (ind_projs oib))
    (* in *)
    (* tLambda nAnon indful body *)
  in

  (* let uvs := nil (*FIXME: universes *) in *)
  (* let indful := tInd ind uvs in *)
  (* let eta := *)
  (*     let ctor := tConstruct ind 0 uvs  in *)
  (*     let map_fun idx_proj _proj := *)
  (*         tProj (ind, 0 (* FIXME: params*), idx_proj) (tRel 0) *)
  (*     in *)
  (*     tApp ctor (mapi map_fun (ind_projs oib)) *)
  (* in *)
  let eq_ind :=
      {| inductive_mind := "Coq.Init.Logic.eq"; inductive_ind := 0 |}
  in
  let qrefl :=
      tApp (tConstruct eq_ind 0 nil) (indful 1 :: (tRel 0 :: nil)%list)
  in
  let qeq :=
      tApp (tInd eq_ind nil) (indful 1 :: (tRel 0 :: eta :: nil)%list)
  in
  let eta_eq := tLambda nAnon (indful 0) (tCast qrefl Cast qeq) in
  let eta_record :=
      let eta_exp := mkApps_ctx existing_eta_exp 0 ctx in
      tApp (tConstruct (mkInd Eta_kername 0) 0 nil)
           (indful 0 :: eta_exp :: eta_eq :: nil)%list
  in
  (it_mkLambda_or_LetIn ctx eta_eq,
   it_mkLambda_or_LetIn ctx eta_record).



Import MonadNotation.

Definition gen_eta_instance (id:ident) : TemplateMonad unit :=
  id <- tmEval all id ;;
  (* REPORT : if the inductive does not exists, raises an anomaly... *)
  mib <- tmQuoteInductive id ;;
  ind <- get_inductive id ;;
  oib <- extract_uniq (ind_bodies mib) "nope" ;;
  let '(_, eta_exp) := eta_oib ind mib oib in
  eta_exp_id <- tmEval all ("eta" ++ id) ;;
  tmMkDefinition eta_exp_id eta_exp;;
  tmExistingInstance eta_exp_id ;;
  ind_eta_exp <- get_const eta_exp_id ;;
  let '(_, eta) :=
      let qeta_exp := tConst ind_eta_exp nil in
      eta_eq_oib ind mib oib qeta_exp
  in
  eta_id <-  tmEval all ("eta_eq" ++ id) ;;
  tmMkDefinition eta_id eta ;;
  tmExistingInstance eta_id.



(** Tests *)

Record R := {x : nat; y : bool ; z : unit -> unit}.

Run TemplateProgram (gen_eta_instance "R").


(* Instance Eta_expR : Eta_exp R := *)
(*   ltac:(let t := eval unfold etaR in {| eta_exp := etaR |} in exact t). *)

(* Quote Definition qEta_expR := Eval unfold Eta_expR in Eta_expR. *)

(* Instance EtaR : Eta R := {| eta := eta_eqR |}. *)

(* Quote Definition qEta := Eval unfold EtaR in EtaR. *)

Goal forall (r:R) f, f r.
  move=> r; rewrite [r]eta/=. Abort.

(* Quote Definition qetaR := (fun (r:R) => {| x := x r; y := y r ; z := z r|}). *)
(* Quote Definition qetaR_eq := (fun (r:R) => eq_refl : r = etaR r). *)


(** Trying to extend to records with params *)

Record R2 A := { a : A }.

Run TemplateProgram (gen_eta_instance "R2").

Goal forall (r:R2 nat) f, f r.
  move=> r; rewrite [r]eta/=. Abort.

Run TemplateProgram (t <- tmQuoteInductive "R2";; tmPrint t).

Quote Definition etaR2 := (fun A (r2:R2 A) => {| a := a A r2 |}).
Print etaR2.
