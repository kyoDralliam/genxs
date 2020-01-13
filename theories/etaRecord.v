From Coq Require Import Strings.String ssreflect ssrbool ssrfun.
From MetaCoq.Template Require Import All.
From Genxs Require Import metacoq_utils.

Set Primitive Projections.

Import MonadNotation.


Class Eta_exp A := { eta_exp : A -> A}.
Class Eta A `{Eta_exp A} := { eta : forall (a:A), a = eta_exp a }.

Definition def_kername (id_ind id_kername:ident) : TemplateMonad unit :=
  ind <- get_inductive id_ind;;
  kername <- tmEval all (inductive_mind ind) ;;
  qkername <- tmQuote kername ;;
  tmMkDefinition id_kername qkername.

Run TemplateProgram (def_kername "Eta_exp" "Eta_exp_kername").
Run TemplateProgram (def_kername "Eta" "Eta_kername").

Definition eta_oib (ind:inductive)
           (mid:mutual_inductive_body)
           (oid:one_inductive_body)
  : term * term :=
  let uvs := match ind_universes mid with
             | _ => nil (*FIXME: universes *)
             end in

  (* let ctx := ind_params mib in *)
  (* let ind shift := mkApps_ctx (tInd ind uvs) shift ctx in *)

  let indful := tInd ind uvs in
  let ctor := tConstruct ind 0 uvs  in
  let body :=
      let map_fun idx_proj _proj :=
          tProj (ind, ind_npars mid, idx_proj) (tRel 0)
      in
      tApp ctor (mapi map_fun (ind_projs oid))
  in
  let eta := tLambda nAnon indful body in
  let eta_exp :=
      tApp (tConstruct (mkInd Eta_exp_kername 0) 0 nil) (indful :: eta :: nil)%list
  in
  (eta, eta_exp).

Definition eta_eq_oib (ind:inductive)
           (mid:mutual_inductive_body)
           (oid: one_inductive_body)
           (existing_eta_exp : term)
  : term * term :=
  let uvs := nil (*FIXME: universes *) in
  let indful := tInd ind uvs in
  let eta :=
      let ctor := tConstruct ind 0 uvs  in
      let map_fun idx_proj _proj :=
          tProj (ind, 0 (* FIXME: params*), idx_proj) (tRel 0)
      in
      tApp ctor (mapi map_fun (ind_projs oid))
  in
  let eq_ind :=
      {| inductive_mind := "Coq.Init.Logic.eq"; inductive_ind := 0 |}
  in
  let qrefl :=
      tApp (tConstruct eq_ind 0 nil) (indful :: (tRel 0 :: nil)%list)
  in
  let qeq :=
      tApp (tInd eq_ind nil) (indful :: (tRel 0 :: eta :: nil)%list)
  in
  let eta_eq := tLambda nAnon indful (tCast qrefl Cast qeq) in
  let eta_record :=
      tApp (tConstruct (mkInd Eta_kername 0) 0 nil)
           (indful :: existing_eta_exp :: eta_eq :: nil)%list
  in
  (eta_eq, eta_record).



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

Run TemplateProgram (t <- tmQuoteInductive "R2";; tmPrint t).

Quote Definition etaR2 := (fun A (r2:R2 A) => {| a := a A r2 |}).
Print etaR2.
