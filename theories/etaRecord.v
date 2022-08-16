From Coq Require Import Strings.String ssreflect ssrbool ssrfun.
From MetaCoq.Template Require Import All.
From Genxs Require Import metacoq_utils.

Set Primitive Projections.

Class Eta_exp A := { eta_exp : A -> A}.
Class Eta A `{Eta_exp A} := { eta : forall (a:A), a = eta_exp a }.

MetaCoq Run (def_kername "Eta_exp"%bs "Eta_exp_kername"%bs).
MetaCoq Run (def_kername "Eta"%bs "Eta_kername"%bs).

Definition anonRel : aname := {| binder_name := nAnon ; binder_relevance := Relevant |}.

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
        let proj := mkProjection ind (ind_npars mib) idx_proj in
        tProj proj (tRel 0)
      in
      tApp ctor (mapi map_fun (ind_projs oib))
  in
  let eta0 := tLambda anonRel indful body in
  let eta_exp0 :=
      tApp (tConstruct (mkInd Eta_exp_kername 0) 0 nil) (indful :: eta0 :: nil)%list
  in
  (it_mkLambda_or_LetIn ctx eta0,
   it_mkLambda_or_LetIn ctx eta_exp0).

Axiom unreachable : forall {A}, A.
Definition eq_ind := Eval cbn in match <% @eq %> with | tInd x _ => x | _ => unreachable end. 

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
        let proj := mkProjection ind (ind_npars mib) idx_proj in
        tProj proj (tRel 0)
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
  let qrefl :=
      tApp <% @eq_refl %> (indful 1 :: (tRel 0 :: nil)%list)
  in
  let qeq :=
      tApp <% @eq %> (indful 1 :: (tRel 0 :: eta :: nil)%list)
  in
  let eta_eq := tLambda anonRel (indful 0) (tCast qrefl Cast qeq) in
  let eta_record :=
      let eta_exp := mkApps_ctx existing_eta_exp 0 ctx in
      tApp (tConstruct (mkInd Eta_kername 0) 0 nil)
           (indful 0 :: eta_exp :: eta_eq :: nil)%list
  in
  (it_mkLambda_or_LetIn ctx eta_eq,
   it_mkLambda_or_LetIn ctx eta_record).



Import MCMonadNotation.


Set Printing Universes.
Definition gen_eta_instance (id:ident) : TemplateMonad unit :=
  (* REPORT : if the inductive does not exists, raises an anomaly... *)
  ind <- get_inductive id ;;
  mib <- tmQuoteInductive ind.(inductive_mind) ;;
  oib <- extract_uniq (ind_bodies mib) "nope"%bs ;;

  let eta_exp := (eta_oib ind mib oib).2 in
  let eta_exp_id := ("eta" ++ id)%bs in
  tmMkDefinition eta_exp_id eta_exp;;
  eta_exp_kn <- get_const eta_exp_id ;; 
  tmExistingInstance (ConstRef eta_exp_kn) ;;

  ind_eta_exp <- get_const eta_exp_id ;;
  let '(_, eta) :=
    let qeta_exp := tConst ind_eta_exp nil in
    eta_eq_oib ind mib oib qeta_exp
  in
  let eta_eq_id := ("eta_eq" ++ id)%bs in
  tmMkDefinition eta_eq_id eta ;;
  eta_eq_kn <- get_const eta_eq_id ;;
  tmExistingInstance (ConstRef eta_eq_kn).


(** Tests *)

Module EtaTests.

  Record R := {x : nat; y : bool ; z : unit -> unit}.

  MetaCoq Run (gen_eta_instance "R"%bs).

  Goal forall (r:R) f, f r.
    move=> r; rewrite [r]eta/=.
  Abort.

  (** Trying with params *)

  Record R2 A := { a : A }.

  MetaCoq Run (gen_eta_instance "R2"%bs).
  
  Goal forall (r:R2 nat) f, f r.
    move=> r; rewrite [r]eta/=.
  Abort.

  (** also dependency *)

  Record R3 (A : Type) (B : A -> Type) := { p : A ; q : B p }.
  MetaCoq Run (gen_eta_instance "R3"%bs).

  From Coq Require Import Fin.

  Goal forall (r:R3 nat Fin.t) f, f r.
    move=> r; rewrite [r]eta/=.
  Abort.

  Record R4 := { C : Type ; op : C -> C -> C ; law : forall x y z, op x (op y z) = x }.
  MetaCoq Run (gen_eta_instance "R4"%bs).
  Goal forall (r:R3 nat Fin.t) f, f r.
    move=> r; rewrite [r]eta/=.
  Abort.

  (* Pushing too far ? *)

  CoInductive Stream := { hd : nat ; tl : Stream }.
  (* Fails as expected (eg. would break SR) *)
  Fail MetaCoq Run (gen_eta_instance "Stream"%bs).

  (* Is there a way to use Pierre-Marie's criterion for dependent elimination of positive CoInductives ? *)
End EtaTests.
