From Coq Require Import ssreflect ssrbool ssrfun.
From MetaCoq.Template Require Import All.




Definition fold_right_i [A B] (f : nat -> B -> A -> A) (a0 : A) :=
  (fix fold_right_i n (l : list B) : A :=
    match l with
    | []%list => a0
    | (hd :: tl)%list => f n hd (fold_right_i (S n) tl)
    end) 0.



(** Helper functions relying on MetaCoq *)

(** [build_const [t1;..;tn] body] builds the term λ(_:t1)..(_:tn).body *)
Definition build_const (argtys: list term) body :=
  List.fold_right
    (fun ty t => tLambda (mkBindAnn nAnon Relevant) ty t)
     body argtys.

(** [mkApps_ctx t shift ctx] build the application of t to the ctx shifted by shift *)
Definition mkApps_ctx (t:term) (shift:nat) (ctx:context) :=
  let args :=
    let fold_fun args i decl :=
      match decl_body decl with
      | None => ((tRel (shift+i)) :: args)%list
      | Some _ => args
      end
    in
    fold_left_i fold_fun ctx nil in
  mkApps t args.

Definition is_prim_record (decl:mutual_inductive_body) : option (option ident)
  :=
    match ind_bodies decl with
    | (oib :: nil)%list =>
      match ind_ctors oib with
      | (ctor_body :: nil)%list => Some (Some (cstr_name ctor_body)) (* Some data is missing wrt to primitivity *)
      | _ => None
      end
    | _ => None
    end.


Definition one_ind_body_to_entry (decl : mutual_inductive_body) (oib : one_inductive_body) : one_inductive_entry :=
  let ra := remove_arity decl.(ind_npars) in
  let ctors := oib.(ind_ctors) in
  {|
    mind_entry_typename := oib.(ind_name);
    mind_entry_arity :=  oib.(ind_type);
    mind_entry_consnames := List.map cstr_name ctors ;
    mind_entry_lc := List.map (fun x => ra x.(cstr_type)) ctors;
  |}.

Arguments List.combine {_ _} _ _.
Definition mind_body_params (decl : mutual_inductive_body) : context :=
  match List.hd_error decl.(ind_bodies) with
  | Some oib =>
      let args := fst (decompose_prod oib.(ind_type)) in
      let nametypes := List.firstn decl.(ind_npars) (uncurry List.combine args) in
      List.rev (List.map (uncurry vass) nametypes)
  | None => nil
  end.
Arguments List.combine [_ _] _ _.

Definition mind_body_to_entry (decl : mutual_inductive_body)
  : mutual_inductive_entry :=
  {|
    mind_entry_record := is_prim_record decl;
    mind_entry_finite := ind_finite decl;
    mind_entry_params := mind_body_params decl ;
    mind_entry_inds := List.map (one_ind_body_to_entry decl) decl.(ind_bodies);
    mind_entry_universes := Universes.universes_entry_of_decl decl.(ind_universes);
    mind_entry_private := None ;
    mind_entry_template := false ;
    mind_entry_variance :=
      Option.map (List.map Some) decl.(ind_variance)
  |}.


Section TemplateMonad.
  Import MCMonadNotation.

  Polymorphic Definition monad_iteri {T} `{Monad T} {A} (f: nat -> A -> T unit) l :=
    monad_map_i f l ;; ret tt.

  (** [extract_uniq l fail_msg] returns x if l = [x] or fails with fail_msg *)
  Polymorphic Definition extract_uniq {A} (l :list A) (fail_msg:string) : TemplateMonad A :=
    match l with | (x :: nil)%list => ret x | _ => tmFail fail_msg end.


  Definition isIndRef := fun x => match x with IndRef _ => true | _ => false end.

  Polymorphic Definition get_inductive@{u} (qid:qualid): TemplateMonad@{_ u} inductive :=
    ts <- tmLocate qid ;;
    match List.filter isIndRef ts with
    | [ IndRef ind ]%list => ret ind
    | (_ :: _ :: _)%list => tmFail ("Ambiguous definition of " ++ qid ++ " as an inductive")%bs
    | _ => tmFail ("The ident " ++ qid ++ " does not refer to an existing inductive ")%bs
    end.

  Definition isConstRef := fun x => match x with ConstRef _ => true | _ => false end.
  Definition get_const (qid:qualid): TemplateMonad kername :=
    ts <- tmLocate qid ;;
    match List.filter isConstRef ts with
    | [ ConstRef kn ]%list => ret kn
    | (_ :: _ :: _)%list => tmFail ("Ambiguous definition of " ++ qid ++ " as a constant")%bs
    | _ => tmFail ("The ident " ++ qid ++ " does not refer to an existing const ant")%bs
    end.

  Definition assertTM (b:bool) : TemplateMonad unit :=
    if b then tmFail "assertion failed"%bs else ret tt.

  (** [def_kername id id_kername] looks up the kernel name of id
      and define a constant with name id_kername to it;
      fails if the associated kernel name is not uniquely defined *)
  Definition def_kername (id id_kername:ident) : TemplateMonad unit :=
    globrefs <- tmLocate id ;;
    kername <- match globrefs with
              | [ConstRef kn]%list => ret kn
              | [IndRef ind]%list => tmEval all (inductive_mind ind)
              | [VarRef _]%list =>
                tmFail ("Found a variable associated to "++ id ++", no associated kername")%bs
              | [ConstructRef _ _]%list =>
                tmFail ("Found a constructor associated to "++ id ++", no associated kername")%bs
              | []%list => tmFail ("No global reference associated to "++id)%bs
              | (_ :: _ :: _)%list => tmFail ("Multiple global references associated to "++id)%bs
              end ;;
    qkername <- tmQuote kername ;;
    tmMkDefinition id_kername qkername.
End TemplateMonad.
