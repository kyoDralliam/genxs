From Coq Require Import Strings.String ssreflect ssrbool ssrfun.
From MetaCoq.Template Require Import All.


(** Helper functions relying on MetaCoq *)

(** [build_const [t1;..;tn] body] builds the term λ(_:t1)..(_:tn).body *)
Fixpoint build_const (argtys: list term) body :=
  List.fold_right (fun ty t => tLambda nAnon ty t) body argtys.

(** [mkApps_ctx t shift ctx] build the application of t to the ctx shifted by shift *)
Definition mkApps_ctx (t:term) (shift:nat) (ctx:context) :=
  let args :=
    let fold_fun args i decl :=
      match decl_body decl with
      | None => ((tRel (shift+i)) :: args)%list
      | Some _ => args
      end
    in
    utils.fold_left_i fold_fun ctx nil in
  mkApps t args.

Definition is_prim_record (decl:mutual_inductive_body) : option (option ident)
  :=
    match ind_bodies decl with
    | (oib :: nil)%list =>
      match ind_ctors oib with
      | (((id,_), _) :: nil)%list => Some (Some id) (* Some data is missing wrt to primitivity *)
      | _ => None
      end
    | _ => None
    end.

Definition mind_body_to_entry (decl : mutual_inductive_body)
  : mutual_inductive_entry.
Proof.
  refine {| mind_entry_record := is_prim_record decl;
            mind_entry_finite := ind_finite decl;
            mind_entry_params := _;
            mind_entry_inds := _;
            mind_entry_universes := decl.(ind_universes);
            mind_entry_private := None |}.
  - refine (match List.hd_error decl.(ind_bodies) with
            | Some i0 => List.rev _
            | None => nil (* assert false: at least one inductive in a mutual block *)
            end).
    have [[names types] _] := decompose_prod i0.(ind_type).
    apply (List.firstn decl.(ind_npars)) in names.
    apply (List.firstn decl.(ind_npars)) in types.
    apply: List.combine; [
      exact (List.map get_ident names)
    | exact (List.map LocalAssum types)].
  - refine (List.map _ decl.(ind_bodies)).
    intros [].
    refine {| mind_entry_typename := ind_name;
              mind_entry_arity := remove_arity decl.(ind_npars) ind_type;
              mind_entry_template := false;
              mind_entry_consnames := _;
              mind_entry_lc := _;
            |}.
    exact (List.map (fun x => fst (fst x)) ind_ctors).
    exact (List.map (fun x => remove_arity decl.(ind_npars)
                                                (snd (fst x))) ind_ctors).
Defined.


Section TemplateMonad.
  Import MonadNotation.

  Definition monad_iteri {T} `{Monad T} {A} (f: nat -> A -> T unit) l :=
    monad_map_i f l ;; ret tt.

  (** [extract_uniq l fail_msg] returns x if l = [x] or fails with fail_msg *)
  Definition extract_uniq {A} (l :list A) (fail_msg:string) : TemplateMonad A :=
    match l with | (x :: nil)%list => ret x | _ => tmFail fail_msg end.

  Definition get_inductive (id:ident): TemplateMonad inductive :=
    t <- tmAbout id ;;
    match t with
    | Some (IndRef ind) => ret ind
    | _ => tmFail ("The ident " ++ id ++ " does not refer to an existing inductive ")
    end.

  Definition get_const (id:ident) : TemplateMonad kername :=
    t <- tmAbout id ;;
    match t with
    | Some (ConstRef name) => ret name
    | _ => tmFail ("The ident " ++ id ++ " does not refer to an existing constant")
    end.

  Definition assertTM (b:bool) : TemplateMonad unit :=
    if b then tmFail "assertion failed" else ret tt.

  (** [def_kername id id_kername] looks up the kernel name of id
      and define a constant with name id_kername to it;
      fails if there is no associated kernel name*)
  Definition def_kername (id id_kername:ident) : TemplateMonad unit :=
    globref <- tmAbout id ;;
    kername <- match globref with
              | Some (ConstRef kn) => ret kn
              | Some (IndRef ind) => tmEval all (inductive_mind ind)
              | Some (ConstructRef _ _) =>
                tmFail ("Found a constructor associated to "++ id ++", no associated kername")
              | None => tmFail ("No global reference associated to "++id)
              end ;;
    qkername <- tmQuote kername ;;
    tmMkDefinition id_kername qkername.
End TemplateMonad.
