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
