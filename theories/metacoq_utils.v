From Coq Require Import Strings.String ssreflect ssrbool ssrfun.
From MetaCoq.Template Require Import All.

Import MonadNotation.

Definition monad_iteri {T} `{Monad T} {A} (f: nat -> A -> T unit) l :=
  monad_map_i f l ;; ret tt.

Fixpoint build_const (argtys: list term) body :=
  List.fold_right (fun ty t => tLambda nAnon ty t) body argtys.

Definition mkApps_ctx (t:term) (shift:nat) (ctx:context) :=
  let args :=
      utils.fold_left_i (fun args i decl =>
                           match decl_body decl with
                           | None => ((tRel (shift+i)) :: args)%list
                           | Some _ => args
                           end) ctx nil in
  mkApps t args.


Definition get_inductive (id:ident): TemplateMonad inductive :=
  t <- tmAbout id ;;
    match t with
    | Some (IndRef ind) => ret ind
    | _ => tmFail ("The ident " ++ id ++ " does not refer to an existing inductive ")
    end.

Definition extract_uniq {A} (l :list A) (fail_msg:string) : TemplateMonad A :=
  match l with | (x :: nil)%list => ret x | _ => tmFail fail_msg end.

Definition get_const (id:ident) : TemplateMonad kername :=
  t <- tmAbout id ;;
    match t with
    | Some (ConstRef name) => ret name
    | _ => tmFail ("The ident " ++ id ++ " does not refer to an existing constant")
    end.
