
Set Primitive Projections.

Record dprod (A:Type) (B : A -> Type) :=
    mkDprod { pr1 : A ; pr2 : B pr1 }.

Arguments pr1 {_ _} _.
Arguments pr2 {_ _} _.

Section Unbundling.
    Context A (B : A -> Type) (C : forall a, B a -> Type).

    Record T := 
        mkT { t_a : A ; t_b : B t_a ; t_c : C t_a t_b }.

    Record T_over_b := 
        mkTob { tob_a : A }.
    Record T_under_b (tob : T_over_b):=
        mkTub { tub_b : B (tob_a tob) ; tub_c : C _ tub_b }.

    Definition proj_above_b (t : T) : T_over_b :=
        mkTob (t_a t).
    Definition proj_under_b (t: T) : T_under_b (proj_above_b t) :=
        mkTub (proj_above_b t) (t_b t) (t_c t).

    (* Definition join_at_b (t' : dprod T_over_b T_under_b) : T :=
        mkT (tob_a (pr1 t')) (tub_b _ tub) (tub_c _ tub).
    

    Lemma T_split_b_and_back t :
        join_at_b (mkDprod _ _ (proj_above_b t) (proj_under_b t)) = t.
    Proof. reflexivity. Defined.

    Lemma build_T_over : forall tob tub,
        let t := join_at_b (mkDprod _ _ tob tub) in
        tob = proj_above_b t.
    Proof. reflexivity. Defined.

    Lemma build_T_under : forall tob tub,
        let t := join_at_b (mkDprod _ _ tob tub) in
        tub = proj_under_b t.
    Proof. reflexivity. Defined. *)

    Definition join_at_b (tob: T_over_b) (tub : T_under_b tob) : T :=
        mkT (tob_a tob) (tub_b _ tub) (tub_c _ tub).
    

    Lemma T_split_b_and_back t :
        join_at_b (proj_above_b t) (proj_under_b t) = t.
    Proof. reflexivity. Defined.

    Lemma build_T_over : forall tob tub,
        tob = proj_above_b (join_at_b tob tub).
    Proof. reflexivity. Defined.

    Lemma build_T_under : forall tob tub,
        tub = proj_under_b (join_at_b tob tub).
    Proof. reflexivity. Defined.

End Unbundling.
