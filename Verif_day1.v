Require Import VST.floyd.proofauto.

Require Import AOC.day1.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

(* day1.c

  unsigned count_increasing(unsigned depths[], int n) {
    int i; unsigned count; unsigned last;
    count = 0;
    last = depths[0];
    i = 1;
    while(i < n) {
      if (last < depths[i]) {
        count++;
      }
      last = depths[i];
      i++;
    }
    return count;
  }

*)

(* Functional Specifications *)

Fixpoint count_increasing (xs : list Z) : Z :=
  match xs with
  | [] => 0
  | (x :: []) => 0
  | (x :: (y :: _) as xs) =>
      if x <? y then 1 + (count_increasing xs) else (count_increasing xs)
  end.

Lemma count_increasing_app_lt :
  forall xs x y ys, x < y ->
                    count_increasing ((xs ++ [x]) ++ y :: ys) = count_increasing (xs ++ [x]) + count_increasing (y :: ys) + 1.
Proof.
  intros xs x y ys lt.
  induction xs as [| a xs ih ].
  - simpl.
    rewrite (proj2 (Z.ltb_lt x y) lt).
    lia.
  - induction xs as [| b xs _ ].
    + simpl.
      rewrite (proj2 (Z.ltb_lt x y) lt).
      induction (Z.lt_decidable a x).
      * rewrite (proj2 (Z.ltb_lt a x) H).
        lia.
      * assert (a <? x = false) as a_ge_x. {
          lia.
        }
        rewrite a_ge_x.
        lia.
    + simpl.
      induction (Z.lt_decidable a b).
      * rewrite (proj2 (Z.ltb_lt a b) H).
        simpl in ih.
        rewrite ih.
        lia.
      * assert (a <? b = false) as a_ge_b. {
          lia.
        }
        rewrite a_ge_b.
        simpl in ih.
        rewrite ih.
        lia.
Qed.

Lemma count_increasing_app_ge :
  forall xs x y ys, x >= y ->
                    count_increasing ((xs ++ [x]) ++ y :: ys) = count_increasing (xs ++ [x]) + count_increasing (y :: ys).
Proof.
  intros xs x y ys ge.
  assert (x <? y = false) as not_lt. {
    lia.
  }
  induction xs as [| a xs ih ].
  - simpl.
    rewrite not_lt.
    lia.
  - induction xs as [| b xs _ ].
    + simpl.
      rewrite not_lt.
      induction (Z.lt_decidable a x).
      * rewrite (proj2 (Z.ltb_lt a x) H).
        lia.
      * assert (a <? x = false) as a_ge_x. {
          lia.
        }
        rewrite a_ge_x.
        lia.
    + simpl.
      induction (Z.lt_decidable a b).
      * rewrite (proj2 (Z.ltb_lt a b) H).
        simpl in ih.
        rewrite ih.
        lia.
      * assert (a <? b = false) as a_ge_b. {
          lia.
        }
        rewrite a_ge_b.
        simpl in ih.
        rewrite ih.
        lia.
Qed.

Lemma count_increasing_last_lt :
  forall xs x, 1 <= Zlength xs ->
               Znth (Zlength xs - 1) xs < x ->
               count_increasing (xs ++ [x]) = count_increasing xs + 1.
  intros xs x bound lt.
  induction xs as [| y xs ih' ] using rev_ind.
  - list_solve.
  - About assert.
    cut (count_increasing ((xs ++ [y]) ++ x :: []) = count_increasing (xs ++ [y]) + count_increasing (x :: []) + 1). {
      intro.
      simpl in H.
      lia.
    }
    apply count_increasing_app_lt.
    autorewrite with sublist in *|-.
    exact lt.
Qed.

Lemma count_increasing_last_ge :
  forall xs x, 1 <= Zlength xs ->
               Znth (Zlength xs - 1) xs >= x ->
               count_increasing (xs ++ [x]) = count_increasing xs.
  intros xs x bound ge.
  induction xs as [| y xs ih' ] using rev_ind.
  - list_solve.
  - About assert.
    cut (count_increasing ((xs ++ [y]) ++ x :: []) = count_increasing (xs ++ [y]) + count_increasing (x :: [])). {
      intro.
      simpl in H.
      lia.
    }
    apply count_increasing_app_ge.
    autorewrite with sublist in *|-.
    exact ge.
Qed.

Lemma count_increasing_sublist_lt :
  forall i xs, 1 <= i < Zlength xs ->
               Znth (i - 1) xs < Znth i xs ->
               count_increasing (sublist 0 (i + 1) xs) = count_increasing (sublist 0 i xs) + 1.
Proof.
  intros i xs bounded lt.
  rewrite (sublist_split 0 i (i+1)) by lia.
  rewrite (sublist_one i) by lia.
  induction xs as [| x xs ih ] using rev_ind.
  - list_solve.
  - rewrite sublist_app1 by list_solve.
    induction (Z.lt_decidable i (Zlength xs)).
    + autorewrite with sublist in *|-*.
      apply ih.
      lia.
      exact lt.
    + assert (i = Zlength xs) as index_last. {
        list_solve.
      }
      rewrite index_last.
      rewrite index_last in lt.
      autorewrite with sublist in *|-*.
      apply count_increasing_last_lt; lia.
Qed.

Lemma count_increasing_sublist_ge :
  forall i xs, 1 <= i < Zlength xs ->
               Znth (i - 1) xs >= Znth i xs ->
               count_increasing (sublist 0 (i + 1) xs) = count_increasing (sublist 0 i xs).
Proof.
  intros i xs bounded ge.
  rewrite (sublist_split 0 i (i+1)) by lia.
  rewrite (sublist_one i) by lia.
  induction xs as [| x xs ih ] using rev_ind.
  - list_solve.
  - rewrite sublist_app1 by list_solve.
    induction (Z.lt_decidable i (Zlength xs)).
    + autorewrite with sublist in *|-*.
      apply ih; lia.
    + assert (i = Zlength xs) as index_last. {
        list_solve.
      }
      rewrite index_last.
      rewrite index_last in ge.
      autorewrite with sublist in *|-*.
      apply count_increasing_last_ge; lia.
Qed.



Definition count_increasing_spec : ident * funspec :=
DECLARE _sum
  WITH depths: val, sh: share, contents: list Z, size: Z
  PRE [ tptr tuint, tint ]
  PROP (readable_share sh; 1 <= size <= Int.max_signed;
        Forall (fun x => 0 <= x <= Int.max_unsigned) contents)
    PARAMS (depths; Vint (Int.repr size))
    SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) depths)
   POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (count_increasing contents)))
    SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) depths).

Definition Gprog := [count_increasing_spec].

Lemma body_count_increasing: semax_body Vprog Gprog f_count_increasing count_increasing_spec.
Proof.
  start_function.
  (* count = 0; *)
  forward.
  (* last = depths[0]; *)
  (* First, we have to show that n - 1 is a valid index. *)
  assert_PROP (0 < Zlength contents) as last_in_bounds. {
    entailer!.
    list_solve.
  }
  forward.
  (* i = 1; *)
  forward.
  (* while (i >= 0) *)
  forward_while
    (EX i: Z,
     PROP (1 <= i <= size)
     LOCAL (temp _depths depths;
            temp _i (Vint (Int.repr i));
            temp _n (Vint (Int.repr size));
            temp _last (Vint (Int.repr (Znth (i - 1) contents)));
            temp _count (Vint (Int.repr (count_increasing (sublist 0 i contents)))))
    SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) depths)).
  - (* Check to see that the invariant holds before we enter the loop for the first time. *)
    Exists 1.
    entailer!.
    f_equal. f_equal.
    rewrite (sublist_one 0) by list_solve.
    reflexivity.
  - (* Check to see that the loop condition won't crash. *)
    entailer!.
  - (* Check to see that the loop invariant holds at the end of the loop. *)
    (* if (last < depths[i]) *)
    (* First, we have to make sure that the array access is in bounds. *)
    assert_PROP (i < Zlength contents). {
      entailer!.
      list_solve.
    }
    forward.
    forward_if 
      (PROP ()
       LOCAL (temp _depths depths;
             temp _i (Vint (Int.repr i));
             temp _n (Vint (Int.repr size));
             temp _last (Vint (Int.repr (Znth (i - 1) contents)));
             temp _count (Vint (Int.repr (count_increasing (sublist 0 (i + 1) contents)))))
      SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) depths)).
    + (* Ensure that the if postcondition holds in the "true" branch. *)
      (* count++; *)
      forward.
      entailer!.
      f_equal. f_equal.
      rewrite 2 Int.unsigned_repr in *|-.
      rewrite (count_increasing_sublist_lt) by list_solve. {
        reflexivity.
      }
      all: apply Forall_Znth; assumption || lia.
    + forward.
      entailer!.
      f_equal. f_equal.
      rewrite 2 Int.unsigned_repr in *|-.
      rewrite (count_increasing_sublist_ge) by list_solve. {
        reflexivity.
      }
      all: apply Forall_Znth; assumption || lia.
    + (* Ensure that the if postcondition is strong enough to entail the loop invariant. *)
      (* last = depths[i]; *)
      forward.
      (* i++; *)
      forward.
      (* We've reached the end of the loop! Time to show that the invariant holds. *)
      Exists (i+1).
      entailer!.
      f_equal. f_equal. f_equal.
      lia.
  - (* Now, we need to show that the loop invariant implies the function's poscondition. *)
    (* return count; *)
    forward.
    entailer!.
    f_equal. f_equal. f_equal.
    apply sublist_same; list_solve.
Qed.
      
