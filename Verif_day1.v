Require Import VST.floyd.proofauto.

Require Import AOC.day1.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition sum_int : list Z -> Z := fold_right Z.add 0.

Lemma sum_int_app :
  forall a b, sum_int (a ++ b) = sum_int a + sum_int b.
Proof.
  intros. induction a; simpl; lia.
Qed.

(* Specification for 'sum' *)
Definition sum_spec : ident * funspec :=
DECLARE _sum
  WITH buf: val, sh : share, contents : list Z, size : Z
  PRE [ tptr tuint, tint ]
    PROP (readable_share sh; 0 <= size <= Int.max_signed;
          Forall (fun x => 0 <= x <= Int.max_unsigned) contents)
    PARAMS (buf; Vint (Int.repr size))
    SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) buf)
   POST [ tuint ]
    PROP () RETURN (Vint (Int.repr (sum_int contents)))
    SEP (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) buf).

Print Z.lt.
Print Decidable.decidable.

Fixpoint count_increasing (xs : list Z) : Z :=
  match xs with
  | [] => 0
  | (x :: []) => 0
  | (x :: (y :: _) as xs) =>
      if x <? y then 1 + (count_increasing xs) else (count_increasing xs)
  end.

Lemma count_increasing_empty :
  count_increasing [] = 0.
Proof.
  reflexivity.
Qed.

(* Counterexample: xs = [200]
                   i = 1
 *)

(* Terrible proof! *)
Lemma count_increasing_gt :
  forall i xs, 1 <= i < Zlength xs -> Znth (i - 1) xs < Znth i xs -> count_increasing (sublist 0 (i + 1) xs) = count_increasing (sublist 0 i xs) + 1.
Proof.
  intros i xs bounded le.
  rewrite 2 sublist_firstn.
  induction xs as [| x xs IH ].
    - list_solve.
    - induction xs as [| y xs _].
      + list_solve.
      + admit.
Admitted.

Lemma count_increasing_le :
  forall i xs, Znth (i - 1) xs >= Znth i xs -> count_increasing (sublist 0 (i + 1) xs) = count_increasing (sublist 0 i xs).
Proof.
Admitted.

(* Specification for 'count_increasing' *)
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


Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]  
     PROP() 
     RETURN (Vint (Int.repr 0))
     SEP(TT).

Definition Gprog := [sum_spec; count_increasing_spec].

Lemma body_count_increasing: semax_body Vprog Gprog f_count_increasing count_increasing_spec.
Proof.
  start_function.
  (* count = 0; *)
  forward.
  (* last = depths[0]; *)
  (* We need to ensure that the index is valid. *)
  assert_PROP (0 < Zlength contents). {
    entailer!.
    list_solve.
  }
  forward.
  (* i = 1; *)
  forward.
  forward_while
    (EX i: Z,
     PROP (1 <= i <= size)
     LOCAL (temp _depths depths;
            temp _i (Vint (Int.repr i));
            temp _n (Vint (Int.repr size));
            temp _last (Vint (Int.repr (Znth (Z.sub i 1) contents)));
            temp _count (Vint (Int.repr (count_increasing (sublist 0 i contents)))))
    SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) depths)).
  - (* For our base case, we need to show that count_increasing on depths[1..1] is 0. *)
    Exists 1.
    entailer!;
    autorewrite with sublist in *|-.
    rewrite (sublist_one 0); simpl; auto.
    + reflexivity.
    + apply H.
  - entailer!.
  -
    (* while(i < n) *)
    assert_PROP (Zlength contents = size). {
      entailer!.
      list_solve.
    }
    forward.
    Fail forward.
    forward_if (PROP ()
                LOCAL (temp _count (Vint (Int.repr (count_increasing (sublist 0 (i + 1) contents))));
                       temp _last (Vint (Int.repr (Znth (Z.sub i 1) contents)));
                       temp _depths depths;
                       temp _n (Vint (Int.repr size));
                       temp _i (Vint (Int.repr i))
                      )
                SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) depths)).
    + forward.
      entailer!.
      (* What we need to prove here is that count_increasing(depths[1..i + 1]) = count_increasing(depths[1..i] + 1),
         given that depths[i] > depths[i + 1]. *)
      f_equal. f_equal.
      apply count_increasing_gt.
      (* We know that Int.unsigned (Int.repr (Znth (i - 1) contents)) < Int.unsigned (Int.repr (Znth i contents)),
         So it's a simple matter of munging some stuff around to get it to work.
       *)
      rewrite 2 Int.unsigned_repr in *|-.
      assumption.
      all: apply Forall_Znth; assumption || lia.
    + forward.
      entailer!.
      (* What we need to prove here is that count_increasing(depths[1..i + 1]) = count_increasing(depths[1..i]),
         given that depths[i] <= depths[i - 1]. *)
      f_equal. f_equal.
      apply count_increasing_le.
      rewrite 2 Int.unsigned_repr in *|-.
      assumption.
      all: apply Forall_Znth; assumption || lia.
    + (* last = depths[i]; *)
      forward.
      (* i++; *)
      forward.
      Exists (i+1).
      entailer!.
      repeat f_equal. lia.
  - forward.
    entailer!.
    repeat f_equal.
    list_solve.
Qed.

Lemma body_sum: semax_body Vprog Gprog f_sum sum_spec.
  Proof.
    start_function.
    forward.
    forward.
    forward_while
      (EX i: Z,
        PROP  (0 <= i <= size)
        LOCAL (temp _buf buf;
               temp _i (Vint (Int.repr i));
               temp _n (Vint (Int.repr size));
               temp _count (Vint (Int.repr (sum_int (sublist 0 i contents)))))
        SEP   (data_at sh (tarray tuint size) (map Vint (map Int.repr contents)) buf)).
    - Exists 0.
      entailer!.
    - entailer!.
    - assert_PROP (Zlength contents = size). {
        entailer!.
        list_solve.
      }
      forward.
      forward.
      forward.
      Exists (i+1).
      entailer!.
      f_equal. f_equal.
      rewrite (sublist_split 0 i (i+1)) by lia.
      rewrite sum_int_app. rewrite (sublist_one i) by lia.
      simpl. lia.
    - forward.
      entailer!.
      autorewrite with sublist in *|-.
      autorewrite with sublist.
      reflexivity.
  Qed.
