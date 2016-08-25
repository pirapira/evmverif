Require Import NArith.

Module Type Word.

  Parameter word : Type.

  Parameter word_eq : word -> word -> bool.
  Parameter word_add : word -> word -> word.
  Parameter word_sub : word -> word -> word.
  Parameter word_mul : word -> word -> word.
  Parameter word_mod : word -> word -> word.
  Parameter word_iszero : word -> bool.
  (* TODO: state correctness of word_iszero *)
  Parameter word_smaller : word -> word -> bool.
  Parameter word_smaller_or_eq : word -> word -> bool.
  Parameter word_of_N : N -> word.
  Parameter N_of_word : word -> N.

  Open Scope N_scope.
  Parameter N_of_word_of_N :
    (* TODO: This 10000 is a bit arbitrary. *)
  forall (n : N), n < 10000 -> N_of_word (word_of_N n) = n.

  Parameter word_of_nat : nat -> word.

  (* TODO: turn these into definitions *)
  Definition word_zero : word := word_of_N 0.
  Definition word_one : word := word_of_N 1.

  Parameter byte : Type.
  Parameter address : Type.
  Parameter address_of_word : word -> address.
  Parameter word_of_address : address -> word.
  Parameter address_eq : address -> address -> bool.
  Parameter address_eq_refl : forall (a : address), address_eq a a = true.

  Parameter word_nth_byte : word -> nat -> byte.

  (* list of bytes [a; b; c] as (a * 256 + b) * 256 + c *)
  Parameter word_of_bytes : list byte -> word.

  Require Import Coq.Lists.List.
  Import ListNotations.
  Open Scope list_scope.

  Parameter words_of_nth_bytes :
    forall w b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31,
    b0 = word_nth_byte w 0 ->
    b1 = word_nth_byte w 1 ->
    b2 = word_nth_byte w 2 ->
    b3 = word_nth_byte w 3 ->
    b4 = word_nth_byte w 4 ->
    b5 = word_nth_byte w 5 ->
    b6 = word_nth_byte w 6 ->
    b7 = word_nth_byte w 7 ->
    b8 = word_nth_byte w 8 ->
    b9 = word_nth_byte w 9 ->
    b10 = word_nth_byte w 10 ->
    b11 = word_nth_byte w 11 ->
    b12 = word_nth_byte w 12 ->
    b13 = word_nth_byte w 13 ->
    b14 = word_nth_byte w 14 ->
    b15 = word_nth_byte w 15 ->
    b16 = word_nth_byte w 16 ->
    b17 = word_nth_byte w 17 ->
    b18 = word_nth_byte w 18 ->
    b19 = word_nth_byte w 19 ->
    b20 = word_nth_byte w 20 ->
    b21 = word_nth_byte w 21 ->
    b22 = word_nth_byte w 22 ->
    b23 = word_nth_byte w 23 ->
    b24 = word_nth_byte w 24 ->
    b25 = word_nth_byte w 25 ->
    b26 = word_nth_byte w 26 ->
    b27 = word_nth_byte w 27 ->
    b28 = word_nth_byte w 28 ->
    b29 = word_nth_byte w 29 ->
    b30 = word_nth_byte w 30 ->
    b31 = word_nth_byte w 31 ->
    word_of_bytes
    [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15; b16;
     b17; b18; b19; b20; b21; b22; b23; b24; b25; b26; b27; b28; b29; b30; b31] =
    w.

  Parameter event : Type. (* logged events *)


  (* These depends on the choice of word.
   * In the concrete case, these can be MSet or FSet.
   *)
  Parameter memory_state : Type. (* For now I don't use the memory *)
  Parameter empty_memory : memory_state.
  Parameter cut_memory : word -> word -> memory_state -> list byte.
  Parameter cut_memory_zero_nil :
    forall start m, cut_memory start word_zero m = nil.

  Parameter storage : Type.
  Parameter storage_load : word -> storage -> word.
  Arguments storage_load idx s /.

  Parameter storage_store : word (* idx *) -> word (* value *) -> storage -> storage.
  Arguments storage_store idx v orig /.

  Parameter empty_storage : storage.
  Parameter empty_storage_empty : forall idx : word,
      is_true (word_iszero (storage_load idx empty_storage)).

End Word.
