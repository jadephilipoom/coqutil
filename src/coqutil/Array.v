Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Byte.
Require Import coqutil.Lift1Prop.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Separation.
Require Import coqutil.Map.SeparationLogic.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Word.LittleEndianList.
Require Import coqutil.Tactics.Tactics.

Section Bytes.
  Context {width} {word : word.word width} {mem : map.map word byte}.

  (* TODO: move to separation? or Bytes file *)
  Fixpoint bytes
             (elems : list byte)
             (addr : word)
    : mem -> Prop :=
    match elems with
    | nil => emp True
    | e :: elems => sep (ptsto addr e)
                        (bytes elems (word.add addr (word.of_Z 1)))
    end.

  Definition word_to_bytes (w : word) : list byte :=
    le_split (Z.to_nat (width / 8)) (word.unsigned w).
  Definition word_from_bytes (bs : list byte) : word :=
    word.of_Z (le_combine bs).

  Section Proofs.
    Context {word_ok : word.ok word} {mem_ok : map.ok mem}
            (width_multiple_of_8 : (width mod 8 = 0)%Z).
    Add Ring wring : (word.ring_theory (word := word)).
    Lemma bytes_nil addr :
      iff1 (bytes nil addr) (emp True).
    Proof using Type. reflexivity. Qed.
    Lemma bytes_cons b bs addr :
      iff1 (bytes (b :: bs) addr)
           (sep (ptsto addr b) (bytes bs (word.add addr (word.of_Z 1)))).
    Proof using Type. reflexivity. Qed.
    Lemma bytes_app bs1 bs2 :
      forall addr,
        iff1
          (bytes (bs1 ++ bs2) addr)
          (sep (bytes bs1 addr)
               (bytes bs2 (word.add addr (word.of_Z (Z.of_nat (length bs1)))))).
    Proof using word_ok mem_ok.
      induction bs1; cbn [bytes length List.app]; intros.
      { rewrite sep_emp_True_l, word.add_0_r. reflexivity. }
      { rewrite IHbs1.
        lazymatch goal with
        | |- iff1 ?lhs ?rhs =>
          lazymatch lhs with
          | context [bytes bs2 ?laddr] =>
            lazymatch rhs with
            | context [bytes bs2 ?raddr] =>
              replace laddr with raddr; [ ecancel | ]
            end
          end
        end.
        replace (Z.of_nat (S (length bs1))) with (1 + Z.of_nat (length bs1))%Z
          by lia.
        rewrite word.ring_morph_add. ring.
      }
    Qed.

    Lemma word_from_bytes_to_bytes w :
      word_from_bytes (word_to_bytes w) = w.
    Proof using word_ok width_multiple_of_8.
      cbv [word_from_bytes word_to_bytes]; intros.
      pose proof (word.unsigned_range w). pose proof word.width_pos.
      pose proof Z_div_exact_full_2 width 8 ltac:(lia) ltac:(lia).
      pose proof (Z.div_pos width 8 ltac:(lia) ltac:(lia)).
      rewrite le_combine_split. rewrite Z2Nat.id by lia.
      lazymatch goal with
      | |- context [(word.unsigned w mod 2 ^ ?x)%Z] =>
        replace x with width by lia
      end.
      rewrite Z.mod_small by lia; apply word.of_Z_unsigned.
    Qed.

    Lemma word_to_bytes_from_bytes bs :
      length bs = Z.to_nat (width / 8) ->
      word_to_bytes (word_from_bytes bs) = bs.
    Proof using word_ok width_multiple_of_8.
      cbv [word_from_bytes word_to_bytes]; intros.
      pose proof word.width_pos. pose proof le_combine_bound bs.
      pose proof (Z.div_pos width 8 ltac:(lia) ltac:(lia)).
      pose proof Z_div_exact_full_2 width 8 ltac:(lia) ltac:(lia).
      lazymatch goal with
      | H : (0 <= le_combine bs < 2 ^ ?x)%Z |- _ =>
        replace x with width in H by lia
      end.
      rewrite word.unsigned_of_Z_nowrap by lia.
      apply split_le_combine'. lia.
    Qed.

    Lemma length_word_to_bytes w :
      length (word_to_bytes w) = Z.to_nat (width / 8).
    Proof using Type. apply length_le_split. Qed.
  End Proofs.
End Bytes.

Section Array.
  Context {elem : Type}
          (elem_to_bytes : elem -> list byte)
          (elem_from_bytes : list byte -> elem)
          (elem_size : nat).

  Definition array_to_bytes (arr : list elem) : list byte :=
    concat (map elem_to_bytes arr).
  Definition array_from_bytes (bs : list byte) : list elem :=
    map elem_from_bytes (chunk elem_size bs).

  Section Proofs.
    Context
      (elem_from_bytes_to_bytes :
         forall e, elem_from_bytes (elem_to_bytes e) = e)
      (elem_to_bytes_from_bytes :
         forall bs,
           length bs = elem_size ->
           elem_to_bytes (elem_from_bytes bs) = bs)
      (length_elem_to_bytes :
         forall e, length (elem_to_bytes e) = elem_size)
      (elem_size_nonzero : elem_size <> 0).

    Lemma array_to_bytes_nil : array_to_bytes nil = nil.
    Proof using Type. reflexivity. Qed.

    Lemma array_to_bytes_cons e arr :
      array_to_bytes (e :: arr) = elem_to_bytes e ++ array_to_bytes arr.
    Proof using Type. reflexivity. Qed.

    Lemma array_to_bytes_app arr1 arr2 :
      array_to_bytes (arr1 ++ arr2) = array_to_bytes arr1 ++ array_to_bytes arr2.
    Proof using Type.
      cbv [array_to_bytes]. rewrite map_app. apply concat_app.
    Qed.

    Lemma array_from_bytes_nil : array_from_bytes nil = nil.
    Proof using Type. reflexivity. Qed.

    Lemma array_from_bytes_step bs1 bs2 :
      length bs1 = elem_size ->
      array_from_bytes (bs1 ++ bs2) = (elem_from_bytes bs1) :: array_from_bytes bs2.
    Proof using elem_size_nonzero.
      intros; cbv [array_from_bytes].
      rewrite chunk_app_chunk by lia.
      apply map_cons.
    Qed.

    Lemma length_array_to_bytes arr :
      length (array_to_bytes arr) = length arr * elem_size.
    Proof using length_elem_to_bytes.
      clear elem_size_nonzero. (* otherwise lia will use it unnecessarily *)
      induction arr; intros; [ rewrite array_to_bytes_nil; cbn [length]; lia | ].
      rewrite array_to_bytes_cons, length_cons, length_app, length_elem_to_bytes.
      rewrite IHarr. lia.
    Qed.

    Lemma length_array_to_bytes_mod arr :
      length (array_to_bytes arr) mod elem_size = 0.
    Proof using length_elem_to_bytes.
      rewrite length_array_to_bytes. apply Nat.Div0.mod_mul.
    Qed.

    Lemma length_array_from_bytes bs :
      length (array_from_bytes bs) = Nat.div_up (length bs) elem_size.
    Proof using elem_size_nonzero.
      cbv [array_from_bytes]. intros.
      rewrite length_map, length_chunk by lia.
      reflexivity.
    Qed.

    Lemma array_from_bytes_to_bytes arr :
      array_from_bytes (array_to_bytes arr) = arr.
    Proof using length_elem_to_bytes elem_from_bytes_to_bytes elem_size_nonzero.
      induction arr.
      { rewrite array_to_bytes_nil, array_from_bytes_nil. reflexivity. }
      { rewrite array_to_bytes_cons, array_from_bytes_step by auto.
        rewrite IHarr, elem_from_bytes_to_bytes. reflexivity. }
    Qed.

    Lemma array_to_bytes_from_bytes bs :
      length bs mod elem_size = 0 ->
      array_to_bytes (array_from_bytes bs) = bs.
    Proof using length_elem_to_bytes elem_to_bytes_from_bytes elem_size_nonzero.
      intro Hmod. apply Nat.Lcm0.mod_divide in Hmod. destruct Hmod as [n ?].
      generalize dependent bs; induction n; intros.
      { destruct bs; cbn [length] in *; [ | lia ].
        rewrite array_from_bytes_nil, array_to_bytes_nil. reflexivity. }
      { rewrite <-(firstn_skipn elem_size bs).
        rewrite array_from_bytes_step by (rewrite length_firstn; lia).
        rewrite array_to_bytes_cons.
        rewrite elem_to_bytes_from_bytes by (rewrite length_firstn; lia).
        rewrite IHn by (rewrite length_skipn; lia).
        reflexivity. }
    Qed.
  End Proofs.
End Array.
