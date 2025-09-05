(* A bitwise characterisation of bv_swrap (and hence sign extension). *)

From Coq Require Import ZArith ZifyNat ZifyBool.
From stdpp Require Import base.
From stdpp.bitvector Require Import definitions.
From stdpp Require Import options.

Local Open Scope Z.

Lemma opp_pow2_bits n i :
  0 ≤ n →
  Z.testbit (-(2 ^ n)) i = (n <=? i).
Proof.
  intros ?.
  destruct (Z_le_gt_dec 0 i) as [|].
  - destruct (Ztrichotomy i n) as [|[|]].
    + rewrite Z.testbit_eqb by done.
      replace n with ((n - i) + i) by lia.
      rewrite Z.pow_add_r by lia.
      rewrite Z.div_opp_l_z; [|lia | apply Z.mod_mul; lia].
      rewrite Z.div_mul by lia.
      replace (n - i) with (Z.succ (n - i - 1)) by lia.
      rewrite Z.pow_succ_r, Z.mul_comm by lia.
      rewrite Z.mod_opp_l_z; [|lia| apply Z.mod_mul; lia].
      lia.
    + subst.
      rewrite Z.testbit_eqb by done.
      rewrite Z.div_opp_l_z; [|lia | apply Z.mod_same; lia].
      rewrite Z.div_same by lia.
      lia.
    + rewrite Z.testbit_eqb by done.
      replace i with ((i - n) + n) at 1 by lia.
      rewrite Z.pow_add_r by lia.
      replace (2 ^ n) with (1 * 2 ^ n) at 1 by lia.
      rewrite Z.div_opp_l_nz; [ |lia| ]. 2: { rewrite Z.mul_mod_distr_r by lia. rewrite Z.mod_1_l; [lia|]. apply Z.pow_gt_1; lia. }
      rewrite Z.div_mul_cancel_r by lia.
      rewrite Z.div_1_l. 2: { apply Z.pow_gt_1; lia. }
      lia.
  - rewrite Z.testbit_neg_r; lia.
Qed.

Lemma top_sub_pow2_bit m n :
  0 ≤ n →
  0 ≤ m →
  Z.testbit (m - 2 ^ n) n = negb (Z.testbit m n).
Proof.
  rewrite <- Z.add_opp_r.
  intros ?; revert m.

  apply Z.le_ind with (n := 0) (m := n); [ | | | done].
  - intros x y ->; reflexivity.
  - intros m ?.
    rewrite Z.add_bit0.
    change (Z.testbit (- 2 ^ 0) 0) with true.
    by rewrite xorb_true_r.
  - clear dependent n.
    intros n ? IH m ?.

    assert (MB : ∃ m' b, 0 ≤ m' /\ m = 2 * m' + Z.b2z b). {
      rewrite (Z.div_mod m 2); [| discriminate].
      exists (m `div` 2), (Z.testbit m 0).
      rewrite Z.bit0_mod.
      lia.
    }
    destruct MB as [m' [b [? ->]]].

    rewrite Z.pow_succ_r by done.
    replace (2 * m' + Z.b2z b + - (2 * 2 ^ n)) with (2 * (m' + - (2 ^ n)) + Z.b2z b) by lia.
    rewrite !Z.testbit_succ_r by done.
    by apply IH.
Qed.

Lemma low_sub_pow2_bit m n i :
  0 ≤ n →
  0 ≤ m →
  0 ≤ i < n →
  Z.testbit (m - 2 ^ n) i = Z.testbit m i.
Proof.
  rewrite <- Z.add_opp_r.
  intros N M [Hi I]. revert m n N M I.
  apply Z.le_ind with (n := 0) (m := i).
  * intros x y EQ; subst. reflexivity.
  * intros m n ? ? ?.
    rewrite Z.add_bit0, opp_pow2_bits by lia.
    replace (n <=? 0) with false by lia.
    by apply xorb_false_r.
  * intros i' ? IH m n ?? I.
    rewrite (Z.div_mod (m + - 2 ^ n) 2) by lia.
    rewrite <- Z.bit0_mod.
    rewrite Z.testbit_succ_r by done.
    replace (- 2 ^ n) with ((- 2 ^ (n - 1)) * 2). 2: {
      rewrite Z.mul_opp_l.
      f_equal.
      rewrite Z.mul_comm.
      rewrite <- Z.add_1_r in I.
      by rewrite <- Z.pow_succ_r; [f_equal;lia|lia].
    }
    rewrite Z_div_plus by lia.

    rewrite (Z.div_mod m 2) at 2 by lia.
    rewrite <- Z.bit0_mod.
    rewrite Z.testbit_succ_r by done.
    apply IH; lia.
  * assumption.
Qed.

Lemma high_sub_pow2_bit m n i :
  0 ≤ n →
  0 ≤ m < 2 ^ (Z.succ n) →
  0 ≤ i →
  Z.testbit (m - 2 ^ n) (n + i) = negb (Z.testbit m n).
Proof.
  intros N M I.
  rewrite <- top_sub_pow2_bit by lia.
  rewrite Z.pow_succ_r in M by done.
  rewrite !(proj1 (Z.bounded_iff_bits n (m - 2 ^ n) N)) by lia.
  done.
Qed.

Lemma low_add_pow2_bit m n i :
  0 ≤ n →
  0 ≤ i < n →
  Z.testbit (m + 2 ^ n) i = Z.testbit m i.
Proof.
  intros N [I I'].
  revert m n N I'.
  apply Z.le_ind with (n := 0) (m := i).
  * intros x y ->. reflexivity.
  * intros m n N ?.
    rewrite Z.add_bit0.
    rewrite Z.pow2_bits_false by lia.
    by rewrite xorb_false_r.
  * clear i I.
    intros i I IH m n N ?.
    rewrite <- !Z.div2_bits by done.
    rewrite <- Z.pow_pred_r by lia.
    rewrite Z.mul_comm.
    rewrite Z.div_add by done.
    apply IH; by lia.
  * assumption.
Qed.

Lemma top_add_pow2_bit m n :
  0 ≤ n →
  Z.testbit (m + 2 ^ n) n = negb (Z.testbit m n).
Proof.
  intro N. revert m.
  apply Z.le_ind with (n := 0) (m := n); [ | | | done].
  - intros x y ->; reflexivity.
  - intros m.
    rewrite Z.add_bit0.
    change (Z.testbit (- 2 ^ 0) 0) with true.
    by rewrite xorb_true_r.
  - clear dependent n.
    intros n ? IH m.

    assert (MB : ∃ m' b, m = 2 * m' + Z.b2z b). {
      rewrite (Z.div_mod m 2); [| discriminate].
      exists (m `div` 2), (Z.testbit m 0).
      rewrite Z.bit0_mod.
      lia.
    }
    destruct MB as [m' [b ->]].

    rewrite Z.pow_succ_r by done.
    replace (2 * m' + Z.b2z b + 2 * 2 ^ n) with (2 * (m' + 2 ^ n) + Z.b2z b) by lia.
    rewrite !Z.testbit_succ_r by done.
    by apply IH.
Qed.


Lemma bv_swrap_spec n (z i : Z):
  0 ≤ i →
  Z.testbit (bv_swrap n z) i = if bool_decide (i < Z.of_N n-1) then Z.testbit z i else Z.testbit z (Z.of_N n-1).
Proof.
  destruct (decide (0 < n)%N).
  - intros ?.
    unfold bv_swrap, bv_half_modulus, bv_modulus.
    replace (2 ^ Z.of_N n `div` 2) with (2 ^ (Z.of_N n - 1)). 2: {
      rewrite Z.pow_sub_r; lia.
    }
    case_bool_decide as Hi.
    + rewrite low_sub_pow2_bit; [ | lia |  apply bv_wrap_in_range | done ].
      rewrite bv_wrap_spec_low by lia.
      apply low_add_pow2_bit; by lia.
    + destruct (decide (i = Z.of_N n - 1)) as [Ieq | Ineq].
      * rewrite Ieq.
        rewrite top_sub_pow2_bit; [ | lia | apply bv_wrap_in_range ].
        rewrite bv_wrap_spec_low by lia.
        rewrite top_add_pow2_bit by lia.
        by apply negb_involutive.
      * replace i with ((Z.of_N n - 1) + (i - (Z.of_N n - 1))) by lia.
        rewrite high_sub_pow2_bit; [ | lia | | lia ]. 2: {
          replace (Z.succ (Z.of_N n - 1)) with (Z.of_N n) by lia.
          apply bv_wrap_in_range.
        }
        rewrite bv_wrap_spec_low by lia.
        rewrite top_add_pow2_bit by lia.
        by apply negb_involutive.
  - intros.
    replace n with 0%N by lia.
    rewrite bool_decide_eq_false_2 by lia.
    unfold bv_swrap, bv_half_modulus, bv_modulus.
    replace (2 ^ Z.of_N 0 `div` 2) with 0 by lia.
    rewrite Z.add_0_r, Z.sub_0_r.
    unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 0) with 1.
    rewrite Z.mod_1_r.
    by rewrite Z.bits_0, Z.testbit_neg_r.
Qed.

