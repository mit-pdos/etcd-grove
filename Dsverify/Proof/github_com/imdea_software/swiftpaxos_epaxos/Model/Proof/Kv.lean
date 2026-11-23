/-
`fire_kv_step`: firing a fresh slot is the key-value model's step (no invariant needed: a GET or
SCAN appended leaves every key's last PUT, a PUT appended is its key's new value; a SCAN's output
over `rangeKeys (cmdOf (.scan k n))`, which is `scanKeys k n` under `inpRangeOk`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Basic

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

/-- A scan's range under `inpRangeOk` is the model's `scanKeys` (no `int64` wrap). -/
theorem rangeKeys_scan (k n : w64) (h : k.toNat + n.toNat < 2 ^ 63) :
    rangeKeys ⟨opSCAN, k, u64Le n⟩ = scanKeys k n := by
  have hk : k.toInt = (k.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
  have hkn : (k + n).toNat = k.toNat + n.toNat := by
    rw [BitVec.toNat_add]; omega
  have hkn' : (k + n).toInt = ((k.toNat + n.toNat : Nat) : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, hkn]; split <;> omega
  unfold rangeKeys scanKeys
  simp only [List.take_of_length_le (by simp [u64Le_length] : (u64Le n).length ≤ 8), u64Le_to_word]
  rw [if_pos (by simp only [sint.Z]; rw [hk, hkn']; omega)]
  simp only [sint.Z]; rw [hk, hkn']
  rw [show (((k.toNat + n.toNat : Nat) : Int) - (k.toNat : Int)).toNat + 1 = n.toNat + 1 by omega,
    show min (n.toNat + 1) (2 ^ 64 - k.toNat) = n.toNat + 1 by omega,
    List.range'_eq_map_range, List.map_map]
  refine List.map_congr_left (fun j hj => ?_)
  have hj := List.mem_range.mp hj
  apply BitVec.eq_of_toNat_eq
  simp only [Function.comp, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

/-- (stage 2) `fire_kv_step` over `kvScan w8` (statement; proof by the model prover). -/
theorem fire_kv_step' (S : Sys) (e : Slot × WCmd) (inp : KvsInput (List w8))
    (hcmd : e.2 = cmdOf inp) (hval : inpRangeOk inp)
    (hnew : e ∉ S.gexec e.2.key) :
    (kvScan w8).step S.kv inp (S.fire e).kv (Sys.outOf S.gexec e.2) := by
  have hg : (S.fire e).gexec = fun k => if Sys.touches e.2 k then S.gexec k ++ [e] else S.gexec k := by
    simp only [Sys.fire, hnew, if_false]
    split <;> rfl
  have hkv : ∀ k, (S.fire e).kv k =
      if Sys.touches e.2 k ∧ e.2.op = opPUT then some e.2.val else S.kv k := by
    intro k
    simp only [Sys.kv, hg]
    by_cases ht : Sys.touches e.2 k
    · simp only [ht, if_true, true_and, Sys.lastPut, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
    · simp only [ht, if_false, false_and]
  cases inp with
  | get k' =>
    simp only [cmdOf] at hcmd
    refine ⟨funext fun k => ?_, ?_⟩
    · rw [hkv, hcmd]; simp [opGET, opPUT]
    · simp [Sys.outOf, hcmd, Sys.kv]
  | put k' v =>
    simp only [cmdOf] at hcmd
    refine ⟨funext fun k => ?_, ?_⟩
    · rw [hkv, hcmd]
      by_cases hk : k = k'
      · subst hk; simp [Sys.touches]
      · simp only [Sys.touches, hk, if_false]
        rw [if_neg]; rintro ⟨h | ⟨h, -⟩, -⟩
        · exact hk h.symm
        · revert h; decide
    · simp [Sys.outOf, hcmd, opGET, opPUT, opSCAN]
  | scan k' n =>
    simp only [cmdOf] at hcmd
    simp only [inpRangeOk] at hval
    refine ⟨funext fun k => ?_, ?_⟩
    · rw [hkv, hcmd]; simp [opSCAN, opPUT]
    · simp only [Sys.outOf, hcmd]
      rw [if_neg (by decide), if_pos trivial, rangeKeys_scan k' n hval]
      rfl

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
