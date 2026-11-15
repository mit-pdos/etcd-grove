/- Lean-first (no Rocq counterpart). The proof of `member.opOwnSnap`. -/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__opOwnSnap
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__saveSnap
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.rnd__choose
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.copyOps
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.nameBound
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.storeOracle
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__ReleaseLockTo
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.OwnSnapAu
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.CandsLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

section pure
variable [GooseExts]

/-- The candidates after `k` turns of the raise loop. -/
def tRaisePre (o : TOracle) (a : w64) (k : Nat) : List TCand :=
  (o.cands.take k).map (tRaiseCand o a) ++ o.cands.drop k

theorem tRaisePre_zero (o : TOracle) (a : w64) : tRaisePre o a 0 = o.cands := by simp [tRaisePre]

theorem tRaisePre_all (o : TOracle) (a : w64) {k : Nat} (hk : o.cands.length ≤ k) :
    tRaisePre o a k = (tRaiseNames o a).cands := by
  simp [tRaisePre, tRaiseNames, List.take_of_length_le hk, List.drop_of_length_le hk]

theorem tRaisePre_get (o : TOracle) (a : w64) {k : Nat} {cd : TCand} (hk : o.cands[k]? = some cd) :
    (tRaisePre o a k)[k]? = some cd := by
  have hl : k < o.cands.length := (List.getElem?_eq_some_iff.1 hk).1
  unfold tRaisePre
  rw [List.getElem?_append_right (by simp; omega)]
  simp [hk, show k - min k o.cands.length = 0 by omega]

theorem tRaisePre_set (o : TOracle) (a : w64) {k : Nat} {cd : TCand} (hk : o.cands[k]? = some cd) :
    (tRaisePre o a k).set k (tRaiseCand o a cd) = tRaisePre o a (k + 1) := by
  have hl : k < o.cands.length := (List.getElem?_eq_some_iff.1 hk).1
  unfold tRaisePre
  apply List.ext_getElem?
  intro n
  rw [List.getElem?_set]
  by_cases hn : n = k
  · subst hn
    rw [if_pos rfl]
    have : n < ((o.cands.take n).map (tRaiseCand o a) ++ o.cands.drop n).length := by simp; omega
    rw [if_pos this, List.getElem?_append_left (by simp; omega)]
    simp [List.getElem?_take, hk]
  · rw [if_neg (Ne.symm hn)]
    by_cases hlt : n < k
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
      simp [List.getElem?_take, hlt, show n < k + 1 by omega]
    · rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map, List.length_take, List.getElem?_drop]
      congr 1; omega

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

set_option maxHeartbeats 2000000 in
theorem member.opOwnSnap.wp_proof (wp_choose : rnd.choose.spec (GF := GF) (hG := hG))
    (wp_saveSnap : member.saveSnap.spec (GF := GF) (hG := hG))
    (wp_copyOps : copyOps.spec (GF := GF) (hG := hG))
    (wp_nameBound : nameBound.spec (GF := GF) (hG := hG))
    (wp_store : storeOracle.spec (GF := GF) (hG := hG))
    (wp_Release : ∀ W : WalGS GF,
      go_etcd_io.etcd.server.v3.storage.wal.WAL.ReleaseLockTo.spec (W := W) (walRaftP (GF := GF)) walRaftMr) :
    member.opOwnSnap.spec (GF := GF) (hG := hG) := by
  intro W e γ m qc o hf hroom
  wp_start as Hlive
  iunfold memLive at Hlive
  icases Hlive with ⟨%w, %v, %os, %c, %d, %t, %vo, %cm, %bs, %l, %tm, %M, %r, %rv, Hres, Ht, Hv, Hc, Hb,
    Hl, Htm, HM, Hr, Hrv, Hpw, %Hfacts⟩
  obtain ⟨hok, hhs, hfl, hwf, hms⟩ := Hfacts
  wp_auto
  wp_if_destruct
  · iapply HΦ
    simp only [↓reduceIte]
    iexists o
    isplitl
    · iunfold memLive
      iexists w, v, os, c, d, t, vo, cm, bs, l, tm, M, r, rv
      iframe
      ipureintro; exact ⟨hok, hhs, hfl, hwf, hms⟩
    · ipureintro; omega
  wp_apply wp_choose $$ [$Hrv] as %k ⟨⟨%rv1, Hrv⟩, %hk⟩
  rw [if_neg (by word)] at hk
  have ha1 : uint.nat bs < uint.nat (bs + W64 1 + k) := by word
  have ha2 : uint.nat (bs + W64 1 + k) ≤ uint.nat cm := by word
  have hl63 := tMemSim_last_lt hms hok.2.2.2.2.2.2.2.2.1
  have hcl := tMemSim_commitLe hms
  have ha63 : uint.nat (bs + W64 1 + k) < 2 ^ 63 := by omega
  try wp_auto
  wp_apply (wp_map_lookup1 (K := w64) (V := w64) go.uint64 go.uint64 tm M (bs + W64 1 + k) (DFrac.own 1)) $$ [$HM] as HM
  have hta : uint.nat ((M !! (bs + W64 1 + k)).getD (zero_val w64)) < 2 ^ 63 := by
    cases hM : M !! (bs + W64 1 + k) with
    | none => show uint.nat (W64 0) < 2 ^ 63; decide
    | some x => exact hfl.2 _ _ hM
  have hsim := tMemSim_own (t := (M !! (bs + W64 1 + k)).getD (zero_val w64)) hms ha1 ha2
  ihave ⟨Hres, #Hpers⟩ := memSaveRes_pers W e γ m w v o os c d qc $$ Hres
  wp_apply (wp_saveSnap W e γ m w v o os c d qc (bs + W64 1 + k) ((M !! (bs + W64 1 + k)).getD (zero_val w64))
    hf hok hhs ha63 hta (tOrRoom_snap hroom (Nat.le_refl _) _ _) hsim.1) $$ [$Hres] as %b1 Hpost1
  cases b1
  · try wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; trivial
  try wp_auto
  ihave Hres1 := memSaveRes_postOp W e γ m w _ c qc $$ [$Hpers $Hpost1]
  icases Hres1 with ⟨%v1, %os1, %d1, Hres1, %Hok1⟩
  sorry

end proof

end etcd_wal
end EtcdGrove
end Perennial
