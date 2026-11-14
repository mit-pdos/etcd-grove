/- Lean-first (no Rocq counterpart).

# `os.File.Truncate.specRepTail` (L4; the W7-W12 log, thirteenth session)

`Repair`'s truncate of its registered, not yet zeroed tail at the write position `o0` (the record's stream
end), proved over `os.File.Truncate.specAu` with the supply `walTail_truncSup` at the pending token (kind
`true`: F-Z or `RepOld`, the lent registry's, at every attempt; `rzStart_pureK`), as
`os.File.Truncate.wp_specWalTail` (`TruncWalTail.lean`) but with the file's offset framed (the os spec
does not touch it). On success the tail's `OsMeta` is the landing `(rsPost true m o0 o0).withTc tc rz`
(`TailMetaRW`: the window open, `lo = o0`); on an error the file handle back.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TruncSup
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.RepairCallees

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- See the file header. -/
theorem os.File.Truncate.wp_specRepTail (Mr : WalMarshal)
    (wp_Truncate : os.File.Truncate.specAu (GF := GF) (hG := hG)) :
    os.File.Truncate.specRepTail (W := W) Mr := by
  intro R jr r f fd name dir γ i H md cuts o0 sz k off hle hS
  iintro %Φ ⟨#Harea, Hw⟩ HΦ
  unfold walTailPO
  icases Hw with ⟨Hof, ⟨%rd, Hfd⟩, Hoff, Hk, %m, %bs, Hm, Hb, %hp, Hv⟩
  obtain ⟨hmsz, ⟨hlen, hmaps, hlo, hhi⟩, hsz62, hfd, hlw⟩ := hp
  have hwr : o0 ≤ m.size := by omega
  have hT : (W64 (o0 : Int)).toNat = o0 := by word
  have hI : 0 ≤ (W64 (o0 : Int)).toInt := by word
  icases (osBytes_takeDrop i _ bs o0 (by omega)).1 $$ Hb with ⟨Hbt, Hbd⟩
  unfold WalFs.walAreaOk
  icases Harea with ⟨#Hinv, #Hos, -⟩
  ihave #Hsup : os.truncSup iprop(walTailKeyL (W := W) dir γ (some (k, true)) ∗
      tailVar (W := W) γ ((H, md, cuts, o0, i, none) : TailG)) i
      (W64 (o0 : Int)).toNat (fun m => LoWr m o0) $$ []
  · rw [hT]
    iapply walTail_truncSup Mr R jr r dir γ (some (k, true)) H md cuts o0 i (fun _ _ => hS) $$ Hinv
  ihave HK : iprop(walTailKeyL (W := W) dir γ (some (k, true)) ∗
      tailVar (W := W) γ ((H, md, cuts, o0, i, none) : TailG)) $$ [Hk Hv]
  · rw [walTailKeyL_some]; unfold tailVar; iframe
  ihave Hbd : osBytes i (min m.size (W64 (o0 : Int)).toNat)
      (DFrac.own (1 : Qp).half) (bs.drop o0) $$ [Hbd]
  · rw [hT, Nat.min_eq_right hwr]; iexact Hbd
  wp_apply wp_Truncate f fd name (DFrac.own 1) (W64 (o0 : Int)) (DFrac.own 1)
    ⟨i, rd, true⟩ m (bs.drop o0) _ (fun m => LoWr m o0) hfd rfl hI hmaps
    (by rw [List.length_drop, hT]; omega) hlw (fun m' h _ => .inr (by rw [hT] at h; omega))
    $$ [Hfd Hof Hm Hbd HK] as %err ⟨Hof, Hfd, HK, Hr, -⟩
  · iframe; iframe #
  rw [hT]
  iapply HΦ
  icases Hr with (⟨%he, %zs, Hd⟩ | ⟨%he, -⟩)
  · ileft
    isplitr
    · ipureintro; exact he
    unfold os.ftDoneH
    icases Hd with ⟨-, ⟨%tc, %rz, %htc, Hm'⟩, -⟩
    icases HK with ⟨Hk, Hv⟩
    rw [walTailKeyL_some]
    iframe Hof Hoff Hk
    isplitl [Hfd]
    · iexists rd; iexact Hfd
    iexists (rsPost true m o0 o0).withTc tc rz, bs.take o0
    iframe Hm' Hbt
    isplitr
    · ipureintro
      refine ⟨rfl, ⟨by simp only [List.length_take, OsMeta.withTc_size, Perennial.os.rsPost_size']; omega,
        by simp [rsPost, hmaps], ?_, ?_⟩, by omega, hfd, ?_⟩
      · simp only [OsMeta.withTc_lo, OsMeta.withTc_size, Perennial.os.rsPost_size', rsPost, announce_lo]
        omega
      · simp only [OsMeta.withTc_hi, OsMeta.withTc_size, Perennial.os.rsPost_size', rsPost, announce_hi]
        omega
      · exact .inr (by simp only [OsMeta.withTc_lo, rsPost, announce_lo]; omega)
    unfold tailVar; iexact Hv
  · iright
    iframe Hof Hoff
    isplitr
    · ipureintro; exact he
    iexists rd; iexact Hfd

end proof

end EtcdGrove
end Perennial

end
