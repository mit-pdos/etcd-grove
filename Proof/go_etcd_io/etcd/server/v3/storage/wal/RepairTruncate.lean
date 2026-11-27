/- Lean-first (no Rocq counterpart).

# `os.File.Truncate.specRepTail` (L4; the W7-W12 log, thirteenth session)

`Repair`'s truncate of its registered, not yet zeroed tail at `tg ∈ [o0, size]` (`o0` the record's stream
end; past it a pending run, P6), proved over `os.File.Truncate.specAu` with the supply `walTail_truncSupR`
at the pending token (kind
`true`: F-Z or `RepOld`, the lent registry's, at every attempt; `rzStart_pureK`), as
`os.File.Truncate.wp_specWalTail` (`TruncWalTail.lean`) but with the file's offset framed (the os spec
does not touch it). On success the tail's `OsMeta` is the landing `(rsPost true m o0 o0).withTc tc rz`
(`TailMetaRW`: the window open, `lo = o0`); on an error the file handle back.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.TruncSupRep
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.RepairCallees

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
  intro R jr r f fd name dir γ i H md cuts o0 tg sz k off hle htg hS
  iintro %Φ ⟨#Harea, Hw⟩ HΦ
  unfold walTailPO
  icases Hw with ⟨Hof, ⟨%rd, %lo, %lk, Hfd, Hlkt⟩, Hoff, Hk, %m, %bs, Hm, Hb, %hp, Hv⟩
  obtain ⟨hmsz, ⟨⟨hlen, hmaps, hlo, hhi⟩, hnz, hpv⟩, hsz62, hfd⟩ := hp
  have hwr : tg ≤ m.size := by omega
  have hT : (W64 (tg : Int)).toNat = tg := by word
  have hI : 0 ≤ (W64 (tg : Int)).toInt := by word
  icases (osBytes_takeDrop i _ bs tg (by omega)).1 $$ Hb with ⟨Hbt, Hbd⟩
  have hnz' : tg = o0 ∨ ∃ b x, o0 ≤ b ∧ b < tg ∧ (bs.take tg)[b]? = some x ∧ x.1 ≠ 0 := by
    rcases hnz with h | ⟨b, x, h1, h2, h3, h4⟩
    · exact .inl h
    · exact .inr ⟨b, x, h1, h2, by rw [List.getElem?_take, if_pos h2]; exact h3, h4⟩
  icases osBytes_repNZ i (bs.take tg) o0 tg (by simp only [List.length_take]; omega) hnz' $$ Hbt with
    ⟨%nz, HNZ, Hrest⟩
  unfold WalFs.walAreaOk
  icases Harea with ⟨#Hinv, #Hos, -⟩
  ihave #Hsup : os.truncSup (repTie (W := W) dir γ k H md cuts o0 i tg nz) i
      (W64 (tg : Int)).toNat (RepP o0 tg m.size) $$ []
  · rw [hT]
    iapply walTail_truncSupR Mr R jr r dir γ k H md cuts o0 i tg m.size nz hS hle hwr $$ Hinv
  ihave HK : repTie (W := W) dir γ k H md cuts o0 i tg nz $$ [Hk Hv HNZ]
  · unfold repTie; rw [walTailKeyL_some]; unfold tailVar; iframe
  ihave Hbd : osBytes i (min m.size (W64 (tg : Int)).toNat)
      (DFrac.own (1 : Qp).half) (bs.drop tg) $$ [Hbd]
  · rw [hT, Nat.min_eq_right hwr]; iexact Hbd
  wp_apply wp_Truncate f fd name (DFrac.own 1) (W64 (tg : Int)) (DFrac.own 1)
    ⟨i, rd, true, lo, lk⟩ m (bs.drop tg) _ (RepP o0 tg m.size) hfd rfl hI hmaps
    (by rw [List.length_drop, hT]; omega) ⟨fun _ => LoWr.of_exact hlo hhi, .inl rfl⟩
    (fun m' h h' => ⟨fun he => .inr (by rw [hT] at h; omega), by rw [hT] at h'; exact h'⟩)
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
    unfold repTie
    icases HK with ⟨Hk, Hv, HNZ⟩
    ihave Hbt := Hrest $$ HNZ
    rw [walTailKeyL_some]
    iframe Hof Hoff Hk
    isplitl [Hfd Hlkt]
    · iexists rd, lo, lk; iframe
    iexists (rsPost true m tg tg).withTc tc rz, bs.take tg
    iframe Hm' Hbt
    isplitr
    · ipureintro
      refine ⟨rfl, ⟨⟨by simp only [List.length_take, OsMeta.withTc_size, Perennial.os.rsPost_size']; omega,
        by simp [rsPost, hmaps], ?_, ?_⟩,
        by simp only [OsMeta.withTc_size, Perennial.os.rsPost_size']; omega, hpv⟩, by omega, hfd⟩
      · simp only [OsMeta.withTc_lo, OsMeta.withTc_size, Perennial.os.rsPost_size', rsPost, announce_lo]
        omega
      · simp only [OsMeta.withTc_hi, OsMeta.withTc_size, Perennial.os.rsPost_size', rsPost, announce_hi]
        omega
    unfold tailVar; iexact Hv
  · iright
    iframe Hof Hoff
    isplitr
    · ipureintro; exact he.1
    iexists rd, lo, lk; iframe

end proof

end EtcdGrove
end Perennial

end
