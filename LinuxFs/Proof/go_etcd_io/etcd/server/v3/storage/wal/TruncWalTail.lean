/- Lean-first (no Rocq counterpart).

# `os.File.Truncate.specWalTail` (I3b, `wal-tc10`)

The WAL tail's truncate at its write position `wr = o0 + |out|` (`cut`'s first step on the old tail),
proved over `os.File.Truncate.specAu` with the supply `walTail_truncSup` (`TruncSup.lean`), the tie the
handle's key and half of its tail record. The handle hands the truncate its halves of the tail's
`OsMeta` and of the bytes past `wr`, keeping those below. On success (`os.ftDoneH`) the tail's `OsMeta`
is the landing `(rsPost true m wr wr).withTc tc rz`, `tc` knowing what the landing keeps known
(`TcKnows`), so the handle's `TailMetaW` holds at the size `wr` with its `TailZ` (`TailZ.rsPost_tc`); on
an error the handle is lost (the spec's post).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TruncSup
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cutTail

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure

/-- **`TailZ` after a truncate at or below the size landed**, the candidates known past the new size
those the landing keeps known (`TcKnows`). -/
theorem TailZ.rsPost_tc {m : OsMeta} {wr : Nat} {tc : GMap Nat Cands} {rz : List Nat} (h : TailZ m)
    (hwr : wr ≤ m.size) (hk : TcKnows m wr wr tc) : TailZ ((rsPost true m wr wr).withTc tc rz) := by
  obtain ⟨z0, hz0, hs0, hp0, hc0⟩ := h
  have hmin : min m.size wr = wr := Nat.min_eq_right hwr
  have hhi : rsHi true m.size wr = pageEnd m.size := by
    simp only [rsHi, if_true, Nat.max_eq_left hwr]
  have hle := le_pageEnd m.size
  refine ⟨if wr < pageEnd m.size then max z0 (pageEnd m.size) else z0, ?_, ?_, ?_, ?_⟩
  · simp only [OsMeta.withTc_zf, rsPost, announce_zf, hz0, Option.map_some, hmin, hhi]
  · simp only [OsMeta.withTc_size, Perennial.os.rsPost_size']; split <;> omega
  · simp only [OsMeta.withTc_size, OsMeta.withTc_cz, Perennial.os.rsPost_size']
    show pageEnd _ ≤ max wr (rsCz true m wr)
    simp only [rsCz, if_true, hhi, hz0, Option.getD_some]
    by_cases hw : wr < pageEnd m.size
    · rw [if_pos hw]
      simp only [pageEnd] at hp0 hle hw ⊢
      omega
    · rw [if_neg hw]
      simp only [pageEnd] at hp0 hle hw ⊢
      omega
  · intro b hb1 hb2
    simp only [OsMeta.withTc_size, Perennial.os.rsPost_size'] at hb1
    simp only [OsMeta.withTc_tc]
    have hz : z0 ≤ b → (m.pc b).isSome := by
      intro hzb; unfold OsMeta.pc
      cases hc : m.tc !! b with
      | some c => rfl
      | none => simp [hz0, hzb]
    have ht := hk b (by
      rw [rsTail_isSome_iff, hmin, hhi]
      by_cases hbh : b < pageEnd m.size
      · refine .inl ⟨⟨hb1, hbh, hb1⟩, ?_⟩
        by_cases hbs : b < m.size
        · exact .inl hbs
        · refine .inr ?_
          by_cases hzb : z0 ≤ b
          · exact hz hzb
          · obtain ⟨c, hc⟩ := hc0 b (by omega) (by omega)
            unfold OsMeta.pc; rw [hc]; rfl
      · have hbz : b < z0 := by split at hb2 <;> omega
        obtain ⟨c, hc⟩ := hc0 b (by omega) hbz
        refine .inr ⟨fun h' => hbh h'.2.1, ?_, by rw [hc]; rfl⟩
        simp only [inRange, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega)
    cases hc : tc !! b with
    | none => rw [hc] at ht; cases ht
    | some c => exact ⟨c, rfl⟩

end pure

end WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- See the file header. -/
theorem os.File.Truncate.wp_specWalTail (Mr : WalMarshal)
    (wp_Truncate : os.File.Truncate.specAu (GF := GF) (hG := hG)) :
    os.File.Truncate.specWalTail (W := W) Mr := by
  intro R jr r f fd name dir γ i H md cuts o0 sz out hle
  iintro %Φ ⟨#Harea, Hw⟩ HΦ
  unfold walTailW
  icases Hw with ⟨Hof, ⟨%rd, Hfd⟩, Hoff, Hk, %m, %bs, Hm, Hb, %hp, Hv⟩
  obtain ⟨hmsz, ⟨hlen, hmaps, hZ, hlo, hhi, hpz⟩, hsz62, hfd, hlw⟩ := hp
  have hwr : o0 + out.length ≤ m.size := by omega
  have hT : (W64 ((o0 : Int) + (out.length : Int))).toNat = o0 + out.length := by word
  have hI : 0 ≤ (W64 ((o0 : Int) + (out.length : Int))).toInt := by word
  icases (osBytes_takeDrop i _ bs (o0 + out.length) (by omega)).1 $$ Hb with ⟨Hbt, Hbd⟩
  unfold WalFs.walAreaOk
  icases Harea with ⟨#Hinv, #Hos, -⟩
  ihave #Hsup : os.truncSup iprop(walTailKey (W := W) dir γ ∗
      tailVar (W := W) γ ((H, md, cuts, o0 + out.length, i, none) : TailG)) i
      (W64 ((o0 : Int) + (out.length : Int))).toNat (fun m => LoWr m (o0 + out.length)) $$ []
  · rw [hT, ← walTailKeyL_none]; iapply walTail_truncSup Mr R jr r dir γ none H md cuts (o0 + out.length) i (fun _ h => nomatch h) (fun _ h => nomatch h) $$ Hinv
  ihave HK : iprop(walTailKey (W := W) dir γ ∗
      tailVar (W := W) γ ((H, md, cuts, o0 + out.length, i, none) : TailG)) $$ [Hk Hv]
  · unfold tailVar; iframe
  ihave Hbd : osBytes i (min m.size (W64 ((o0 : Int) + (out.length : Int))).toNat)
      (DFrac.own (1 : Qp).half) (bs.drop (o0 + out.length)) $$ [Hbd]
  · rw [hT, Nat.min_eq_right hwr]; iexact Hbd
  wp_apply wp_Truncate f fd name (DFrac.own 1) (W64 ((o0 : Int) + (out.length : Int))) (DFrac.own 1)
    ⟨i, rd, true⟩ m (bs.drop (o0 + out.length)) _ (fun m => LoWr m (o0 + out.length)) hfd rfl hI hmaps
    (by rw [List.length_drop, hT]; omega) hlw $$ [Hof Hfd Hm Hbd HK] as %err ⟨Hof, Hfd, HK, Hr, -⟩
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
    iframe Hof Hoff Hk
    isplitl [Hfd]
    · iexists rd; iexact Hfd
    iexists (rsPost true m (o0 + out.length) (o0 + out.length)).withTc tc rz, bs.take (o0 + out.length)
    iframe Hm' Hbt
    isplitr
    · ipureintro
      refine ⟨rfl, ⟨by simp only [List.length_take, OsMeta.withTc_size, Perennial.os.rsPost_size']; omega,
        by simp [rsPost, hmaps], TailZ.rsPost_tc hZ hwr htc.1, ?_, ?_, ?_⟩, by omega, hfd, ?_⟩
      · simp only [OsMeta.withTc_lo, OsMeta.withTc_size, Perennial.os.rsPost_size', rsPost, announce_lo]
        omega
      · simp only [OsMeta.withTc_hi, OsMeta.withTc_size, Perennial.os.rsPost_size', rsPost, announce_hi]
        omega
      · exact hpz.of_tcFrom htc.2
          (by simp only [OsMeta.withTc_hi, rsPost, announce_hi]; omega)
          (by simp only [OsMeta.withTc_hi, rsPost, announce_hi]; omega)
      · exact .inr (by simp only [OsMeta.withTc_lo, rsPost, announce_lo]; omega)
    unfold tailVar; iexact Hv
  · iright; ipureintro; exact he

end proof

end EtcdGrove
end Perennial

end
