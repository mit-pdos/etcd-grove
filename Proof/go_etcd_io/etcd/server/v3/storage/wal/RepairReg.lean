/- Lean-first (no Rocq counterpart).

# `Repair`'s tail registration, pending (L4; W7 of `notes/wal-fsext-plan.md`, W7-W12 log, fifteenth session)

`repair_register`: before its truncate, `Repair` registers the last segment of the WAL it holds open
(`walLastOpen`: the directory's key, its claim's half, the pin, no tail registered) as a pending tail
(`walInvRegisterPendLaw_holds` at `gs = [gL]`). The registration's layout reads the same records from the
segment as the decoder loop did (`walRepairFile` on it, `repairFile_unique`): the tail record is stated at
the stream's end `wr`, and the decoder's `LastOffset()` at the stop, `(recFrames rs).length`, is `wr` or,
past a pending run (P6), the run's end: `TailMetaRP` at it (the run's first length word nonzero, the
reader's stop at `wr` on the bytes below it; what `os.File.Truncate.specRepTail` takes).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllRegCommit
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairPre
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadState
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairTailDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairDecode

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **`Repair`'s registration of its last segment, pending** (see the file header). -/
theorem repair_register (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString) (dir : GoString)
    (d : WalDur) (lay : WalLay) (X : List GoString) (hj : NamesH) (gL : SegG) (rs : List WalRec)
    (habs : WalAbsD walCodec Mr d lay hj.cur) (hnd : (lay.segs.map (·.ino)).Nodup)
    (hsn : SegsNamed lay.segs hj.cur) (hgL : lay.segs.getLast? = some gL)
    (hSz : gL.om.size = gL.bs.length) (hRF : RepairFile walCodec (segImg gL) rs) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) walCodec Mr R jr r -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ walDirKey (W := W) dir lay.j X -∗
      osNames (L := hG.goose_localGS) lay.j (.except X) (DFrac.own (1 : Qp).half) hj -∗
      walTailsFrag (W := W) ∅ -∗
      osMeta (L := hG.goose_localGS) gL.ino (DFrac.own (1 : Qp).half) gL.om -∗
      osBytes (L := hG.goose_localGS) gL.ino 0 (DFrac.own (1 : Qp).half) gL.bs ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗
      osNames (L := hG.goose_localGS) lay.j (.except X) (DFrac.own (1 : Qp).half) hj ∗
      osMeta (L := hG.goose_localGS) gL.ino (DFrac.own (1 : Qp).half) gL.om ∗
      osBytes (L := hG.goose_localGS) gL.ino 0 (DFrac.own (1 : Qp).half) gL.bs ∗
      ∃ (γ : GName) (H : List (WalOpG WalEnt)) (md : List w8) (cuts : List Nat) (k wr : Nat),
        walTailsFrag (W := W) (<[dir := γ]> (∅ : GMap GoString GName)) ∗ walPendTok (W := W) dir γ k ∗
        tailVar (W := W) γ ((H, md, cuts, wr, gL.ino, none) : TailG) ∗
        ⌜wr = (tailStream Mr H md cuts).length ∧ wr ≤ (recFrames walCodec rs).length ∧
          TailMetaRP Mr (tailCrc Mr H md cuts) wr (recFrames walCodec rs).length gL.om gL.bs⌝ := by
  iintro #Hinv Hnc #Hk Hn Htf Hm Hb
  have hgLm : gL ∈ lay.segs := List.mem_of_getLast? hgL
  have hnm : ∀ g ∈ [gL], hj.cur !! g.name = some (.file g.ino) := by
    intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    exact (hsn.1 g hgLm).2
  have hwn : walNames hj.cur = lay.segs.map (·.name) :=
    walNames_segs hsn habs.names.1 hnd habs.names.2
  have hdrop : ∃ kk, (walNames hj.cur).drop kk = [gL].map (·.name) := by
    obtain ⟨A, e⟩ := List.getLast?_eq_some_iff.1 hgL
    refine ⟨A.length, ?_⟩
    rw [hwn, e, List.map_append, List.drop_left' (by simp)]
  ihave Hh : [∗list] g ∈ [gL], osMeta (L := hG.goose_localGS) g.ino (DFrac.own (1 : Qp).half) g.om ∗
      osBytes (L := hG.goose_localGS) g.ino 0 (DFrac.own (1 : Qp).half) g.bs $$ [Hm Hb]
  · iapply (BigSepL.bigSepL_singleton (PROP := IProp GF)).2; iframe
  imod walInvRegisterPendLaw_holds walCodec Mr R jr r dir lay.j X hj [gL] gL hnm hdrop
      (fun g hg => by rw [List.mem_singleton] at hg; subst hg; exact hSz) rfl
    $$ Hinv Hnc Hk Hn Htf Hh with ⟨Hnc, Hn, Hh, %d', %lay', %kk, %γ, Htf, Hpt, Hv, %hrs⟩
  obtain ⟨-, habs', hex', hwr', hdr', hTM, -, -⟩ := hrs
  obtain ⟨rs', es, hRF', hrsw', -, hpS, hnz⟩ :=
    walRepairFile walCodec_ok habs' hex' hwr' gL (getLast?_of_drop (by rw [hdr']; rfl))
  have hrr : rs = rs' := repairFile_unique walCodec_ok hRF hRF'
  subst hrr
  icases (BigSepL.bigSepL_singleton (PROP := IProp GF)).1 $$ Hh with ⟨Hm, Hb⟩
  imodintro
  iframe Hnc Hn Hm Hb
  iexists γ, d'.H, d'.metadata, lay'.cuts, lay'.old.length, lay'.wr
  iframe Htf Hpt
  isplitl [Hv]
  · unfold tailVar tailG; iexact Hv
  ipureintro
  refine ⟨by rw [hwr', tailStream_eq], by omega, hTM, ?_, ?_⟩
  · rcases hnz with h | ⟨b, h1, h2, h3⟩
    · exact .inl h
    · have hb : b < gL.bs.length := by
        apply Classical.byContradiction; intro hb
        apply h3
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [segImg]; omega)]; rfl
      refine .inr ⟨b, gL.bs[b], h1, h2, List.getElem?_eq_getElem hb, ?_⟩
      rw [getD_of_lt _ _ _ (by simp [segImg]; exact hb)] at h3
      simpa [segImg] using h3
  · rw [List.map_take]
    unfold segImg at hpS
    unfold tailCrc
    rw [show histN d'.H = histM d' by rw [histM]]
    exact hpS

end iris

end WalFs
end EtcdGrove
end Perennial

end
