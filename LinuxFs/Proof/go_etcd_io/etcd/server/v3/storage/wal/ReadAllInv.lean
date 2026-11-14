/- Lean-first (no Rocq counterpart).

# `ReadAll`'s read of the invariant before the loop (W3/W5 of `notes/wal-fsext-plan.md`, nineteenth session)

The decode loop's arms must not panic (`MustUnmarshalEntry`, …), so the proof needs, before the loop,
that what the reader reads from the handle's files decodes (`ReadAllLoop.readFiles_dec`). The files'
bytes are fixed by the program's halves (`walReadTie`), so one look at the invariant suffices, with no
program step: `walInv_open` under `notCrashed` (as `walInv_dirPath`), `walInvBody_readState`, closed at
once. `walInv_readFiles` gives the read's pure facts at that moment; `readTie_dec` turns them into the
loop's premise over the decoder's files (`F.bs = segImg g`, `walReadTie`'s file fact).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadState
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllLoop
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DecDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **The decoder's files decode**: files whose bytes are the page-cache images of the layout's
segments from `kk` on, under the read's facts. -/
theorem readFiles_dec' {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {U : WalUnmarshal} (hU : U.Ok Mr)
    {d : WalDur} {lay : WalLay} {ents : Ents} (hab : WalAbsD C Mr d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (kk : Nat)
    (gs : List SegG) (hgs : lay.segs.drop kk = gs) (hne : gs ≠ []) (bss : List (List w8))
    (hbs : bss = gs.map segImg) :
    ∀ r ∈ (rdRest C bss 0 0#32).recs, RecDec U r := by
  have hkk : kk < lay.segs.length := by
    refine Nat.lt_of_not_le fun h => hne ?_
    rw [← hgs]; exact List.drop_eq_nil_of_le h
  rw [rdRest_start, hbs, ← hgs]
  exact readFiles_dec hC hU hab hex hwr kk hkk

/-- **The decoder's files decode, their metadata records the WAL's** (`readFiles_dec'` with
`readFiles_md`: the loop's premise). -/
theorem readFiles_ok' {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {U : WalUnmarshal} (hU : U.Ok Mr)
    {d : WalDur} {lay : WalLay} {ents : Ents} (hab : WalAbsD C Mr d lay ents) (hex : TailExact lay)
    (hwr : lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length) (kk : Nat)
    (gs : List SegG) (hgs : lay.segs.drop kk = gs) (hne : gs ≠ []) (bss : List (List w8))
    (hbs : bss = gs.map segImg) :
    ∀ r ∈ (rdRest C bss 0 0#32).recs, RecDec U r ∧ RecMd d.metadata r := by
  have hkk : kk < lay.segs.length := by
    refine Nat.lt_of_not_le fun h => hne ?_
    rw [← hgs]; exact List.drop_eq_nil_of_le h
  intro r hr
  refine ⟨readFiles_dec' hC hU hab hex hwr kk gs hgs hne bss hbs r hr, ?_⟩
  rw [rdRest_start, hbs, ← hgs] at hr
  exact readFiles_md hC hab hex hwr kk hkk r hr

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **The read's facts, by a look at the invariant** (see the file header): no step, the invariant
closed at once; the resources `walInvBody_readState` takes come back. -/
theorem walInv_readFiles (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (j : Ino) (X : List GoString) (hj0 : NamesH) (gs : List SegG)
    (hnm : ∀ g ∈ gs, hj0.cur !! g.name = some (.file g.ino))
    (hdrop : ∃ kk, (walNames hj0.cur).drop kk = gs.map (·.name))
    (hsz : ∀ g ∈ gs, g.om.size = g.bs.length) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ walDirKey (W := W) dir j X -∗
      osNames (L := hG.goose_localGS) j (.except X) (DFrac.own (1 : Qp).half) hj0 -∗
      walTailsFrag (W := W) ∅ -∗
      ([∗list] g ∈ gs, osMeta (L := hG.goose_localGS) g.ino (DFrac.own (1 : Qp).half) g.om ∗
        osBytes (L := hG.goose_localGS) g.ino 0 (DFrac.own (1 : Qp).half) g.bs) ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗
      osNames (L := hG.goose_localGS) j (.except X) (DFrac.own (1 : Qp).half) hj0 ∗
      walTailsFrag (W := W) ∅ ∗
      ([∗list] g ∈ gs, osMeta (L := hG.goose_localGS) g.ino (DFrac.own (1 : Qp).half) g.om ∗
        osBytes (L := hG.goose_localGS) g.ino 0 (DFrac.own (1 : Qp).half) g.bs) ∗
      ∃ (d : WalDur) (lay : WalLay) (kk : Nat),
        ⌜lay.j = j ∧ WalAbsD C Mr d lay hj0.cur ∧ TailExact lay ∧
          lay.wr = (segStream C Mr d lay.cuts lay.cuts.length).length ∧ lay.segs.drop kk = gs⌝ := by
  iintro #Hinv Hnc #Hk Hn Hf Hgs
  imod walInv_open (L := hG.goose_localGS) C Mr R jr r ⊤ (fun _ _ => CoPset.mem_full) $$ Hinv Hnc
    with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  icases walInvBody_readState (L := hG.goose_localGS) C Mr R jr r s dir j X hj0 gs hnm hdrop hsz
    $$ Hb Hk Hn Hf Hgs with ⟨%d, %lay, %kk, %hfacts, Hb, -, Hn, Hf, Hgs⟩
  imod Hcl $$ [Hb] with -
  · iexists s; iexact Hb
  imodintro
  iframe
  iexists d, lay, kk
  ipureintro
  exact hfacts.2

end iris

end WalFs
end EtcdGrove
end Perennial
