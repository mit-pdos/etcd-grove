/-
`tRelI_synced` and `oracleRep_synced`, out of `member__sync.lean`'s proof so that the tester's lemmas
import them without the proof (import tiers, 2026-11-18).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__sync
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.storeOracle
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Sync
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.SnapPure
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.putOpsLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- The relation the synced oracle stores: its candidate accounts for the WAL. -/
theorem tRelI_synced (W : WalGS GF) (area : GoString) (o : TOracle) (c : TCand) (d : WalDur)
    (h : tMemOk o c d) (hl : o.since.length < 2 ^ 64) (hw : tCheckWf o) :
    WalFs.walSyncedLb (W := W) (tWalDir area) 0 d.H.length ∗ WalFs.walNamed (W := W) (tWalDir area) 0 ⊢
      tRelI (W := W) (GF := GF) area (tSynced o) (some d) := by
  iintro ⟨#Hs, #Hn⟩
  unfold tRelI
  simp only [show (tSynced o).created = true from h.1, ↓reduceIte]
  iexists d, c
  isplitr
  · ipureintro; exact ⟨rfl, h.2.1, tMemOk_candOk h hl, tCheckWf_synced hw hl⟩
  rw [tSynced_mark o c hl, ← tMemOk_len h]
  isplitl []
  · iexact Hs
  · iexact Hn

/-- The oracle with its mark at `len(since)`: the Go value's `synced` written. -/
theorem oracleRep_synced (v : oracle) (o : TOracle) :
    oracleRep (GF := GF) v o ⊢ ⌜o.since.length < 2 ^ 64⌝ ∗
      oracleRep (oracle.mk v.created' v.cands' v.since' v.since'.len v.lastHS' v.opens') (tSynced o) := by
  iintro Hr
  iunfold oracleRep at Hr
  icases Hr with ⟨%Hf, Hcs, #Hsince, Hscap, #Hop, Hopcap⟩
  ihave #Hs2 := Hsince
  iunfold opsRep at Hs2
  icases Hs2 with ⟨%vs, #Hs, #Hel⟩
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hel_len := opsElems_length $$ Hel
  have hw : W64 o.since.length = v.since'.len := w64_of_length o.since v.since'.len (Hel_len ▸ Hlen)
  isplitr
  · ipureintro; rw [← Hel_len, Hlen.1]; word
  iunfold oracleRep
  simp only [tSynced]
  isplitr
  · ipureintro
    exact ⟨Hf.1, by show v.since'.len = W64 o.since.length; exact hw.symm, Hf.2.2⟩
  iframe
  isplitl []
  · iexact Hsince
  · iexact Hop

end proof

end etcd_wal
end EtcdGrove
end Perennial
