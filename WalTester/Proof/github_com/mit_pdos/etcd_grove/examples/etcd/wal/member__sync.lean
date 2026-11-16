/-
`member.sync.wp_proof` (W4c U5): `Sync`, then `storeOracle` of the synced oracle, whose `tRelI` is the
candidate's (`tMemOk_candOk`) with `Sync`'s `walSyncedLb` at the whole history. Lean-first (no Rocq
counterpart).
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__sync
public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.storeOracle
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Sync
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.putOps
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.SnapPure

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
    WalFs.walSyncedLb (W := W) (tWalDir area) d.H.length ∗ WalFs.walNamed (W := W) (tWalDir area) ⊢
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

theorem member.sync.wp_proof
    (wp_store : storeOracle.spec (GF := GF) (hG := hG))
    (wp_Sync : ∀ W : WalGS GF,
      go_etcd_io.etcd.server.v3.storage.wal.WAL.Sync.spec (W := W) (walRaftP (GF := GF)) walRaftMr) :
    member.sync.spec (GF := GF) (hG := hG) := by
  intro W e γ m w v o os c d qc hf hok hsm hcwf
  wp_start as ⟨#Hos, #Hsi, #Hinv, #Hdi, Hh, Hperm, Hpath, Hw, Hov, Hrep, Ho, Hwo, #Harea, Hwf,
    #Hlen, #Hnm⟩
  wp_auto
  wp_apply (wp_Sync W e.R e.jr (e.area) w (tWalDir e.area) d.H.length) $$ [Hwf]
    as %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, Hwf, #Hsl⟩ | %Herr)
  · subst Herr
    wp_auto
    ihave ⟨%hl, Hrep⟩ := oracleRep_synced v o $$ Hrep
    ihave #Hrel := tRelI_synced W e.area o c d hok hl hcwf $$ [Hsl Hnm]
    · isplitl []
      · iexact Hsl
      · iexact Hnm
    wp_apply (wp_store W e γ _ os (tSynced o) (some d) qc hf hsm) $$ [Hh Hperm Hrep Ho Hwo]
      as ⟨Hh, Hperm, Hrep, Ho, Hwo⟩
    · iframe; iframe #
    iapply HΦ
    simp only [↓reduceIte]
    iframe
    iframe #
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ie =>
    wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe

end proof

end etcd_wal
end EtcdGrove
end Perennial
