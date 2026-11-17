/-
`DB.Stats_kv`'s proof: bbolt's proved `DB.Stats` at the program's file extension (`theFs`), over
the backend's vocabulary (`InvBbolt.lean`; stage S1 of `notes/bbolt-integration-plan.md`).
-/
module

public import Spec.go_etcd_io.bbolt.DB__Stats_kv
public import Spec.go_etcd_io.bbolt.DB__Stats

@[expose] public section

set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem bbolt.DB.Stats_kv.wp_proof
    (h : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [os.file.FieldAssumptions]
      [os.fileStat.FieldAssumptions], bbolt.DB.Stats.spec (GF := GF) (hG := hG)) :
    bbolt.DB.Stats_kv.spec (GF := GF) (hG := hG) := by
  intro db tx γ T
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, onFs_none hfs]
    iintro %Φ ⟨-, ⟨H, -⟩⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, backend.curAt_eq, backend.bktEnts_eq, backend.seekIdx_eq,
      onFs_some hfs]
    iintro %Φ ⟨-, #Hb, Hl⟩ HΦ
    have h' := h db γ (some (tx, T))
    simp only [bbolt.statSlot.eq_2] at h'
    wp_apply h' $$ [$Hb $Hl] as %s Hl
    iapply HΦ; iexact Hl

end proof

end EtcdGrove
end Perennial
