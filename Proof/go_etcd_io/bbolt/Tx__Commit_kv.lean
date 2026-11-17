/-
`Tx.Commit_kv`'s proof: bbolt's proved `Tx.Commit` at the program's file extension (`theFs`), over
the backend's vocabulary (`InvBbolt.lean`; stage S1 of `notes/bbolt-integration-plan.md`).
-/
module

public import Spec.go_etcd_io.bbolt.Tx__Commit_kv
public import Spec.go_etcd_io.bbolt.Tx__Commit

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

theorem bbolt.Tx.Commit_kv.wp_proof
    (h : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [os.file.FieldAssumptions]
      [os.fileStat.FieldAssumptions], bbolt.Tx.Commit.spec (GF := GF) (hG := hG)) :
    bbolt.Tx.Commit_kv.spec (GF := GF) (hG := hG) := by
  intro db tx γ D S
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, onFs_none hfs]
    iintro %Φ ⟨-, ⟨H, -⟩⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, backend.curAt_eq, backend.bktEnts_eq, backend.seekIdx_eq,
      onFs_some hfs]
    iintro %Φ ⟨-, ⟨#Hdb, Hs⟩, #Hd, ⟨%G, Hl⟩⟩ HΦ
    ihave Hau := bbolt.boltState_commit_au γ D S $$ Hs
    have h' := h tx γ (wView D S G) (bbolt.boltState γ 1 S)
    try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, TxView.ro.proj_rw, TxView.ro.proj_base, TxView.ro.proj_cur, TxView.ro.proj_gen, wView_setBkt, wView_dropBkt] at h'
    wp_apply h' $$ [$Hl $Hau] as %err ⟨#Hdn, Hr⟩
    all_goals try (ipureintro; first | trivial | rfl)
    iapply HΦ; iframe Hdn
    icases Hr with (⟨%He, Hs⟩ | ⟨%He, -⟩)
    · ileft; isplitr; · ipureintro; exact He
      iframe Hs Hdb
      unfold wrTok; itrivial
    · iright; ipureintro; exact He

end proof

end EtcdGrove
end Perennial
