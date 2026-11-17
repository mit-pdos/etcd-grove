/-
`Tx.CreateBucketIfNotExists_kv`'s proof: bbolt's proved `Tx.CreateBucketIfNotExists` at the program's file extension (`theFs`), over
the backend's vocabulary (`InvBbolt.lean`; stage S1 of `notes/bbolt-integration-plan.md`).
-/
module

public import Spec.go_etcd_io.bbolt.Tx__CreateBucketIfNotExists_kv
public import Spec.go_etcd_io.bbolt.Tx__CreateBucketIfNotExists

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

theorem bbolt.Tx.CreateBucketIfNotExists_kv.wp_proof
    (h : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [os.file.FieldAssumptions]
      [os.fileStat.FieldAssumptions], bbolt.Tx.CreateBucketIfNotExists.spec (GF := GF) (hG := hG)) :
    bbolt.Tx.CreateBucketIfNotExists_kv.spec (GF := GF) (hG := hG) := by
  intro tx γ D S G name n dq hn0 hnm
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax⟩
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, onFs_none hfs]
    iintro %Φ ⟨-, ⟨H, -⟩⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, backend.curAt_eq, backend.bktEnts_eq, backend.seekIdx_eq,
      onFs_some hfs]
    iintro %Φ ⟨-, Hl, Hn⟩ HΦ
    have h' := h tx γ (wView D S G) name n dq
    try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, TxView.ro.proj_rw, TxView.ro.proj_base, TxView.ro.proj_cur, TxView.ro.proj_gen, wView_setBkt, wView_dropBkt] at h'
    have hc : ¬ n.length = 0 := by omega
    simp only [if_neg hc] at h'
    wp_apply h' $$ [$Hl $Hn] as %b %err ⟨Hn, Hr⟩
    · ipureintro; exact ⟨trivial, hnm⟩
    icases Hr with ⟨%He, #Hb, Hl⟩
    iapply HΦ
    iframe Hn
    isplitr; · ipureintro; exact He
    isplitl [Hl]
    · rw [show wView D (if S.lookup n = none then S.insert n ∅ else S) G =
          (if S.lookup n = none then wView D (S.insert n ∅) G else wView D S G) by split <;> rfl]
      iexact Hl
    · iexact Hb

end proof

end EtcdGrove
end Perennial
