/-
`Tx.Bucket_kvr`'s proof: bbolt's proved `Tx.Bucket` at the program's file extension (`theFs`), over
the backend's vocabulary (`InvBbolt.lean`; stage S1 of `notes/bbolt-integration-plan.md`).
-/
module

public import Spec.go_etcd_io.bbolt.Tx__Bucket_kvr
public import Spec.go_etcd_io.bbolt.Tx__Bucket

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

theorem bbolt.Tx.Bucket_kvr.wp_proof
    (h : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [os.file.FieldAssumptions]
      [os.fileStat.FieldAssumptions], bbolt.Tx.Bucket.spec (GF := GF) (hG := hG)) :
    bbolt.Tx.Bucket_kvr.spec (GF := GF) (hG := hG) := by
  intro tx γ q D name n dq
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax⟩
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, onFs_none hfs]
    iintro %Φ ⟨-, ⟨H, -⟩⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.ownDB, backend.isDB, backend.txLive, backend.txBytes, backend.ownWTx, backend.ownWTxG,
      backend.wBkt, backend.ownCur, backend.txDone, backend.txDB, backend.curAt_eq, backend.bktEnts_eq, backend.seekIdx_eq,
      onFs_some hfs]
    iintro %Φ ⟨-, Hl, Hn⟩ HΦ
    have h' := h tx γ q (TxView.ro D) name n dq
    try simp only [wView.proj_rw, wView.proj_base, wView.proj_cur, wView.proj_gen, TxView.ro.proj_rw, TxView.ro.proj_base, TxView.ro.proj_cur, TxView.ro.proj_gen, wView_setBkt, wView_dropBkt, bbolt.statSlot] at h'
    wp_apply h' $$ [$Hl $Hn] as %b ⟨Hl, Hn, Hr⟩
    · ipureintro; intro h'; cases h'
    iapply HΦ; iframe Hl Hn
    icases Hr with (%Hr | ⟨%Hr, #Hb⟩)
    · ileft; ipureintro; exact Hr
    · iright
      obtain ⟨hn, hb⟩ := Hr
      obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.1 hn
      iexists m
      isplitr
      · ipureintro; exact ⟨hm, hb⟩
      · iexact Hb

end proof

end EtcdGrove
end Perennial
