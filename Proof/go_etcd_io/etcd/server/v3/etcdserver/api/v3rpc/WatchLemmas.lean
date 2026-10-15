/-
Lemmas the watch server's loops share (the watch slice's unit W-S): a response struct as the
wire model's message (`watchRespMsg_intro`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A response struct is the wire model's message** `m`: the struct (read-only), its header's
fields, its events' slice holding the events of `m` (mvcc's `evIs`), and its other fields
`m`'s. -/
theorem watchRespMsg_intro (l : Loc) (v : etcdserverpb.WatchResponse) (m : WatchRespM)
    (ps : List Loc) (h1 : v.WatchId' = m.watchId) (h2 : v.Created' = m.created)
    (h3 : v.Canceled' = m.canceled) (h4 : v.CompactRevision' = m.compactRev)
    (h5 : v.CancelReason' = m.cancelReason) (h6 : v.Fragment' = m.fragment)
    (hlen : ps.length = m.evs.length) :
    ⌜l ≠ null⌝ ∗ typedPointsto l v DFrac.discard ∗ hdrFull v.Header' m.hdr ∗
      v.Events' ↦*□ ps ∗ ([∗list] x ∈ ps.zip m.evs, mvcc.evIs x.1 x.2) ⊢
      watchRespMsg (GF := GF) l m := by
  iintro ⟨%Hl, Hv, #Hh, #Hps, #Hevs⟩
  iStructNamed Hv
  iunfold watchRespMsg
  iframe %
  rw [← h1, ← h2, ← h3, ← h4, ← h5, ← h6]
  iframe
  iframe #

/-- **A control response struct** (no events, no compaction, not fragmented) is the wire model's
message with no ghost source. -/
theorem ctrlMsg_intro (l h : Loc) (hm : HdrM) (id cmp : w64) (cr ca : Bool) (reason : GoString)
    (st : google_golang_org.protobuf.internal.impl.MessageState) (uf : GoSlice) (sc : w32) :
    ⌜l ≠ null⌝ ∗
      typedPointsto l (etcdserverpb.WatchResponse.mk st h id cr ca cmp reason false slice.nil uf sc)
        DFrac.discard ∗ hdrFull h hm ⊢
      watchRespMsg (GF := GF) l ⟨hm, id, cr, ca, cmp, reason, false, [], none⟩ := by
  iintro ⟨%Hl, #Hv, #Hh⟩
  iapply watchRespMsg_intro l (etcdserverpb.WatchResponse.mk st h id cr ca cmp reason false
    slice.nil uf sc) _ [] rfl rfl rfl rfl rfl rfl rfl
  iframe #
  isplitr
  · ipureintro; exact Hl
  isplitl
  · iapply ownSlice_nil
  simp only [List.zip_nil_left]
  iapply BigSepL.bigSepL_nil.2
  iempintro

end lemmas

end v3rpc
end EtcdGrove
end Perennial
