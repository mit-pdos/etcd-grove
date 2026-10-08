/-
Port of election_proof/spec_readOnly__addRequest.v (feb5c73d4).

Lean notes:
* The reference `readOnly__addRequestⁱᵐᵖˡ, new/code/go_etcd_io/raft/v3.v:6250` is to
  the Lean generated code `readOnly.addRequest.impl`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `ro.addRequest(commitIndex, req)` (`readOnly.addRequest.impl`,
`Code/go_etcd_io/raft/v3.lean`; `read_only.go:60`):

      ro.unconfirmedReads = append(ro.unconfirmedReads,
          &readIndexRequest{req: req, index: commitIndex})

No panic, no call. The queue is `ownReadOnly`'s, a read-only slice with owned slack, so
`append` writes into the slack or reallocates (`wp_slice_append_persistent`); the new
request is allocated and persisted. The record gains `⟨commitIndex, req.From', ents⟩`
(`readonlyAdd`), where `ents` is what `req.Entries'` points to, which the caller holds
read-only (as `msgAbs` does for a queued message -- the request message is stored by
value, so its `Entries` slice is shared). The receiver is a pointer, so the spec owns
the object. -/
abbrev readOnly.addRequest.spec : Prop :=
  ∀ (ro : Loc) (r : ReadOnly) (commitIndex : w64) (req : raftpb.Message)
    (ents : List raftpb.Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hown" ∷ ownReadOnly ro r ∗
      "#Hents" ∷ req.Entries' ↦*□ ents }}
    (App (App (Val (ro @!! go.GoType.PointerType readOnly.ty @!! go!"addRequest"))
      (Val #commitIndex)) (Val #req))
  {{ RET #();
      ownReadOnly ro (readonlyAdd r (ReadReq.mk commitIndex req.From' ents)) }}

end spec

end EtcdGrove
end Perennial
