/-
`m.CloseWithError(err)` (`etcdserver/api/snap/message.go`; names only; rafthttp stage 7b, D42,
2026-10-24, statement for review, **D22's interface**: to be agreed with the D22 owner): closes
the message's reader and sends `err == nil` on its `closeC` (`NewMessage`'s channel, of one slot,
whose receives carry nothing: `isChanBag` at `True`; a second send would block, which a partial
correctness spec allows). The snapshot sender calls it once, after its post, from `send`'s
`defer`. The trust boundary (an axiom once the sender's proof uses it, stage 7d). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.snap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI snap

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `m.CloseWithError(err)` of a merged message (see the file header): returns. -/
abbrev snap.Message.CloseWithError.spec : Prop :=
  ∀ (m ml : Loc) (rc err : GoInterface),
  {{ msgIs (GF := GF) m ml rc }}
    (App (Val (m @!! go.GoType.PointerType
        _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message.ty @!!
        go!"CloseWithError")) (Val #err))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
