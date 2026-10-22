/-
`m.CloseNotify()` (`etcdserver/api/snap/message.go`; names only): the message's `closeC`. The
trust boundary (D22 S-h, 2026-10-20; an axiom in `Proof/.../snap/Message__CloseNotify.lean`).
Lean-first (no Rocq counterpart); the vocabulary is `Proof/.../snap/Defs.lean`.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `m.CloseNotify()`: `m`'s `closeC` (read-only). -/
abbrev snap.Message.CloseNotify.spec : Prop :=
  ∀ (m c : Loc),
  {{ msgCloseC (GF := GF) m c }}
    (App (Val (m @!! go.GoType.PointerType
        _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message.ty @!!
        go!"CloseNotify")) (Val #()))
  {{ RET #c; True }}

end spec

end EtcdGrove
end Perennial
