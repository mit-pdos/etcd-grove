/-
`(*clientv3.lessor).sendKeepAliveLoop(stream)` (`client/v3/lease.go`; item 1, the client lease). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `l.sendKeepAliveLoop(stream)` on a lessor (`lessorAt`) with the client end of a keep-alive
stream and its send token: sends a request for each keep-alive due (read under the lock) until a
send fails or the stream's context, `donec` or the stop context is done; it returns then (or runs
forever). -/
abbrev lessor.sendKeepAliveLoop.spec : Prop :=
  ∀ (l : Loc) (addr : GoString) (st : GoInterface) (γ : StreamNames)
    (Dn : Nat → (w64 × w64) → IProp GF) (cd : context.ContextDesc (IProp GF)) (L : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorAt l addr ∗
      cliBidiStreamIs st γ pbLeaseKeepAliveRequest pbLeaseKeepAliveResponse
        (fun _ _ => iprop(True)) Dn cd ∗
      cliSendTok (Req := pbLeaseKeepAliveRequest) γ L }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"sendKeepAliveLoop")) (Val #st))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
