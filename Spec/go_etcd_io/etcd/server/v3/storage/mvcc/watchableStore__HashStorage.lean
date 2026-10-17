/-
`(*mvcc.watchableStore).HashStorage()` (`server/storage/mvcc/kvstore.go`, promoted from the embedded
`*store`; names only; item 4, the server start): what `v3rpc.NewMaintenanceServer` stores as its
`hasher`.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.mvcc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `wsl.HashStorage()` on the watchable store returns a value (a `mvcc.HashStorage`). -/
abbrev mvcc.watchableStore.HashStorage.spec : Prop :=
  ∀ (wsl : Loc),
  {{ (True : IProp GF) }}
    (App (Val (wsl @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty
      @!! go!"HashStorage")) (Val #()))
  {{ (h : GoInterface), RET #h; True }}

end spec

end EtcdGrove
end Perennial
