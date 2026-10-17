/-
`RecordClientCertExpiration` (`metrics.go`, pr-verify etcd#21621). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvConnStats

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`RecordClientCertExpiration(x)`** observes `x` in the histogram
`clientCertExpirationSecs` once: from the histogram's `P` to its `Q x` (`certExpHist`). -/
abbrev v3rpc.RecordClientCertExpiration.spec : Prop :=
  ∀ (x : w64) (P : IProp GF) (Q : w64 → IProp GF),
  {{ v3rpc.certExpHist P Q ∗ P }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.RecordClientCertExpiration))
      (Val #x))
  {{ RET #(); Q x }}

end spec

end EtcdGrove
end Perennial
