/-
`concurrency.runSTM(s, apply)` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
`InvSTM.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTM

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `runSTM(s, apply)`, for an STM before its first `reset`: attempts (`reset`, `apply`, `commit`)
until `apply` fails or a commit succeeds, in a goroutine whose result comes back on a channel:
`stmResult` (an error: `apply`'s, or a client error, recovered from the abort's panic). -/
abbrev runSTM.spec : Prop :=
  ∀ (lvl : w64) (pfx : GoString) (p : Loc) (apply : GoFunc) (Q : STMSt → Prop) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ stmMethods lvl pfx p ∗ stmStale lvl pfx p ∗ applySpec pfx apply Q ∗
      etcdReached lo }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.runSTM))
      (Val #(GoInterface.ok (stmIface lvl p)))) (Val #apply))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); stmResult pfx lvl lo Q resp err }}

end spec

end concurrency
end EtcdGrove
end Perennial
