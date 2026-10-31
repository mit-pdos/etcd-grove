/-
`concurrency.NewMutex(s, pfx)` (`client/v3/concurrency/mutex.go`). Lean-first (no Rocq counterpart); see
`InvMutex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvMutex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- **`NewMutex(s, pfx)`**, for a session `s` whose client answers for the prefix `pfx + "/"`
(`isEtcdMutexClient`), and a prefix shorter than `2 ^ 27` bytes (2026-10-30, kept in `isMutex`): a
mutex on that prefix, in its initial state (`myKey = ""`, `myRev = -1`,
`hdr = nil`). -/
abbrev NewMutex.spec : Prop :=
  ∀ (s : Loc) (γ : SessionNames) (client : Loc) (id : w64) (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ isSession s γ client id ∗
      isEtcdMutexClient client (pfx ++ go!"/") ∗ ⌜pfx.length < 2 ^ 27⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.NewMutex)) (Val #s)) (Val #pfx))
  {{ (m : Loc), RET #m; isMutex m s γ client id (pfx ++ go!"/") ∗ mutexState m MutexSt.init }}

end spec

end concurrency
end EtcdGrove
end Perennial
