/-
`s.ensureLeadership()` (`server.go`), names only: a trust-boundary contract. Lean-first (no Rocq counterpart); the
lease-renew plan (`notes/lease-renew-plan.md`, 2026-11-01), vocabulary `LeaseRead.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseRead

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.ensureLeadership()`** (names-only, a contract; the lease-renew plan's C2), any goroutine,
with the request side's and the read side's server facts (as `leaseTimeToLive.spec`), a reader slot
of the logger's lock (`srvLgReader`: `Logger()`), one of the read loop's (`srvReadReader`:
`LinearizableReadNotify`'s) and a thread token, which it returns: a boolean.

**Why it is faithful.** It logs (`s.Logger()`, under `s.lgMu`'s read lock), reads `s.r`'s latest
tick time twice (`isActive` → `getLatestTickTs`, under `r.tickMu`'s read lock), takes
`context.WithTimeout(s.ctx, s.Cfg.ReqTimeout())`, waits for a linearizable read
(`s.read.LinearizableReadNotify`, proved: `ReadOn.lean`, with the read loop's slot) and compares
`raftStatus().Lead` with the member's id; every branch returns a boolean. It writes nothing the
model sees. **Its assumption**: `tickMu`'s read locks need no slot of the caller's. The model drops
`tickMu`'s reader slots when the node starts (`NodeStart.lean`), so no request goroutine has one;
a goroutine holds that read lock only inside `getLatestTickTs`, so its readers are at most the
goroutines, fewer than the lock's reader limit by the thread bound (`threadTok`,
`threadBound GF ≤ 2 ^ 30 - 1`), which is what a slot would rule out. -/
abbrev EtcdServer.ensureLeadership.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvLgReader s ∗
      srvReadReader s γr ∗ threadTok ∗ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"ensureLeadership")) (Val #()))
  {{ (b : Bool), RET #b; srvLgReader s ∗ srvReadReader s γr ∗ threadTok }}

end spec

end EtcdGrove
end Perennial
