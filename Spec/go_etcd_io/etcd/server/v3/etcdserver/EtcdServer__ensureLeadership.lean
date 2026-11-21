/-
`s.ensureLeadership()` (`server.go`), translated with its body (srvloops2, 2026-11-21; until then names
only, a trust-boundary contract). Lean-first (no Rocq counterpart); the lease-renew plan
(`notes/lease-renew-plan.md`, 2026-11-01), vocabulary `LeaseRead.lean`.
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

/-- **`s.ensureLeadership()`**, any goroutine, with the request side's and the read side's server
facts (as `leaseTimeToLive.spec`), a reader slot of the logger's lock (`srvLgReader`: `Logger()`),
one of the read loop's (`srvReadReader`: `LinearizableReadNotify`'s) and one level `l` of a thread
token, 3 or 4 (`levelTok l`, `rnTickLvlOk l`: the revocation's outer goroutine calls it with its level
3, `LeaseRenew` with its spare level 4), which it returns: a boolean.

It logs (`s.Logger()`), reads `s.r`'s latest tick time (`isActive` → `getLatestTickTs`, under
`r.tickMu`'s read lock, with a reader slot borrowed from the lock's pool at level `l`, `rnTickPool`,
by the level token: `srvLeadCheckOk`, the reader's view's), and returns `true` if a tick happened within three tick
intervals; else waits for a linearizable read (`s.read.LinearizableReadNotify` on
`context.WithTimeout(s.ctx, s.Cfg.ReqTimeout())`) and compares raft's `Status().Lead` with the member's
id. It writes nothing the model sees. (srvloops2, 2026-11-21: proved over its body; until then a
names-only contract, which took a level token of any level and assumed `tickMu`'s read lock needed no
reader slot, with the premise `threadBound GF ≤ 2 ^ 30 - 1` for that assumption.) -/
abbrev EtcdServer.ensureLeadership.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (l : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvLgReader s ∗
      srvReadReader s γr ∗ levelTok l ∗ ⌜rnTickLvlOk l⌝ }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"ensureLeadership")) (Val #()))
  {{ (b : Bool), RET #b; srvLgReader s ∗ srvReadReader s γr ∗ levelTok l }}

end spec

end EtcdGrove
end Perennial
