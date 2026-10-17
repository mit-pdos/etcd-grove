/-
`s.waitApplyWithinRequestLimit(timeout)` (`server.go`; new in etcd-io/etcd#22527, branch
`pr-verify/etcd-22527`): after a publish rejected with "too many requests", wait until the member
has applied far enough for a proposal at the committed index it reads to pass the request limit,
or until the timeout or the server's stop. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Why the wait ended** (for `c`, the committed index read at entry): the limit already
passes, with no wait (`c ≤ maxNormalGap`); the applied index has reached `c - maxNormalGap`, so a
proposal checked at `c` passes `exceedsRequestLimit`'s normal gap (`c ≤ applied + 5000`); or the
wait gave up (the timer fired, or `stopping` is closed). The last case carries no fact: neither
channel's close tells anything (the timer's channel and `stopping` have content `True`), so in a
partial-correctness triple the disjunction is as strong as `True`. It is stated to document the
three exits; what the PR is about (no retry before the apply catches up, unless the timeout or the
stop comes first) is a progress property, outside what the triple can say.

**What `appliedAtLeast` means here rests on raft's no-snapshot contract.** The server's proof ties
`applyWait`'s `appliedAtLeast γr` to `s.appliedIndex` (`setAppliedIndex`), and `applyAll`'s
`applySnapshot` is verified only with no snapshot (`EtcdServer__applySnapshot.lean`). With a
snapshot, Go's `applyAll` triggers `applyWait` at the snapshot's index while `s.appliedIndex` may
still lag (etcd-io/etcd#22516, fixed by #22510), and the wait then ends at once with the limit
still exceeded: the case of #22526's reproduction, which this PR alone leaves looping. -/
def waitApplyExit (γr : ReadNames) (c : w64) : IProp GF :=
  iprop(⌜uint.Z c ≤ 5000⌝ ∨ (⌜5000 < uint.Z c⌝ ∗ appliedAtLeast γr (c - W64 5000)) ∨ True)

/-- `s.waitApplyWithinRequestLimit(timeout)`, any goroutine, at the server's read-side view
(`isServerRead`: the committed index's invariant, the applied index's waiters `applyWait`, a
`WaitTime` for `appliedAtLeast γr`, and the `stopping` channel): it returns, with the committed
index `c` it read (`committedAtLeast γr c`) and why the wait ended (`waitApplyExit`). -/
abbrev EtcdServer.waitApplyWithinRequestLimit.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (d : _root_.Perennial.time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerRead s E γr }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"waitApplyWithinRequestLimit"))
      (Val #d))
  {{ RET #(); ∃ c : w64, committedAtLeast γr c ∗ waitApplyExit γr c }}

end spec

end EtcdGrove
end Perennial
