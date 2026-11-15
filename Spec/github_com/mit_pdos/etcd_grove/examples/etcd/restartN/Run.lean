/-
`Run(k, lg)` (`examples/etcd/restartN/restartN.go`; `notes/restartN-plan.md`): for `k ≥ 2`, the `k`
members (`etcdstart.Members`) started, each serving its peer handler (`startMembers`), the `N1`
in-process `Put`s through member `0` (`put`), a follower other than member `0` stopped (`stop`: member
`k - 1`, or `k - 2` if `k > 2` and member `k - 1` leads), the `N2` more `Put`s through member `0`, the
stopped member started again on its data directory (`restartMember`, its peer handler swapped to the new
incarnation's), and the check at the restarted member (`check`). Lean-first (no Rocq counterpart).

**The triple:** with a zap logger, for `k ≤ 1000` members whose ids `ids` (in the members' order) are
`bootstrap`'s (`BootFacts`), the members' start bundles (`etcdstart.memberStartRes`: each data directory
fresh, the right to listen on its peer address with its HTTP protocol unregistered, `ETCD_VERIFY` off),
the main thread's token and `Run`'s named premises (`premises`: `bootstrap`'s contract for each member's
first start, and its restart contract for the members that may be stopped), at the bounds the server's
specs take: no panic.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.KV
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Defs
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restartN

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver
open etcd_restart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Assumptions]

/-- See the file header. -/
abbrev Run.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (k : Nat) (lg : Loc) (N : Nat) (ids : List w64)
    (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  k ≤ 1000 → ids.length = k → BootFacts ids ps ctxs boot →
  srvLevels (GF := GF) →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restartN ∗
      zapLoggerOk lg ∗
      ([∗list] m ∈ members k, etcdstart.memberStartRes (GF := GF) m.Name' ⟨some m.Peer', none⟩) ∗
      threadTok ∗ premises k N ids ps ctxs boot }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restartN.Run)) (Val #(W64 k)))
      (Val #lg))
  {{ (b : Bool), RET #b; True }}

end spec

end etcd_restartN
end EtcdGrove
end Perennial
