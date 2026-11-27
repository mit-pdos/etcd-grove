/-
`Run(lg)` (`examples/etcd/restart/restart3.go`; restart3 C2, 2026-11-15): the three members built
(`build`) and started, each serving its peer handler (`newMember`), the `N1` in-process `Put`s through
member 1 (`put`), a follower other than member 1 stopped (`stop`: member 3, or member 2 if member 3
leads), the `N2` more `Put`s through member 1, the stopped member started again on its data directory
(`restartMember`, its peer handler swapped to the new incarnation's), and the check at the restarted
member (`check`). Lean-first (no Rocq counterpart).

**The triple:** with a zap logger, the members' start bundles (`etcdstart.memberStartRes`: each data
directory fresh, the right to listen on its peer address with its HTTP protocol unregistered,
`ETCD_VERIFY` off), the main thread's token and `Run`'s named premises (`premises`: `bootstrap`'s
contract for each member's first start, and its restart contract for members 2 and 3), at the bounds
the server's specs take: no panic.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.KV
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart.Defs
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart.Assumptions]

/-- See the file header. -/
abbrev Run.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (lg : Loc) (N : Nat) (id₁ id₂ id₃ : w64)
    (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  BootFacts id₁ id₂ id₃ ps ctxs boot →
  srvLevels (GF := GF) →
  N + 7 + bootWB ≤ backend.wbInit →
  authRecordsFit → apply.backendUnderQuota → storage.diskOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart ∗
      zapLoggerOk lg ∗
      etcdstart.memberStartRes (GF := GF) name₁ ⟨some peerAddr₁, none⟩ ∗
      etcdstart.memberStartRes (GF := GF) name₂ ⟨some peerAddr₂, none⟩ ∗
      etcdstart.memberStartRes (GF := GF) name₃ ⟨some peerAddr₃, none⟩ ∗
      threadTok ∗ premises N id₁ id₂ id₃ ps ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart.Run)) (Val #lg))
  {{ (b : Bool), RET #b; True }}

end spec

end etcd_restart
end EtcdGrove
end Perennial
