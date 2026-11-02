/-
`Run(lg)` (`examples/restart3/restart3.go`; the restart plan's R2a, 2026-11-02; DRAFT): three
members started, member 1's gRPC API served and a client of it, a `Put` of `k`, a follower stopped
(member 3, or member 2 if member 3 leads), `NPuts` more `Put`s, the follower started again on its
data directory and its gRPC API served, a client of it, a `Get` of `k`, and a panic unless the
`Get` returned the last `Put`'s value. Lean-first (no Rocq counterpart).

**The triple:** putget3's `Main.spec`'s (`putget3/Main.lean`) for `restart3`'s members at any
logger `lg` that is not `nil`, with the rights to listen on all three client addresses (member 1's
is served before the restart, the restarted member's after it) and `restart3`'s premises (with the
restart's contracts, `premises`): `Run(lg)` returns, so it did not panic.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.restart3.Defs
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace restart3

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.restart3.Assumptions]

/-- `Run`'s and `Main`'s pure premises (putget3's, but the thread and receipt bounds, which `Run.spec`
and `Main.spec` take as instances). -/
def runPure (id₁ id₂ id₃ : w64) (ctxs : List (List w8)) (boot : List LogEntry) : Prop :=
  BootFacts id₁ id₂ id₃ ctxs boot ∧
  ckptEffectsOk ∧ authRecordsFit ∧ apply.backendUnderQuota ∧ grpcRepliesFit ∧ storage.diskOk

/-- `Run`'s and `Main`'s resources (putget3's `Main`'s, with all three client addresses). -/
def runRes (N : Nat) (id₁ id₂ id₃ : w64) (ctxs : List (List w8)) (boot : List LogEntry) :
    IProp GF :=
  iprop(netAddrFree (GF := GF) peerAddr₁ ∗ netAddrFree (GF := GF) peerAddr₂ ∗
    netAddrFree (GF := GF) peerAddr₃ ∗ netAddrFree (GF := GF) clientAddr₁ ∗
    netAddrFree (GF := GF) clientAddr₂ ∗ netAddrFree (GF := GF) clientAddr₃ ∗
    httpProtoFree (GF := GF) peerAddr₁ ∗ httpProtoFree (GF := GF) peerAddr₂ ∗
    httpProtoFree (GF := GF) peerAddr₃ ∗ threadTok ∗ premises N id₁ id₂ id₃ ctxs boot)

/-- See the file header. -/
abbrev Run.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (lg : Loc) (N : Nat) (id₁ id₂ id₃ : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)] [ReceiptBoundLe GF (N + 1)],
  lg ≠ null → runPure id₁ id₂ id₃ ctxs boot →
  v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.restart3 ∗
      runRes N id₁ id₂ id₃ ctxs boot }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.restart3.Run)) (Val #lg))
  {{ RET #(); True }}

end spec

end restart3
end EtcdGrove
end Perennial
