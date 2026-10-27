/-
`MainWatch(nw, nops, sched)` (`examples/linkv3p/linkv3p.go`; W4 of `notes/watch-cut-plan.md`,
2026-10-22): watchkv's workload over linkv3p's cluster under partitions. The writers' `nw * nops`
puts picked (`genAll`); the cluster started (`startCluster`: three members, a bridge to each,
three clients each of every bridge); a prefix watch on `wk/` from revision `1` through the first
client; the partitioner forked on the schedule `sched`; `nw` writer goroutines, each put through a
client picked at random; then, after they are done, the successful puts' log, the watch read up to
their highest revision (`collect`) and the check (`checkWatch`, which panics if the watch did not
report exactly the writes). Lean-first (no Rocq counterpart).

**The triple:** from the package's `isPkgInit`, the right to listen on the nine addresses, the
schedule read-only (for *every* list of steps), the main thread's token and `Main`'s named
premises (`linkv3p.premises`), `MainWatch(nw, nops, sched)` does not panic and returns `WatchOk`
(`0`: the check ran and passed), `WatchFailed` (`1`: a step of the start failed) or `WatchEnded`
(`2`: the watch ended before it reported every successful put). The pure premises are `Main`'s
(`linkv3p.Main.spec`) and watchkv's bounds on `nw` and `nops` (`watchkv.Main.spec`); the class
premises are the client watcher's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.Defs
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

/-- See the file header. -/
abbrev MainWatch.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [ErrorStringLeaf] [ErrorStringNoGRPCStatus] [context.ErrorStringIsError]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)] [PeerPausable]
    (N : Nat) (id₁ id₂ id₃ : w64) (bootLog : List EntryM) (nw nops : w64) (sched : GoSlice)
    (steps : List github_com.mit_pdos.etcd_grove.examples.linkv3p.Step),
  BootFacts id₁ id₂ id₃ bootLog →
  threadBound GF ≤ 2 ^ 29 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota →
  storage.dbOpensOk → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  0 ≤ sint.Z nw → sint.Z nw < 2 ^ 31 → 0 ≤ sint.Z nops →
  sint.Z nw * sint.Z nops < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3p ∗
      netAddrFree (GF := GF) peerAddr₁ ∗ netAddrFree (GF := GF) peerAddr₂ ∗
      netAddrFree (GF := GF) peerAddr₃ ∗ netAddrFree (GF := GF) clientAddr₁ ∗
      netAddrFree (GF := GF) clientAddr₂ ∗ netAddrFree (GF := GF) clientAddr₃ ∗
      netAddrFree (GF := GF) bridgeAddr₁ ∗ netAddrFree (GF := GF) bridgeAddr₂ ∗
      netAddrFree (GF := GF) bridgeAddr₃ ∗
      httpProtoFree (GF := GF) peerAddr₁ ∗ httpProtoFree (GF := GF) peerAddr₂ ∗
      httpProtoFree (GF := GF) peerAddr₃ ∗ sched ↦*□ steps ∗ threadTok ∗
      premises N id₁ id₂ id₃ bootLog }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3p.MainWatch))
      (Val #nw)) (Val #nops)) (Val #sched))
  {{ (r : w64), RET #r; ⌜r = W64 0 ∨ r = W64 1 ∨ r = W64 2⌝ }}

end spec

end linkv3p
end EtcdGrove
end Perennial
