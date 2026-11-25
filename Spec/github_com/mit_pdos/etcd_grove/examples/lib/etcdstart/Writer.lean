/- Lean-first (no Rocq counterpart).
`Writer(cli, w, tried, lo, hi)` (`examples/lib/etcdstart/watch.go`; watchkv's `writer` until 2026-10-22,
D33, which cachekv's repeated): the Puts `tried[lo:hi]` through a client whose `KV` field is a
`*kv` of etcd's KV `γk` that sends a write at most once (`isKv api γk false`, `kv.Put.spec`'s
precondition), each with the caller's write update of the KV state by the put (one of the caller's
persistent family, fired at most once, its result `QW k v σ` at the state `σ` it fired at), each in
a context with the examples' request timeout (`context.WithTimeout(context.Background(),
RequestTimeout)`, cancelled after the call; 2026-10-23, `notes/client-timeouts-plan.md` D-T2: the
context is an `isContext` whose `Err()` returns client errors, by the premises `ContextReadErrs`
and `ContextErrsClient` on Go's context errors), logging each that returned no error in `w`
(`wsInvF`, the log's lock invariant) with the caller's fact `OkF` of its record (from `QW` and the
reply's facts: its revision is `σ`'s next, `σ` a well-formed log's state, `kvLogOk`). The caller's facts are its own
(watchkv's of its invariant over the KV state, cachekv's of the clients' model of etcd); until
2026-10-26 the adapter's (`kmInv`, `okFactKM`), before D48 the server's sealed logs. Each Put must fit a gRPC
message: the pairs tried are small (`wkvSizeOk`; 2026-10-31, `notes/invoke-size.md`, pass 4). The
write updates' commits are told the revision's room (`kvRoom σ`, as `kv.Put.spec`'s; 2026-11-05, H-rr1).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WritesF
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.go_etcd_io.etcd.client.v3.ReadUpds
public import Proof.go_etcd_io.etcd.client.v3.PerTypeKVRest
public import Proof.go_etcd_io.etcd.client.v3.PerTypeLease
public import Proof.go_etcd_io.etcd.client.v3.ServerWatcher
public import Proof.go_etcd_io.etcd.client.v3.LeaseClient
public import Proof.go_etcd_io.etcd.client.v3.PerTypeAuth
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.PerTypeWatch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerRFacts
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServerR
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
public import Spec.go_etcd_io.raft.v3.MemoryStorage__SetHardState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__ApplySnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Compact
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Lemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.NetErr
public import Spec.sort.SortAnyLess
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadRaft
public import Proof.go_etcd_io.etcd.pkg.v3.wait.TimeListIfc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LessorOk
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.LessorDerive
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerAllocOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AdminEntryOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyAllSnapLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunAdapt
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchStep
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchClass
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthService
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.QuotaLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerLeaseRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerLeaseRevoke
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.QuotaLeaseLemmas
public import Proof.go_etcd_io.etcd.client.v3.KVServiceOn
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.lib.etcdstart go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]

/-- See the file header. -/
abbrev Writer.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (cl api : Loc) (γk : KVNames) (QW : GoString → GoString → KVState → IProp GF)
    (OkF : wrec → IProp GF) (w : Loc) (tsl : GoSlice) (tried : List wkv) (lo hi : w64),
  (∀ p, Persistent (OkF p)) →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  0 ≤ sint.Z lo → sint.Z lo ≤ sint.Z hi → sint.Z hi ≤ tried.length → (∀ x ∈ tried, wkvSizeOk x) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
        GoInterface.ok (client.kvIfaceOf api) ∗
      client.isKv api γk false ∗ tsl ↦*□ tried ∗
      (□ ∀ (k v : GoString), ⌜(k, v) ∈ tried.map pairOf⌝ -∗
        AU <{ ∃∃ (σ : KVState), etcdKV γk σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
          <{ etcdKV γk (kvOpStep (.put (putWireOf (opPutModel k v []))) σ) ∗ ⌜kvRoom σ⌝,
            COMM QW k v σ }>) ∗
      (□ ∀ (k v : GoString) (σ : KVState), QW k v σ -∗ ⌜σ.rev + 4 < 2 ^ 63 ∧ kvLogOk σ⌝ -∗
        OkF ⟨W64 ((σ.rev + 1 : Nat) : Int), k, v⟩) ∗
      sync.isMutex (structFieldRef github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writes go!"Mu" w)
        (wsInvF w OkF)) }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writer))
      (Val #cl)) (Val #w)) (Val #tsl)) (Val #lo)) (Val #hi))
  {{ RET #(); levelTok 0 ∗ (True) }}

end spec

end etcdstart
end EtcdGrove
end Perennial
