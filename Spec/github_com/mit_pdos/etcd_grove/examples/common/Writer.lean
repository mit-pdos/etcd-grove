/- Lean-first (no Rocq counterpart).
`Writer(cli, w, tried, lo, hi)` (`examples/common/watch.go`; watchkv's `writer` until 2026-10-22,
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
message: the pairs tried are small (`wkvSizeOk`; 2026-10-31, `notes/invoke-size.md`, pass 4).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.WritesF
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.common go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

/-- See the file header. -/
abbrev Writer.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (cl api : Loc) (γk : KVNames) (QW : GoString → GoString → KVState → IProp GF)
    (OkF : wrec → IProp GF) (w : Loc) (tsl : GoSlice) (tried : List wkv) (lo hi : w64),
  (∀ p, Persistent (OkF p)) →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  0 ≤ sint.Z lo → sint.Z lo ≤ sint.Z hi → sint.Z hi ≤ tried.length → (∀ x ∈ tried, wkvSizeOk x) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
        GoInterface.ok (client.kvIfaceOf api) ∗
      client.isKv api γk false ∗ tsl ↦*□ tried ∗
      (□ ∀ (k v : GoString), ⌜(k, v) ∈ tried.map pairOf⌝ -∗
        AU <{ ∃∃ (σ : KVState), etcdKV γk σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
          <{ etcdKV γk (kvOpStep (.put (putWireOf (opPutModel k v []))) σ),
            COMM QW k v σ }>) ∗
      (□ ∀ (k v : GoString) (σ : KVState), QW k v σ -∗ ⌜σ.rev + 4 < 2 ^ 63 ∧ kvLogOk σ⌝ -∗
        OkF ⟨W64 ((σ.rev + 1 : Nat) : Int), k, v⟩) ∗
      sync.isMutex (structFieldRef github_com.mit_pdos.etcd_grove.examples.common.Writes go!"Mu" w)
        (wsInvF w OkF) }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.common.Writer))
      (Val #cl)) (Val #w)) (Val #tsl)) (Val #lo)) (Val #hi))
  {{ RET #(); True }}

end spec

end common
end EtcdGrove
end Perennial
