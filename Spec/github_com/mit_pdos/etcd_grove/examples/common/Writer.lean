/- Lean-first (no Rocq counterpart).

`Writer(cli, w, tried, lo, hi)` (`examples/common/watch.go`; watchkv's `writer` until 2026-10-22,
D33, which cachekv's repeated): the Puts `tried[lo:hi]` through `New`'s client that sends a write at
most once (`clientWriteOnce`), each with the caller's update for a put tried (`kvOpAu1` of it: watchkv's
`put_au` over its KV invariant, cachekv's over the client's), each in a context with the examples'
request timeout (`context.WithTimeout(context.Background(), RequestTimeout)`, cancelled after the
call; 2026-10-23, `notes/client-timeouts-plan.md` D-T2: the context is an `isContext` whose `Err()`
returns client errors, by the premises `ContextReadErrs` and `ContextErrsClient` on Go's context
errors), logging each that returned no error in `w` with `okFact` (`wsInv`, the log's lock
invariant).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Writes
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.common

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

/-- See the file header. -/
abbrev Writer.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
    [ContextErrsClient (GF := GF) (hG := hG)]
    (cl : Loc) (ep : GoString) (V : client.WEnv GF)
    (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) (w : Loc) (tsl : GoSlice)
    (tried : List wkv) (lo hi : w64),
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  0 ≤ sint.Z lo → sint.Z lo ≤ sint.Z hi → sint.Z hi ≤ tried.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isNewClient cl [ep] V ∗ EtcdGrove.client.clientWriteOnce cl [ep] ∗
      isGrpcRpc ep go!"/etcdserverpb.KV/Put" (client.etcdPutSpec E γr cid mid) ∗
      tsl ↦*□ tried ∗
      iprop(□ ∀ (k v : GoString), ⌜(k, v) ∈ tried.map pairOf⌝ -∗
        kvOpAu1 γr.kv (.put (client.putKeyOp k v)) (fun _ => iprop(True))) ∗
      sync.isMutex (structFieldRef github_com.mit_pdos.etcd_grove.examples.common.Writes go!"Mu" w)
        (wsInv w E) }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.common.Writer))
      (Val #cl)) (Val #w)) (Val #tsl)) (Val #lo)) (Val #hi))
  {{ RET #(); True }}

end spec

end common
end EtcdGrove
end Perennial
