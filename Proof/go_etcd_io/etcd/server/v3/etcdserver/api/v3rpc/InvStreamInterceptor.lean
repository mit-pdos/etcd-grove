/-
**The server's stream interceptor** (`v3rpc/interceptor.go`'s `newStreamInterceptor` and
`monitorLeader`; the watch slice's unit W-W, 2026-10-15): the vocabulary of their specs.
Lean-first (no Rocq counterpart).

* `v3rpc.streamsMapIs smap` (persistent): the `*streamsMap` `monitorLeader` returns: its `mu` a
  mutex whose invariant says the `streams` field holds an empty map. The map stays empty because
  the only insertion (`smap.streams[ss] = struct{}{}`) is in the interceptor's require-leader
  branch, which `runsNoRequireLeader` excludes; the monitor goroutine only replaces it by a fresh
  empty map. So its `for ss := range smap.streams` body never runs.
* `v3rpc.runsNoRequireLeader` (persistent; **a premise about the deployment**): no client of the
  server asks for a leader on a stream. For every run context grpc gives a handler (`isContext ci
  cd ∗ grpcRunCtx ci`), `metadata.FromIncomingContext(ci)` meets its generic triple
  (`metadata.FromIncomingContext.spec`: no metadata, or a fresh map of non-empty fresh slices),
  and in the map the key `rpctypes.MetadataRequireLeaderKey` (`"hasleader"`, the value `kl` of
  the package variable) has no value or one whose first element is not
  `rpctypes.MetadataHasLeader` (`"true"`, the value `hl`): the condition of the interceptor's
  `if ks := md[MetadataRequireLeaderKey]; len(ks) > 0 && ks[0] == MetadataHasLeader` is false.
  The slice's clients (the recipes, the cache) never call `clientv3.WithRequireLeader`, which is
  what puts the pair in a stream's outgoing metadata; the premise is to be discharged by the
  client-side derivation (W-C). It is deliberately weak: a `hasleader` key with another value is
  allowed, and the API-version and metrics paths are proved for any metadata.

Why the require-leader branch is excluded rather than proved (`notes/decisions.md`, "The stream
interceptor's require-leader premise"): it wraps the stream in a `serverStreamWithCtx` whose
context is `newCancellableContext(ss.Context())`, which the handler would need as a run context
(`isContext ∗ grpcRunCtx`): (1) Perennial's `WithCancel` over a general `isContext` parent
(`wp_WithCancel_any`; the strong `context.WithCancel.spec` needs a `*cancelCtx` parent) relates
the child's `Value` to nothing of the parent's, so `grpcRunCtx` does not transfer; (2)
`cancellableContext.Err()` returns the stored reason after `Cancel`'s unlock and before
`c.cancel()`, a non-nil `Err()` while `Done()` is open, against `context.Context`'s contract, so
the wrapper is not an `isContext` (`issues/etcd-stream-interceptor-err-before-done.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvQuota
public import Proof.google_golang_org.grpc.InvGrpcStream
public import Spec.google_golang_org.grpc.metadata.FromIncomingContext

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- The invariant of a `*streamsMap`'s mutex: the `streams` field holds an empty map (see the file
header). -/
def v3rpc.streamsMapInv (smap : Loc) : IProp GF :=
  iprop(∃ mp : GoMap, structFieldRef v3rpc.streamsMap go!"streams" smap ↦ mp ∗
    mp ↦$ (∅ : GMap GoInterface Unit))

/-- **The `*streamsMap` `smap`** (persistent; see the file header). -/
def v3rpc.streamsMapIs (smap : Loc) : IProp GF :=
  sync.isMutex (structFieldRef v3rpc.streamsMap go!"mu" smap) (v3rpc.streamsMapInv smap)

instance v3rpc.streamsMapIs_persistent (smap : Loc) :
    Persistent (v3rpc.streamsMapIs (GF := GF) smap) := by
  unfold v3rpc.streamsMapIs; infer_instance

/-- **No stream asks for a leader** (persistent; a premise about the deployment, see the file
header): at every run context, `metadata.FromIncomingContext` gives no metadata, or metadata in
which the require-leader key's values (if any) do not start with `"true"`. -/
def v3rpc.runsNoRequireLeader : IProp GF :=
  iprop(□ ∀ (kl hl : GoString) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
    globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.MetadataRequireLeaderKey ↦□ kl -∗
    globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.MetadataHasLeader ↦□ hl -∗
    context.isContext ci cd -∗ grpcRunCtx ci -∗
    {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc.metadata }}
      (App (Val (@! google_golang_org.grpc.metadata.FromIncomingContext))
        (Val #(GoInterface.ok ci)))
    {{ (md : GoMap) (ok : Bool), RET (PairV #md #ok);
        ⌜ok = false⌝ ∨ ∃ m : GMap GoString GoSlice, md ↦$ m ∗
          [∗map] k ↦ sl ∈ m, ∃ vs : List GoString, sl ↦* vs ∗ ⌜vs ≠ []⌝ ∗
            ⌜k = kl → vs.head? ≠ some hl⌝ }})

instance v3rpc.runsNoRequireLeader_persistent :
    Persistent (v3rpc.runsNoRequireLeader (GF := GF)) := by
  unfold v3rpc.runsNoRequireLeader; infer_instance

end defs

end EtcdGrove
end Perennial
