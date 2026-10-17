/-
`clientv3.NewCtxClient(ctx, opts...)` (`client/v3/client.go`) as PR etcd-io/etcd#21809 changes it:
the client it returns has the default call options, as `New`'s do. Lean-first (no Rocq
counterpart); see `InvCtxClient.lean`.

Before the PR, `callOpts` was left `nil`: every call of the `KV`, `Lease`, `Watcher`, ... a caller
builds over the client (`NewKVFromKVClient(remote, c)`, ...) passed no call options, so the
connection's default call options applied (the caller's `grpc.WithDefaultCallOptions`, else grpc's
own: send limit `MaxInt32`, receive limit 4 MiB, `WaitForReady(false)`). After it, every call
passes the three defaults (`defaultCallOptVals`), which override the connection's (grpc applies a
call's options after the connection's). The postcondition's `callOpts ↦ dsl` with
`dsl ↦*□ defaultCallOptVals` is what the PR changes: the old code returns `callOpts` = the nil
slice, of length 0.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvCtxClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `NewCtxClient(parent, opts...)`, for a context `parent` (`isContext`), options that write
only the logger (`ctxClientOptsAt`) and the package's default call options `dsl`
(`defaultCallOptsVar`): a new client `c` whose
* call options are `dsl`, the defaults `New` gives a client (`defaultCallOptVals`: wait for
  ready, send limit 2 MiB, receive limit `MaxInt32`; `callOptsAt dsl`: full, each one a grpc
  option holding only scalars, what `NewKV`'s and the KV path's proofs need of a client's call
  options);
* logger is non-nil (the last option's, or `zap.NewNop()` if it left none), owned
  (`isClientLogger_alloc` makes it what `GetLogger` needs);
* context is a child of `parent` (`WithCancel`'s);
* `KV`, `Watcher`, `Lease`, `Cluster`, `Auth`, `Maintenance` are `nil`, and owned: the caller fills
  them (`v3client.New`). -/
abbrev NewCtxClient.spec : Prop :=
  ∀ (parent : GoInterfaceOk) (s : context.ContextDesc (IProp GF)) (opts dsl : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ context.isContext parent s ∗
      ctxClientOptsAt opts ∗ defaultCallOptsVar dsl }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.NewCtxClient)) (Val #(interface.ok parent)))
      (Val #opts))
  {{ (c : Loc), RET #c; ⌜c ≠ null⌝ ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"callOpts" c ↦ dsl ∗
      dsl ↦*□ defaultCallOptVals ∗ callOptsAt dsl ∗
      (∃ lg : Loc, sync.atomic.ownPointer (hG := hG) (T' := go_uber_org.zap.Logger)
        (clientLgAddr c) (DFrac.own 1) lg ∗ ⌜lg ≠ null⌝) ∗
      (∃ (ctx' : GoInterfaceOk) (γ' : context.ContextNames),
        structFieldRef go_etcd_io.etcd.client.v3.Client go!"ctx" c ↦ (GoInterface.ok ctx') ∗
        context.isContext ctx' { s with PDone := iprop(True), Done_gn := γ' }) ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"Cluster" c ↦
        (zero_val go_etcd_io.etcd.client.v3.Cluster) ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" c ↦
        (zero_val go_etcd_io.etcd.client.v3.KV) ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"Lease" c ↦
        (zero_val go_etcd_io.etcd.client.v3.Lease) ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"Watcher" c ↦
        (zero_val go_etcd_io.etcd.client.v3.Watcher) ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"Auth" c ↦
        (zero_val go_etcd_io.etcd.client.v3.Auth) ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"Maintenance" c ↦
        (zero_val go_etcd_io.etcd.client.v3.Maintenance) }}

end spec

end EtcdGrove
end Perennial
