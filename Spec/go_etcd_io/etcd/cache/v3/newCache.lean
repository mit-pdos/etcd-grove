/-
`newCache(client, prefix, cfg, clock)` (`cache/cache.go`). Lean-first (no Rocq counterpart); see `InvNew.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `newCache(client, prefix, cfg, clock)`, for a client of etcd (`isEtcdClient`) and a clock
(`isClock`): it rejects a configuration with `HistoryWindowSize ≤ 0` or `BTreeDegree < 2`
(`nil` and an error); otherwise it builds the store, `ready`, the progress requestor and the demux
(`NewDemux`, which starts the resync loop), with the internal context
`context.WithCancel(context.Background())`, starts the watch loop (`getWatchLoop`, with the
store's and the demux's writers) and the progress requestor's loop (`run`) on the wait group, and
returns the cache with its handles (`newCacheResult`). A configuration it accepts must moreover be
`CfgBounded` (finding 5: a negative `PerWatcherBufferSize` panics later, and Perennial's
`make(chan T, n)` needs it below `2^32`; the capacity and the degree must not overflow). `context.isClosedchanInit` (`context`'s package-init fact about
`closedchan`) is for `WithCancel(Background())`. -/
abbrev newCache.spec : Prop :=
  ∀ (client : Loc) (pfx : GoString) (cfg : Config) (clk : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ context.isClosedchanInit ∗
      isEtcdClient client pfx ∗ isClock clk ∗ ⌜CfgValid cfg → CfgBounded cfg⌝ ∗
      ⌜threadBound GF + cacheWgOwedMax ≤ 2 ^ 31⌝ }}
    (App (App (App (App (Val (@! newCache)) (Val #client)) (Val #pfx)) (Val #cfg))
      (Val #(GoInterface.ok clk)))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err); newCacheResult pfx cfg c err }}

end spec

end EtcdGrove
end Perennial
