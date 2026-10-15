/-
`New(client, prefix, opts...)` (`cache/cache.go`). Lean-first (no Rocq counterpart); see `InvNew.lean`.
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

/-- **`New(client, prefix, opts...)`**, for a client of etcd for the prefix (`isEtcdClient`) and
options with the transformers `gs` (`cfgOptsAt`): the configuration is `defaultConfig()` with
the options applied in order (`cfgApply gs defaultConfigVal`); if it is rejected
(`HistoryWindowSize ≤ 0` or `BTreeDegree < 2`) `New` returns `nil` and an error, otherwise a
cache for the prefix and the configuration with its handles (`newCacheResult`: `isCacheFields`,
the readers of `Get`, the slots of `Watch`, the handles of `WaitForNextResync`, the token of
`Close`), its resync loop, watch loop and progress requestor running on the real clock
(`realClock`). An accepted configuration must be `CfgBounded` (finding 5). It takes
`context.isClosedchanInit`, `context`'s package-init fact about `closedchan` (persistent; a
program's `main` has it once `context` is initialized), which the internal context's
`WithCancel(Background())` needs. -/
abbrev New.spec : Prop :=
  ∀ (client : Loc) (pfx : GoString) (sl : GoSlice) (gs : List (Config → Config)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ context.isClosedchanInit ∗
      isEtcdClient client pfx ∗ cfgOptsAt sl gs ∗
      ⌜CfgValid (cfgApply gs defaultConfigVal) → CfgBounded (cfgApply gs defaultConfigVal)⌝ ∗
      ⌜threadBound GF + cacheWgOwedMax ≤ 2 ^ 31⌝ }}
    (App (App (App (Val (@! New)) (Val #client)) (Val #pfx)) (Val #sl))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      newCacheResult pfx (cfgApply gs defaultConfigVal) c err }}

end spec

end EtcdGrove
end Perennial
