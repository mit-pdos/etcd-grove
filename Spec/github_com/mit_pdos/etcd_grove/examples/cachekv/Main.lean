/- Lean-first (no Rocq counterpart).

`Main(nw, nops)` (`examples/cachekv/cachekv.go`): watchkv's `Main` (`Spec/.../watchkv/Main.lean`)
with the watch read through etcd's cache: the writers' `nw * nops` Puts picked (`genAll`), one
etcd member started in process (as `examples/putget`'s `Main`, on `cachekv`'s ports), a client
with etcd's default configuration (its default retries; D29), a cache of the prefix `ck/` over the
client (`cache.New`, the default options), the cache's watch of the prefix from revision `2`,
`nw` writer goroutines, then, after they are done, the successful Puts' log, the watch read up to
their highest revision (`collect`) and the check (`check`, which panics if the watch did not
report exactly the writes).

**The triple:** from the package's `isPkgInit`, the right to listen on the client address
`127.0.0.1:23873`, the main thread's token and `Main`'s named premises (`cachekv.premises`,
watchkv's at `cachekv`'s configuration), `Main(nw, nops)` does not panic and returns `Ok` (`0`:
the check ran and passed), `Failed` (`1`: a step of the start failed) or `WatchEnded` (`2`: the
watch ended before it reported every successful Put). The premises are watchkv's: the cache needs
none of its own (its thread bound, `threadBound GF + 3 ≤ 2 ^ 31`, follows from the watchable
store's `2 ^ 29`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.cachekv.Defs
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.cachekv.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry) (nw nops : w64),
  putget.BootFacts id ctxs boot →
  threadBound GF ≤ 2 ^ 29 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota →
  storage.dbOpensOk → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  0 ≤ sint.Z nw → sint.Z nw < 2 ^ 31 → 0 ≤ sint.Z nops →
  sint.Z nw * sint.Z nops < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.cachekv ∗
      netAddrFree (GF := GF) go!"127.0.0.1:23873" ∗ threadTok ∗ premises N id ctxs boot }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.cachekv.Main)) (Val #nw))
      (Val #nops))
  {{ (r : w64), RET #r; ⌜r = W64 0 ∨ r = W64 1 ∨ r = W64 2⌝ }}

end spec

end cachekv
end EtcdGrove
end Perennial
