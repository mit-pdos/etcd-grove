/- Lean-first (no Rocq counterpart).

`Main(nw, nops)` (`examples/watchkv/watchkv.go`; D23): the writers' `nw * nops` Puts picked
(`genAll`), one etcd member started in process (as `examples/putget`'s `Main`, on `watchkv`'s
ports), a client with etcd's default configuration (its default retries; D29), a prefix watch on
`wk/` from revision `1`, `nw` writer goroutines, then, after they are done, the successful Puts'
log, the watch read up to their highest revision (`collect`) and the check (`check`, which panics
if the watch did not report exactly the writes).

**The triple:** from the package's `isPkgInit`, the right to listen on the client address
`127.0.0.1:23872`, the main thread's token and `Main`'s named premises (`watchkv.premises`,
putget's at `watchkv`'s configuration and the watch stream's transport premise), `Main(nw, nops)`
does not panic and returns `Ok` (`0`: the check ran and passed), `Failed` (`1`: a step of the start
failed) or `WatchEnded` (`2`: the watch ended before it reported every successful Put). The pure
premises are putget's (`putget.Main.spec`), the thread bound below the watchable
store's lock's reader limit (`2 ^ 29`), and the bounds on `nw` and `nops`; the class premises are
the client watcher's (`isNewClient_watcher`'s).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Defs
public import Proof.go_etcd_io.etcd.client.v3.ErrorsNewOk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.watchkv.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [ErrorStringLeaf] [ErrorStringNoGRPCStatus] [context.ErrorStringIsError]
    [EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)] [ContextErrsClient (GF := GF) (hG := hG)]
    (N : Nat) (id : w64) (bootLog : List EntryM) (nw nops : w64),
  putget.BootFacts id bootLog →
  threadBound GF ≤ 2 ^ 29 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota →
  storage.dbOpensOk → v3rpc.ServerMethodSets →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  0 ≤ sint.Z nw → sint.Z nw < 2 ^ 31 → 0 ≤ sint.Z nops →
  sint.Z nw * sint.Z nops < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.watchkv ∗
      netAddrFree (GF := GF) go!"127.0.0.1:23872" ∗ threadTok ∗ premises N id bootLog }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.watchkv.Main)) (Val #nw))
      (Val #nops))
  {{ (r : w64), RET #r; ⌜r = W64 0 ∨ r = W64 1 ∨ r = W64 2⌝ }}

end spec

end watchkv
end EtcdGrove
end Perennial
