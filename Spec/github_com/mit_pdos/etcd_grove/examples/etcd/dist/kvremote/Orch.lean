/- Lean-first (no Rocq counterpart).

`Orch(nodes, ops, timeout)` (`examples/etcd/dist/kvremote`): the orchestrator, `remote.Run` of
txnlin's model (`Model()`, `isModel linkvtxnS`), the client machines at `nodes`, `Codec()`, txnlin's
`Gen`, `ops` operations per client and `Attempt`. It returns a verdict that is not porcupine's
`Illegal`, from `kvOrchPre ns ops`: for some cluster KV names `γk` and pending-map names `γ`, every
address in `ns` serves the store `kvR γk`'s calls (`remoteAddr`), the slot map (`mapCtx`), node 0's
invariant at the model's start (`pendCtx`, `pendLib`), and each address's call budget (`ops`
operations of `readTries` attempts); the bounds `remote.Run` takes (the time receipts', the number of
clients and of operations).

The spec is an instance of N7-kv's schema `Orch.specWith OP` (`etcd-safe-n7kv`,
`dist/kvremote/OrchWith.lean`), at `OP := kvOrchPre`. Proved in
`Proof/.../dist/kvremote/Orch.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Store
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

open Iris Iris.BI Net
open EtcdGrove EtcdGrove.etcd_txnlin
open go_etcd_io.etcd.server.v3.etcdserver mvcc
open github_com.mit_pdos.etcd_grove.examples.lib.remote

section share
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

/-- **txnlin's model at the global ghost state**: `linkvtxnS`'s model (`linkvtxnSG.M = linkvtxnS.M`, by
`rfl`), without its value representation (`rep`, over the heap, which needs a local ghost state). The pending
library's `pendCtx`/`pendLib` read only the model, so at `linkvtxnSG` they are those at `linkvtxnS`
(`pendCtx_linkvtxnSG`, `pendLib_linkvtxnSG`, `Proof/.../dist/kvremote/Orch.lean`). -/
def linkvtxnSG : github_com.anishathalye.porcupine.ModelSpec GF (linkv.PSet MS MI) where
  M := linkv.pM TS decOp
  rep _ _ _ := iprop(False)
  ioOk _ _ := iprop(True)
  ioOk_pers _ _ := by infer_instance

/-- **What the orchestrator needs** (see the file header), at the client machines' addresses `ns`
and `ops` operations per client; at the global ghost state only (the orchestrator machine's boot share). -/
def kvOrchPre (ns : List GoString) (ops : w64) : IProp GF :=
  iprop(∃ (γk : KVNames) (γ : PendNames),
    ⌜receiptBound GF ≤ 2 ^ 63 ∧ ns.length < 2 ^ 31 ∧ 0 ≤ sint.Z ops ∧
      (ns.length : Int) * sint.Z ops < 2 ^ 60⌝ ∗
    ([∗list] a ∈ ns, remoteAddr (Gg := Gg) (kvR (GF := GF) γk) a) ∗
    mapCtx (Gg := Gg) (I := VIn) ∗
    pendCtx (Gg := Gg) (kvR (GF := GF) γk) (linkvtxnSG (GF := GF)) γ ∗
    pendLib (Gg := Gg) (linkvtxnSG (GF := GF)) γ (linkvtxnSG (GF := GF)).M.init ∗
    [∗list] a ∈ ns, budUnits (Gg := Gg) a (sint.nat ops * readTries))

end share

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

/-- See the file header. -/
abbrev Orch.spec : Prop :=
  ∀ (nodes : GoSlice) (ns : List GoString) (ops tmo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote ∗
      nodes ↦*□ ns ∗ kvOrchPre (Gg := hG.goose_globalGS) ns ops }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Orch))
      (Val #nodes)) (Val #ops)) (Val #tmo))
  {{ (r : GoString), RET #r; ⌜r ≠ go!"Illegal"⌝ }}

end spec

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
