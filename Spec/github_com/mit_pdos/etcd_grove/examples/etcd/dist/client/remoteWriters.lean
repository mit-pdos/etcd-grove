/- Lean-first (no Rocq counterpart).

`remoteWriters(nodes, tried, nops)` (`examples/etcd/dist/client/nodes.go`): **the watch workload's
writers at their machines** (#50 N10a, `notes/etcd-dist-plan.md` §24): writer `c`'s Puts are
`tried[c*nops, (c+1)*nops)`, sent to the client machine `nodes[c]` (`remote.Report` with
`writerCodec`, all at once, `CallAll`), which does them (`writerOp`); the result is the successful Puts
the answering writers' logs report.

`remoteWriters.specWith WS` is a **schema**, parametric in the writer machines' share `WS Γ ns` (what
the start gives the orchestrator for the writer service at the machines `ns`): `RunWatch`'s proof takes
it as a hypothesis. **Not proved yet** (plan §24.4): `remote.Report.spec` and `ServeClient.spec` carry
a call's input and output as Go values that are functions of their models (`RWire.iv`/`ov`,
`wireOk`'s `DecIn`/`DecOut` returning exactly the value encoded), which a slice is not (`writerCodec`'s
input is a `[]etcdstart.KV`, its output a `[]etcdstart.PutRec`). Either the remote library's wire
becomes value predicates (a proof refactor of `Net/.../lib/remote`, no trust; on M1's line), or the
codec's values become slice-free (a Go change, as `txnlin`'s fixed-arity `Input`/`Output`).

**The triple:** from the writer machines' share, the Puts `trs` (`len(nodes) * nops` of them,
read-only) each one of the plan `P` and small, and the orchestrator's adapter (`kmInv γ` at the view's
KV, `γ.W = wkW P`, the start's changes seen), `remoteWriters` returns the successful Puts `oks`, each
with `okFactK γ p` (`writerOp.spec`'s post). The level token is threaded.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WatchWorkDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open etcd_dist etcdstart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

/-- See the file header. -/
abbrev remoteWriters.specWith (WS : DistView → List GoString → IProp GF) : Prop :=
  ∀ (nodes tsl : GoSlice) (ns : List GoString) (trs : List wkv) (nops : w64) (Γ : DistView)
    (γ : KMNames) (P : List (GoString × GoString)),
  0 ≤ sint.Z nops → (trs.length : Int) = ns.length * sint.Z nops → γ.kv = Γ.kv →
  γ.W = etcd_partition.wkW P → (∀ p ∈ trs, pairOf p ∈ P ∧ wkvSizeOk p) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ nodes ↦*□ ns ∗ tsl ↦*□ trs ∗ WS Γ ns ∗ kmInv γ ∗
      monoListLbOwn γ.ch ([[]] : List (List mvcc.Change)) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.remoteWriters))
      (Val #nodes)) (Val #tsl)) (Val #nops))
  {{ (sl : GoSlice), RET #sl; levelTok 0 ∗
      ∃ oks : List wrec, sl ↦* oks ∗ □ [∗list] p ∈ oks, etcd_partition.okFactK γ p }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
