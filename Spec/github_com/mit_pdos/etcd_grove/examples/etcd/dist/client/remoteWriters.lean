/- Lean-first (no Rocq counterpart).

`remoteWriters(nodes, tried, nops)` (`examples/etcd/dist/client/nodes.go`): **the watch workload's
writers at their machines** (#50 N10a, `notes/etcd-dist-plan.md` §24): writer `c`'s Puts are
`tried[c*nops, (c+1)*nops)`, sent to the client machine `nodes[c]` (`remote.Report` with
`writerCodec`, all at once, `CallAll`), which does them (`writerOp`); the result is the successful Puts
the answering writers' logs report.

**The triple:** from the writer machines' share (`writersShare Γ ns`: the slot map, each node's writer
service and one call's budget), the Puts `trs` (`len(nodes) * nops` of them, read-only, each one of the
plan `n.2.2` and small, `nops < 2 ^ 56` so that each writer's Puts and log encode in a message), and the
orchestrator's adapter (`kmInv (kmOf Γ n)`, the start's changes seen), `remoteWriters` returns the
successful Puts `oks`, each with `okFactK (kmOf Γ n) p` (the answering writers' `wQ`). The level token is
threaded. (Until 2026-11-26 a schema in the share, `specWith`: `lib/remote`'s wire carried only fixed
values, §24.4; the wire refactor, §28, made the slices describable.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WriterWire
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open etcd_dist etcdstart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

/-- See the file header. -/
abbrev remoteWriters.spec : Prop :=
  ∀ [π : NetProtoGS] [ρ : RemoteGS] (nodes tsl : GoSlice) (ns : List GoString) (trs : List wkv)
    (nops : w64) (Γ : DistView) (n : WN),
  0 ≤ sint.Z nops → sint.Z nops < 2 ^ 56 → (trs.length : Int) = ns.length * sint.Z nops →
  (∀ p ∈ trs, pairOf p ∈ n.2.2 ∧ wkvSmall p) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      levelTok 0 ∗ nodes ↦*□ ns ∗ tsl ↦*□ trs ∗ writersShare (Gg := hG.goose_globalGS) Γ ns ∗
      kmInv (kmOf Γ n) ∗ monoListLbOwn n.1 ([[]] : List (List mvcc.Change)) }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.remoteWriters))
      (Val #nodes)) (Val #tsl)) (Val #nops))
  {{ (sl : GoSlice), RET #sl; levelTok 0 ∗
      ∃ oks : List wrec, sl ↦* oks ∗ □ [∗list] p ∈ oks, etcd_partition.okFactK (kmOf Γ n) p }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
