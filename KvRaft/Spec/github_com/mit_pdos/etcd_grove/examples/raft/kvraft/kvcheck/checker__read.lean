/-
`c.read(key)` (kvcheck.go), at kvraft's store (`kvFacts γ cf`, the checker's counters `kvCnt γ n`:
`StoreDefs.lean`): logically atomic over the store's map (kvdurable's `Cluster.Read`), returning `m key`:
reads of `key` at random members over kvraft's wire protocol, each with a fresh sequence number (whose
law mints the read's context at every replica, after the log of the read's start), until one answers.
Partial correctness: a read no replica ever answers keeps `read` looping.
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.StoreDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open raft_kvreconf (KVMap)
open Iris Iris.BI Net kvraft

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]
variable [field_sem : net.FieldAssumptions] [go.IntoValInj GoString]
variable [kvraft_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev checker.read.spec : Prop :=
  ∀ (γ : KdNames) (cf : List w8 → Prop) (c : Loc) (ls : List GoString) (key : GoString)
    (Φ : List w8 → IProp GF),
  (key.length : Int) < 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck ∗
      isCheckerP (kvFacts γ cf) c (kvCnt γ ls.length) ls ∗ rkvInv γ ∗
      AU <{ ∃∃ (x : KVMap), rkvVal γ x }> @ kdMask, ∅ <{ rkvVal γ x, COMM Φ (x key) }> }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker.ty @!! go!"read"))
      (Val #key))
  {{ (v : GoString), RET #v; Φ v }}

end spec

end raft_kvcheck
end EtcdGrove
end Perennial
