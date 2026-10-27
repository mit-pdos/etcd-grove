/- Lean-first (no Rocq counterpart).

`(*KV).apply(e)` (kv.go:179): one committed entry, after the committed prefix
`ap` the replica applied (`runOwn`); a waiter of the entry's operation, if this replica
proposed it and the entry is the operation's first, gets the value after it (`waitP`).

`e` is a `*pb.Entry` holding the committed log entry `le` at index `idx` (`entRO`, read-only for
good: what `Ready.CommittedEntries` hands out, `Draft.committedEntriesAt`), read through its
getters.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- See the file header. -/
abbrev KV.apply.spec : Prop :=
  ∀ (γr : RKVNames) (γp : RepNames) (r : Loc) (id : w64) (n st : Loc)
    (ap : List Draft.LogEntry) (e : Loc) (le : Draft.LogEntry) (idx : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      isReplica γr γp r id n st ∗ runOwn γr r ap ∗ entRO e (le.toEntryM idx) ∗
      Draft.isCommittedLogLb γr.cluster (ap ++ [le]) }}
    (App (Val (r @!! go.GoType.PointerType rKVTy @!! go!"apply")) (Val #e))
  {{ RET #(); runOwn γr r (ap ++ [le]) }}

end spec

end kv
end EtcdGrove
end Perennial
