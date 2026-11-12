/-
**Two members' certified logs are in prefix order** (W2 of `notes/watch-cut-plan.md`, the lifting
lemma; `notes/decisions.md` D32): a store log a member certified (`mvcc.certOk`, at its own
certificates' map) is the KV model of a committed prefix of the raft log (`kv_cert_read`); the
members share the raft names, so their committed prefixes are comparable (`srvRLogLb_prefix`), and
they agree on what the model reads (`c0`, `ch0`, `log0`), so the models of comparable prefixes are
comparable (`kvRaftOf_prefix`). A revision's changes, and so a watch's events at it, are then the
same at every member: what lets a watch resumed at another member continue one history. Lean-first
(no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver

section cmp
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- Two KV names that agree on what the model reads have the same model. -/
theorem kvModel_congr (γk γk' : KVNames) (hc0 : γk'.c0 = γk.c0) (hch : γk'.ch0 = γk.ch0)
    (hlog : γk'.log0 = γk.log0) (A : List EntryModel) : kvModel γk' A = kvModel γk A := by
  unfold kvModel; rw [hc0, hch, hlog]

end cmp

end EtcdGrove
end Perennial
