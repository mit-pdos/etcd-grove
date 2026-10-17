/-
`unsafeHashByRev` (`hash.go`): the hash of the `Key` bucket through a locked read transaction
(pr-verify/etcd-21202; `HashParams.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.HashParams

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `unsafeHashByRev(tx, c, rev, keep)`, of a read transaction `rt` (`metaReadTx`: the model
does not track what it reads) and a kept set `keep` (read at a fraction, given back), returns a
hash whose compaction revision and revision are `c` and `rev` (`kvHasher.Hash` returns its
fields `newKVHasher(c, rev, keep)` set), its value opaque (the crc32 of the pairs
`kvHashIncludes` keeps, `tx.UnsafeForEach` of the `Key` bucket), and some error (`UnsafeForEach`'s). The axiom assumes
that `rt`'s `UnsafeForEach` over the `Key` bucket returns (the backend's does; `metaReadTx`, the
compaction's view-less read transaction, does not specify it). -/
abbrev mvcc.unsafeHashByRev.spec : Prop :=
  ∀ (rt : GoInterfaceOk) (c rev : w64) (keep : GoMap) (dq : DFrac) (A : GMap Revision Unit),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.metaReadTx rt ∗ ownMap keep dq A }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.unsafeHashByRev))
      (Val #(GoInterface.ok rt))) (Val #c)) (Val #rev)) (Val #keep))
  {{ (h : KeyValueHash) (err : GoInterface), RET (PairV #h #err);
      ownMap keep dq A ∗ ⌜h.CompactRevision' = c ∧ h.Revision' = rev⌝ }}

end spec

end EtcdGrove
end Perennial
