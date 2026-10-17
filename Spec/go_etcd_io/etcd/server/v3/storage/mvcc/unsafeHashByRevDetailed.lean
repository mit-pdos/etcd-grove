/-
`unsafeHashByRevDetailed` (`hash.go`, etcd-io/etcd#21202): the hash of the `Key` bucket through a
locked read transaction, with each hashed pair's own hash (pr-verify/etcd-21202; `HashParams.lean`).
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

/-- `unsafeHashByRevDetailed(tx, c, rev, keep)`, as `unsafeHashByRev`'s spec: of a read
transaction `rt` (`metaReadTx`) and a kept set `keep` (read at a fraction, given back), returns
some error (`UnsafeForEach`'s) and, if it is `nil`, a result whose total hash and own fields have
compaction revision `c` and revision `rev` (what `newKVHasherDetailed(c, rev, keep)` sets,
`Hash()` returns, and the literal copies; on an error the code returns `DetailedHashResult{}`,
all zero, unlike `unsafeHashByRev`), the hash values and the per-pair list opaque (crc32). Like
`unsafeHashByRev`'s, the axiom assumes that `rt`'s `UnsafeForEach` over the `Key` bucket returns
(the backend's does: `metaReadTx` does not specify it). -/
abbrev mvcc.unsafeHashByRevDetailed.spec : Prop :=
  ∀ (rt : GoInterfaceOk) (c rev : w64) (keep : GoMap) (dq : DFrac) (A : GMap Revision Unit),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.metaReadTx rt ∗ ownMap keep dq A }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.unsafeHashByRevDetailed))
      (Val #(GoInterface.ok rt))) (Val #c)) (Val #rev)) (Val #keep))
  {{ (d : DetailedHashResult) (err : GoInterface), RET (PairV #d #err);
      ownMap keep dq A ∗ ⌜err = GoInterface.nil → d.TotalHash'.CompactRevision' = c ∧
        d.TotalHash'.Revision' = rev ∧ d.CompactRevision' = c ∧ d.Revision' = rev⌝ }}

end spec

end EtcdGrove
end Perennial
