/-
`schema.UnsafeUpdateConsistentIndexRaftTerm(tx, index, raftTerm)` (keepfix (c), fork b1512efdd). Lean-first (no
Rocq counterpart); see `InvCindex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.storage

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- `UnsafeUpdateConsistentIndexRaftTerm(tx, index, raftTerm)`: unless `index` or `raftTerm` is 0, puts the
16 bytes `index ++ raftTerm` (big-endian) at the meta key `consistentIndexRaftTerm` of the batch transaction
`tx` (`metaRtWriter`, its token `PTr`): the key becomes `rtAfterSave r index raftTerm`. -/
abbrev schema.UnsafeUpdateConsistentIndexRaftTerm.spec : Prop :=
  ∀ (tx : GoInterfaceOk) (TMx : MetaCI → Option (w64 × w64) → IProp GF) (PTr : IProp GF) (m : MetaCI)
    (r : Option (w64 × w64)) (index raftTerm : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ metaRtWriter tx TMx PTr ∗
      TMx m r ∗ PTr }}
    (App (App (App (Val (@! schema.UnsafeUpdateConsistentIndexRaftTerm)) (Val #(GoInterface.ok tx)))
      (Val #index)) (Val #raftTerm))
  {{ RET #(); TMx m (rtAfterSave r index raftTerm) }}

end spec

end EtcdGrove
end Perennial
