/-
`store.checkPrevCompactionCompleted` (`kvstore.go`) (2026-10-13, unit 5a).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.checkPrevCompactionCompleted()`: some boolean (the meta keys read through a `ReadTx`
with no view, `metaReadTx`; racy with the job, which writes `finishedCompactRev`: the result only
decides whether the next compaction's hash is stored, which the model ignores). -/
abbrev mvcc.store.checkPrevCompactionCompleted.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isStore s γ }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"checkPrevCompactionCompleted")) (Val #()))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
