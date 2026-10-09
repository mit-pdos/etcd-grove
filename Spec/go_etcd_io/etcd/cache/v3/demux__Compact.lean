/-
`demux.Compact(compactRev)`. Lean-first (no Rocq counterpart); see `InvDemux.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvDemux

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `d.Compact(compactRev)`, by the writer: `purge` under the lock (the revision is not used). -/
abbrev demux.Compact.spec : Prop :=
  ∀ (d : Loc) (γd : DemuxNames) (cap : Nat) (C : DemuxCert GF) (c : DemuxCore)
    (compactRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isDemux d γd cap C ∗ demuxWriter d γd cap C c }}
    (App (Val (d @!! go.GoType.PointerType demux.ty @!! go!"Compact")) (Val #compactRev))
  {{ RET #(); demuxWriter d γd cap C DemuxCore.init }}

end spec

end EtcdGrove
end Perennial
