/-
`demux.LatestRev()`. Lean-first (no Rocq counterpart); see `InvDemux.lean`.
-/
import EtcdGrove.Cache.InvDemux

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

/-- `d.LatestRev()` (under a read lock): the `maxRev` of some state of the demux. (No lower
bound: `purge` resets `maxRev` to `0`.) -/
abbrev demux.LatestRev.spec : Prop :=
  ∀ (d : Loc) (γd : DemuxNames) (cap : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isDemux d γd cap ∗ demuxHandle d γd cap }}
    (App (Val (d @!! go.GoType.PointerType demux.ty @!! go!"LatestRev")) (Val #()))
  {{ (r : w64), RET #r; demuxHandle d γd cap ∗ ⌜∃ c, DemuxInv cap c ∧ r = c.maxRev⌝ }}

end spec

end EtcdGrove
end Perennial
