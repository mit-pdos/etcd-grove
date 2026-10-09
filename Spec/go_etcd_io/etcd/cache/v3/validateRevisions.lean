/-
`validateRevisions(resp, latestRev)`. Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `validateRevisions(resp, latestRev)`: `nil` iff `validRevisions r latestRev` (a progress
notification not behind `latestRev`, or events all above it), else some error. -/
abbrev validateRevisions.spec : Prop :=
  ∀ (resp : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (latestRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ respAt resp r }}
    (App (App (Val (@! validateRevisions)) (Val #resp)) (Val #latestRev))
  {{ (err : GoInterface), RET #err;
      ⌜if validRevisions r latestRev then err = GoInterface.nil
        else ∃ e, err = GoInterface.ok e⌝ }}

end spec

end EtcdGrove
end Perennial
