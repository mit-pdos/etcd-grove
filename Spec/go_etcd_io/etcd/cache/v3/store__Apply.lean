/-
`store.Apply(resp)`. Lean-first (no Rocq counterpart); see `InvStore.lean`.
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

/-- `s.Apply(resp)`, by the writer: the store's state becomes `(applyResp cap st r).1`, and
the error is `nil` iff `(applyResp cap st r).2` (see `applyResp` for the cases, and
`applyEvents` for what a failed delete leaves). The events must be in revision order
(`EvRevSorted`, as etcd sends them), and the caller certifies every snapshot `Apply` appends
(`snapCerts E (applyRespSnaps st r)`) and every revision it may move the latest revision to
(`revCerts R (applyRespRevs st r)`). -/
abbrev store.Apply.spec : Prop :=
  ∀ (s : Loc) (γ : StoreNames) (cap : Nat) (E : w64 → KvMap → IProp GF) (R : w64 → IProp GF) (st : StoreState)
    (resp : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isStore s γ cap ∗ storeWriter s γ cap E R st ∗ respAt resp r ∗ ⌜EvRevSorted r.events⌝ ∗
      snapCerts E (applyRespSnaps st r) ∗ revCerts R (applyRespRevs st r) }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Apply")) (Val #resp))
  {{ (err : GoInterface), RET #err;
      storeWriter s γ cap E R (applyResp cap st r).1 ∗
      storeRevLb γ (applyResp cap st r).1.latestRev ∗
      ⌜if (applyResp cap st r).2 then err = GoInterface.nil else ∃ e, err = GoInterface.ok e⌝ }}

end spec

end EtcdGrove
end Perennial
