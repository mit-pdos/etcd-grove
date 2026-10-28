/-
`(*consistencyStore).WroteAt(owner, ownerUID, resource, rv)` (`consistency.go:133`): records that
the caller wrote `rv` of `resource` for `owner`. Lean-first.
-/
module

public import Proof.k8s_io.client_go.util.consistency.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace consistency

open Iris Iris.BI k8s_io.client_go.util.consistency

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.consistency.Assumptions]

/-- **`c.WroteAt(o, uid, gr, rv)`**, logically atomic: the owner's record (a new empty one if
there is none or it is for another UID) takes `rv` for `gr` if `rv` is well formed and newer
than the version there (`wroteAtM`). A version that is not well formed (`""`, `"0"`, ...) is not
recorded, though the record is still created or replaced: `EnsureReady` then has nothing to wait
for (`issues/nonissues/k8s-consistency-malformed-rv-ready.md`). The caller holds some permission
`T o q` for the owner (so no `EnsureReady(o)` runs meanwhile) and one of the map lock's reader
slots. -/
abbrev consistencyStore.WroteAt.spec : Prop :=
  ∀ (c : Loc) (γ : ConsNames) (T : Owner → Qp → IProp GF) (S : GMap GR LastSyncRVGetter)
    (G : GR → GoString → IProp GF) (o : Owner) (uid : GoString) (gr : GR) (rv : GoString) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.consistency ∗
      isCons c γ T S G ∗ T o q ∗ consReader c γ }}
  <<{ ∀∀ M, consState γ M }>>
    (App (App (App (App (Val (c @!! go.GoType.PointerType consistencyStore.ty @!! go!"WroteAt"))
      (Val #o)) (Val #uid)) (Val #gr)) (Val #rv)) @@ ↑consN
  <<{ consState γ (wroteAtM M o uid gr rv) }>>
  {{ RET #(); T o q ∗ consReader c γ }}

end spec

end consistency
end EtcdGrove
end Perennial
