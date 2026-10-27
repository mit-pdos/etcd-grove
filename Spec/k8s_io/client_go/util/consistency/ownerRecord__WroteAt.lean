/-
`(*ownerRecord).WroteAt(resource, rv)` (`consistency.go:178`): raises the record's version of
`resource` to `rv` if `rv` is well formed and newer. Lean-first; internal: the pending write lands
(its abstract effect took place at `ensureWrittenRecord`).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.consistency.Assumptions]

/-- `r.WroteAt(gr, rv)` for the pending write `⟨r, gr, rv, q⟩`: under the record's lock its
versions become `wroteAtVs V gr rv`; the write is no longer pending, and the caller gets its
permission back. -/
abbrev ownerRecord.WroteAt.spec : Prop :=
  ∀ (γ : ConsNames) (T : Owner → Qp → IProp GF) (r : Loc) (s : RecS) (id : Nat) (gr : GR)
    (rv : GoString) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.consistency ∗
      inv consN (consInv γ T) ∗ isRec γ r s ∗ pendTok γ id ⟨r, gr, rv, q⟩ }}
    (App (App (Val (r @!! go.GoType.PointerType ownerRecord.ty @!! go!"WroteAt")) (Val #gr))
      (Val #rv))
  {{ RET #(); T s.owner q }}

end spec

end consistency
end EtcdGrove
end Perennial
