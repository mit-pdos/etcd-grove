/-
`(*consistencyStore).ensureWrittenRecord(owner, ownerUID)` (`consistency.go:112`): the owner's
record for `ownerUID`, created (or replacing one for another UID) if needed. Lean-first; internal:
`WroteAt`'s linearization point (the write it is called for, `gr` and `rv`, becomes pending).
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

/-- `c.ensureWrittenRecord(o, uid)`, for `WroteAt(o, uid, gr, rv)`: its linearization point is
`WroteAt`'s (`wroteAtM`), when it finds the owner's record for `uid` or installs a new one; it
returns the record, registered (`isRec`), and the receipt of the write as pending (`pendTok`),
which holds the caller's permission `T o q` until `ownerRecord.WroteAt` writes it. -/
abbrev consistencyStore.ensureWrittenRecord.spec : Prop :=
  ∀ (c : Loc) (γ : ConsNames) (T : Owner → Qp → IProp GF) (S : GMap GR LastSyncRVGetter)
    (G : GR → GoString → IProp GF) (o : Owner) (uid : GoString) (gr : GR) (rv : GoString) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.consistency ∗
      isCons c γ T S G ∗ T o q ∗ consReader c γ }}
  <<{ ∀∀ M, consState γ M }>>
    (App (App (Val (c @!! go.GoType.PointerType consistencyStore.ty @!! go!"ensureWrittenRecord"))
      (Val #o)) (Val #uid)) @@ ↑consN
  <<{ consState γ (wroteAtM M o uid gr rv) }>>
  {{ (r : Loc), RET #r; consReader c γ ∗ ∃ (s : RecS) (id : Nat),
      isRec γ r s ∗ ⌜s.owner = o⌝ ∗ pendTok γ id ⟨r, gr, rv, q⟩ }}

end spec

end consistency
end EtcdGrove
end Perennial
