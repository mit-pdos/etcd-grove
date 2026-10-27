/-
`(*consistencyStore).Clear(owner, ownerUID)` (`consistency.go:139`): deletes the owner's record if
`ownerUID` is empty or is the record's. Lean-first.
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

/-- The abstract state `Clear` updates: the caller's (`none`), or nothing for `EnsureReady`'s
own call (`some _`: its record is deleted abstractly already, so `clearM` changes nothing). -/
def clearState (γ : ConsNames) (md : Option (Loc × RecS × Vs)) (M : GMap Owner Rec) : IProp GF :=
  match md with
  | none => consState γ M
  | some _ => iprop(True)

/-- What `EnsureReady`'s own call of `Clear` brings: its slot's receipt, cleared, for the record
`r` whose UID it passes. -/
def clearPre (γ : ConsNames) (o : Owner) (uid : GoString) (md : Option (Loc × RecS × Vs)) :
    IProp GF :=
  match md with
  | none => iprop(True)
  | some (r, s, V) => iprop(ensTok γ o ⟨r, V, true⟩ ∗ isRec γ r s ∗ ⌜s.owner = o ∧ s.uid = uid⌝)

/-- What it gets back: the permission it deposited. -/
def clearPost (T : Owner → Qp → IProp GF) (o : Owner) (md : Option (Loc × RecS × Vs)) :
    IProp GF :=
  match md with
  | none => iprop(True)
  | some _ => T o 1

variable [package_sem : k8s_io.client_go.util.consistency.Assumptions]

/-- **`c.Clear(o, uid)`**, logically atomic: `clearM M o uid` (the owner's record goes if `uid`
is empty or is its UID). Needs no permission: any thread may clear any owner's record. (`md` is
`none` for every caller but `EnsureReady`, whose call, `some`, also takes back the permission
`T o 1` it deposited in the store's invariant.) -/
abbrev consistencyStore.Clear.spec : Prop :=
  ∀ (c : Loc) (γ : ConsNames) (T : Owner → Qp → IProp GF) (S : GMap GR LastSyncRVGetter)
    (G : GR → GoString → IProp GF) (o : Owner) (uid : GoString) (md : Option (Loc × RecS × Vs)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.util.consistency ∗
      isCons c γ T S G ∗ clearPre γ o uid md }}
  <<{ ∀∀ M, clearState γ md M }>>
    (App (App (Val (c @!! go.GoType.PointerType consistencyStore.ty @!! go!"Clear"))
      (Val #o)) (Val #uid)) @@ ↑consN
  <<{ clearState γ md (clearM M o uid) }>>
  {{ RET #(); clearPost T o md }}

end spec

end consistency
end EtcdGrove
end Perennial
