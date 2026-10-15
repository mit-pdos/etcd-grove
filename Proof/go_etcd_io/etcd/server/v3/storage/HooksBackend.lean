/-
The backend over the server's hooks (2026-10-13, unit 8). Lean-first (no Rocq counterpart); see
`InvHooks.lean` and `notes/decisions.md`, "The server's backend hook (unit 8)".

`isBackend_backendHooks`: a backend whose `hooks` field is the server's `BackendHooks` `bh`
(`isBackendNH`: every fact of `isBackend` but the hooks' contract) is `isBackend`, the hooks'
contract derived from `BackendHooks.OnPreCommitUnsafe`'s proof, given the indexer's save
(`saveSpec`) over that backend. By Löb induction (`isBackend_of_hooks`): the hook's puts need
the backend's contract, which holds the hook's.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.BackendHooks__OnPreCommitUnsafe
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.HooksLoeb

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage backend storage

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- **The backend over the server's hooks**: `isBackendNH` with the `hooks` field the server's
`BackendHooks` `bh` (indexer `ix`), and the indexer's save over the backend (`saveSpec`, given
`isBackend`), make `isBackend`: the hooks' contract is `OnPreCommitUnsafe`'s. -/
theorem isBackend_backendHooks
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b bh : Loc) (ix : GoInterfaceOk) (lg : Loc)
    (hH : hooksParams P) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackendHooks bh ix lg ∗ isBackendNH γ P W Pk b (hooksIface bh) ∗
      □ (isBackend γ P W Pk b -∗ ∀ t : Loc, bF go!"batchTx" b ↦□ t -∗ saveSpec γ P Pk b t ix) ⊢
      isBackend γ P W Pk b := by
  iintro ⟨#Hspkg, #Hbpkg, #Hsch, #Hh, #Hnh, #Hsv⟩
  iapply isBackend_of_hooks γ P W Pk b (hooksIface bh)
  iframe Hnh
  iintro !> #Hb %t #Ht
  unfold hooksSpec
  iright
  iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.BackendHooks.ty, #bh⟩
  isplitr
  · ipureintro; rfl
  iintro !> %st %Φ !> ⟨Hl, HPk, %Hpre⟩ HΦ
  ihave Hs : ▷ saveSpec γ P Pk b t ix $$ []
  · inext
    iapply Hsv $$ Hb Ht
  iapply (hOn γ P W Pk b t bh ix lg st hH) $$ [Hl HPk Hs] HΦ
  iframe Hspkg Hbpkg Hsch Hh Hs Hb Ht Hl HPk
  ipureintro; exact Hpre

end proof

end EtcdGrove
end Perennial
