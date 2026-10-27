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
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvNew

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage backend storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
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
  iintro !> %st %stop %m %u %Φ !> ⟨Hl, HPk, %Hpre, Hpay⟩ HΦ
  ihave Hs : ▷ saveReq γ P Pk b t ix iprop(True) iprop(True) $$ []
  · inext
    iapply saveReq_of_saveSpec
    iapply Hsv $$ Hb Ht
  iapply (hOn γ P W Pk b t bh ix lg st iprop(True) iprop(True) stop m u hH) $$ [Hl HPk Hs Hpay]
  · iframe Hspkg Hbpkg Hsch Hh Hs Hb Ht Hl HPk Hpay
    ipureintro; exact Hpre
  iintro !> ⟨%st', Hl, HPk, -, Hpay, %Hst⟩
  iapply HΦ
  iexists st'
  iframe Hl HPk Hpay
  ipureintro; exact Hst

/-- **The server's hooks serve a commit's request** (D22 the stored-index window, 2026-10-23): the
hooks `bh` of the backend `b` serve `X ⇒ Y` (`backend.hooksReq`) if the indexer's save does
(`saveReq`): `BackendHooks.OnPreCommitUnsafe` runs the save once. -/
theorem hooksReq_backendHooks
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (γ : BNames) (P : BParams) (W Pk : IProp GF) (b t bh : Loc) (ix : GoInterfaceOk) (lg : Loc)
    (hH : hooksParams P) (X Y : IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackendHooks bh ix lg ∗ isBackend γ P W Pk b ∗ bF go!"batchTx" b ↦□ t ∗
      saveReq γ P Pk b t ix X Y ⊢
      hooksReq γ P Pk b t (hooksIface bh) X Y := by
  iintro ⟨#Hspkg, #Hbpkg, #Hsch, #Hh, #Hb, #Ht, #Hsv⟩
  unfold hooksReq
  iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.BackendHooks.ty, #bh⟩
  isplitr
  · ipureintro; rfl
  iintro !> %st %stop %m %u %Φ !> ⟨Hl, HPk, HX, %Hpre, Hpay⟩ HΦ
  iapply (hOn γ P W Pk b t bh ix lg st X Y stop m u hH) $$ [Hl HPk HX Hpay] HΦ
  iframe Hspkg Hbpkg Hsch Hh Hsv Hb Ht Hl HPk HX Hpay
  ipureintro; exact Hpre

end proof

section proofLC
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- **The server's hooks' contract for every backend of a family** (D22 receiver epochs, S8b,
2026-10-24; `backend.hooksOk`, what an open's `openPre` takes): the hooks `bh` over the indexer
`ix` meet the hooks' contract of every backend made with `P`, `W`, `Pk` if the indexer's save
does, given the backend later: `BackendHooks.OnPreCommitUnsafe` runs the save once. -/
theorem hooksOk_backendHooks
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (P : BParams) (W Pk : BNames → IProp GF) (bh : Loc) (ix : GoInterfaceOk) (lg : Loc)
    (hH : hooksParams P) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackendHooks bh ix lg ∗
      □ (∀ (γ : BNames) (b t : Loc), ▷ isBackend γ P (W γ) (Pk γ) b -∗ bF go!"batchTx" b ↦□ t -∗
          ▷ saveSpec γ P (Pk γ) b t ix) ⊢
      hooksOk P W Pk (hooksIface bh) := by
  iintro ⟨#Hspkg, #Hbpkg, #Hsch, #Hh, #Hsv⟩
  unfold hooksOk
  iintro !> %γ %b %t #Hb #Ht
  unfold hooksSpec
  iright
  iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.BackendHooks.ty, #bh⟩
  isplitr
  · ipureintro; rfl
  iintro !> %st %stop %m %u %Φ !> ⟨Hl, HPk, %Hpre, Hpay⟩ HΦ
  ihave #Hs1 := Hsv $$ %γ %b %t Hb Ht
  ihave Hs : ▷ saveReq γ P (Pk γ) b t ix iprop(True) iprop(True) $$ []
  · inext
    iapply saveReq_of_saveSpec
    iexact Hs1
  iapply (hOn γ P (W γ) (Pk γ) b t bh ix lg st iprop(True) iprop(True) stop m u hH)
    $$ [Hl HPk Hs Hpay]
  · iframe Hspkg Hbpkg Hsch Hh Hs Hb Ht Hl HPk Hpay
    ipureintro; exact Hpre
  iintro !> ⟨%st', Hl, HPk, -, Hpay, %Hst⟩
  iapply HΦ
  iexists st'
  iframe Hl HPk Hpay
  ipureintro; exact Hst

end proofLC

end EtcdGrove
end Perennial
