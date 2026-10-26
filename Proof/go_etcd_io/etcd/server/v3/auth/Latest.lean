/-
**The checks at the latest state** (the auth plan's E2r, 2026-10-26; `notes/decisions.md`, "E2r of
the auth plan"). The checks' specs (`isOpPermitted`, `IsAdminPermitted`, ...) give their verdict
at *some* recorded state per read (S3: `permVerdict`, `adminVerdict`), all a concurrent reader can
be promised. The apply thread is the store's only writer and holds the admin side's authority
(`authOwn`, S4f) between its batch transactions, so its own checks can be promised the latest state
of that authority (`histLast`): this file states and proves those variants beside the generic
specs, over the backend's read contract at the latest state (`authReadTxOk`'s second clause).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__lockedReadTx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.lockedReadTx()` for a caller holding the admin side's authority `hs` (the apply thread):
the locked read transaction is at the latest state (`authReadTxLockedL`); the authority back. -/
abbrev auth.authStore.lockedReadTx.specL : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (hs : List auth.AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      beRd st R M ∗ R ∗ authOwn M hs }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"lockedReadTx")) (Val #()))
  {{ (tx : GoInterface), RET #tx; beRd st R M ∗ authReadTxLockedL tx R M hs ∗ authOwn M hs }}

end spec

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.lockedReadTx.wp_latest :
    auth.authStore.lockedReadTx.specL (GF := GF) (hG := hG) := by
  intro st R M hs
  wp_start as ⟨#Hinv, Hrd, HR, Hown⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold authInv at Hinv
  icases Hinv with ⟨%Hst, -, -, -, -, -, -⟩
  iunfold beRd at Hrd
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hlk, HP⟩
  iunfold beP at HP
  icases HP with ⟨%be, Hbe, #Hbeok⟩
  ihave #Hbeok' := Hbeok
  iunfold authBackendOk at Hbeok'
  icases Hbeok' with ⟨%bi, %Hbi, #HRT⟩
  subst Hbi
  wp_auto
  wp_apply HRT as %tx Htx
  iunfold authReadTxOk at Htx
  icases Htx with ⟨%ti, %Hti, Htx⟩
  subst Hti
  icases Htx with ⟨%Hs, -, #HRL, #Hreads⟩
  wp_auto
  wp_bind (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
  iapply HRL $$ %hs [HR Hown]
  · iframe HR Hown
  inext
  iintro ⟨%sta, Htok, #Hsnap, Hown, %Hlast⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hbe] as Hrd
  · inext; iunfold beP; iexists _; iframe Hbe; iexact Hbeok
  iapply HΦ
  iunfold beRd
  iframe Hrd Hown
  iunfold authReadTxLockedL
  iexists ti
  isplitr
  · ipureintro; rfl
  iexists sta, Hs
  iframe Htok
  iframe #
  ipureintro; exact Hlast

end proof

end EtcdGrove
end Perennial
