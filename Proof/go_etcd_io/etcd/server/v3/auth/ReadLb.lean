/-
**The reads no older than a published index** (the auth plan's E3g, 2026-10-27; `notes/decisions.md`,
"E3g of the auth plan"). The checks' specs give their verdict at *some* recorded state per read (S3:
`permVerdict`), which cannot rule out a read checked against a state from before the reader's own
observation (the boot state, auth disabled). The user chose (2026-10-27) the reads' freshness as a
monotone lower bound, like the KV reads' revision floor: a reader holding a lower bound `i` of the
history's published index (`authPubLb`, every state up to `i` committed to the backend) has its
check's verdict at states no older than `i`. This file states it for the backend's read side
(`lockedReadTx`, over the read contract's third clause, `authReadTxOk`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__lockedReadTx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

namespace auth

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **A locked read transaction no older than the index `i`** (the auth plan's E3g): as
`authReadTxLocked`, its state recorded at an index at least `i` (`authSnapFrom`). -/
def authReadTxLockedFrom (tx : GoInterface) (R : IProp GF) (M : AuthMode) (i : Nat) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tx = GoInterface.ok ti⌝ ∗
    ∃ (sta : AuthState) (Hs : AuthState → IProp GF), Hs sta ∗ authSnapFrom M i sta ∗
      authTxReads ti R Hs)

end defs

end auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.lockedReadTx()` for a reader holding a lower bound `i` of the published index: the locked
read transaction is at a state no older than `i` (`authReadTxLockedFrom`). -/
abbrev auth.authStore.lockedReadTx.specLb : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : auth.AuthMode) (i : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      beRd st R M ∗ R ∗ authPubLbM M i }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"lockedReadTx")) (Val #()))
  {{ (tx : GoInterface), RET #tx; beRd st R M ∗ authReadTxLockedFrom tx R M i }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.authStore.lockedReadTx.wp_lb :
    auth.authStore.lockedReadTx.specLb (GF := GF) (hG := hG) := by
  intro st R M i
  wp_start as ⟨#Hinv, Hrd, HR, #Hlb⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold authInv at Hinv
  icases Hinv with ⟨%Hst, -, -, -, -, -, -⟩
  iunfold beRd at Hrd
  wp_auto
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
  icases Htx with ⟨%Hs, -, -, #HRF, #Hreads⟩
  wp_auto
  wp_bind (App (Val #(methods ti.ty go!"RLock" ti.v)) (Val #()))
  iapply HRF $$ %i [HR]
  · iframe HR Hlb
  inext
  iintro ⟨%sta, Htok, #Hsnap⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hlk Hbe] as Hrd
  · inext; iunfold beP; iexists _; iframe Hbe; iexact Hbeok
  iapply HΦ
  iunfold beRd
  iframe Hrd
  iunfold authReadTxLockedFrom
  iexists ti
  isplitr
  · ipureintro; rfl
  iexists sta, Hs
  iframe Htok
  iframe #

end proof
