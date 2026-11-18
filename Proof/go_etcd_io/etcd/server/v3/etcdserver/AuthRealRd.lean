/-
**The auth realization's read contract** (auth-schema-srv A6, 2026-11-18): schema's read transaction over the
real backend meets the store's guarded read contract (`auth.authReadTxOk`, `auth.authBackendOk`) at the ticket
`ownToks γt 1`, over the per-backend invariant (`AuthRealInv.lean`): the real backend is schema's `authBE` for the
ticket pool (`real_BE`, from `authBE_real` and the pool's steps), and after schema's `RLock` the token of the held
read observes the view (`real_view`, `real_viewIdle`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthRealInv
public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authReadTx__RLock
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authReadTx__RUnlock
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authReadTx__UnsafeGetUser
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authReadTx__UnsafeGetRole
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authReadTx__UnsafeReadAuthEnabled
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authReadTx__UnsafeReadAuthRevision
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authReadTx__UnsafeGetAllUsers
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__ReadTx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authReal

open Iris Iris.BI Iris.ProofMode backend

section rd
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- The token of a held read of the ticket pool. -/
abbrev heldT (γ : RNames) (d : mvcc.KBReal) : Loc → schema.AuthData → IProp GF :=
  schema.heldR d.γB d.P d.be (fun _ => ownToks γ.γh 1)

/-- **The read transaction's token of a view** `v`: a held read whose buckets hold `v`. -/
def hsT (γ : RNames) (d : mvcc.KBReal) (rt : GoInterfaceOk) (v : auth.BkView) : IProp GF :=
  iprop(∃ (x : Loc) (D : schema.AuthData), heldT γ d x D ∗ schema.authReader rt (heldT γ d x D) D ∗
    ⌜viewAt v D⌝)

/-- **The real backend is schema's `authBE` for the ticket pool.** -/
theorem real_BE (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFE : backend.readTx.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (W Pk : IProp GF) (hP : schema.authHas d.P) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend d.γB d.P W Pk d.be ∗ realInv γ d s0 q0 ⊢
      schema.authBE (schema.beIface d.be) (ownToks γ.γt 1) (depT γ) (heldT γ d) := by
  iintro ⟨#Hp1, #Hp2, #Hb, #Hinv⟩
  iapply schema.authBE_real hRT hRL hRU hUR hFE hID hName hSafe d.γB d.P W Pk d.be (ownToks γ.γt 1)
    (depT γ) (rcpt γ s0) (fun _ => ownToks γ.γh 1) hP
  iframe Hp1 Hp2 Hb
  isplitr
  · iintro !> %o ⟨HR, HL, Hlc⟩
    iapply real_acq γ d s0 q0 o $$ [$Hinv $HR $HL $Hlc]
  isplitr
  · iintro !> %o %x %rv %qo ⟨Hh, Ho, HC, Hlc⟩
    iapply real_obs γ d s0 q0 o x rv qo $$ [$Hinv $Hh $Ho $HC $Hlc]
  · iintro !> %rv ⟨Ht, Hy, Hlc⟩
    iapply real_rel γ d s0 q0 $$ [$Hinv $Ht $Hy $Hlc]

/-- **Schema's read transaction meets the store's read contract** (`auth.authReadTxOk` in `on γa`, at the
ticket): `RLock` with a share of the currency or the write token (the lent `depT`), then the view of the held
read (`real_view`, `real_viewIdle`); the reads are schema's at each bucket's state. -/
theorem real_readTxOk (hRLs : schema.authReadTx.RLock.spec (GF := GF) (hG := hG))
    (hRUs : schema.authReadTx.RUnlock.spec (GF := GF) (hG := hG))
    (hGU : schema.authReadTx.UnsafeGetUser.spec (GF := GF) (hG := hG))
    (hGR : schema.authReadTx.UnsafeGetRole.spec (GF := GF) (hG := hG))
    (hEn : schema.authReadTx.UnsafeReadAuthEnabled.spec (GF := GF) (hG := hG))
    (hRev : schema.authReadTx.UnsafeReadAuthRevision.spec (GF := GF) (hG := hG))
    (hGA : schema.authReadTx.UnsafeGetAllUsers.spec (GF := GF) (hG := hG))
    (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (l : Loc) (rt : GoInterfaceOk) (lg : Loc) (hlg : lg ≠ null) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ realInv γ d s0 q0 ∗
      schema.atxF go!"tx" l ↦□ (GoInterface.ok rt : GoInterface) ∗ schema.atxF go!"lg" l ↦□ lg ∗
      schema.authRTx rt (ownToks γ.γt 1) (depT γ) (heldT γ d) ⊢
      auth.authReadTxOk
        (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authReadTx.ty) #l)
        (ownToks γ.γt 1) (.on γ.γa) γ.γc := by
  iintro ⟨#Hpkg, #Hinv, #Htx, #Hlg, #Hrt⟩
  simp only [auth.authReadTxOk]
  iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authReadTx.ty, #l⟩
  isplitr
  · ipureintro; rfl
  iexists hsT γ d rt
  isplitr
  · iintro !> %q !> %Φ ⟨HR, Hc⟩ HΦ
    iapply wp_fupd
    wp_apply (hRLs l rt (ownToks γ.γt 1) (heldT γ d) (depT γ) (some q)) $$ [$Htx $Hrt $HR Hc]
      as ⟨⟨%x, %D, %Hwf, HD, HL, #Hrd⟩, Hlc⟩
    · simp only [depT]; iexact Hc
    imod (monoNatLbOwn_0 (GF := GF) γ.γa.pub) with #Hlb0
    imod real_view γ d s0 q0 _ x D 0 $$ [$Hinv $HD $Hlc] with ⟨HD, %v, %Hv, #Hsn⟩
    · iunfold auth.authPubLb; iexact Hlb0
    imodintro
    iapply HΦ
    iexists v
    simp only [depT]
    iframe HL
    isplitl [HD]
    · iunfold hsT; iexists x, D; iframe HD Hrd; ipureintro; exact Hv
    simp only [auth.authViewSnap]
    iexact Hsn
  isplitr
  · iintro !> %i %q !> %Φ ⟨HR, #Hlb, Hc⟩ HΦ
    iapply wp_fupd
    wp_apply (hRLs l rt (ownToks γ.γt 1) (heldT γ d) (depT γ) (some q)) $$ [$Htx $Hrt $HR Hc]
      as ⟨⟨%x, %D, %Hwf, HD, HL, #Hrd⟩, Hlc⟩
    · simp only [depT]; iexact Hc
    imod real_view γ d s0 q0 _ x D i $$ [$Hinv $HD $Hlc] with ⟨HD, %v, %Hv, #Hsn⟩
    · simp only [auth.authPubLbM]; iexact Hlb
    imodintro
    iapply HΦ
    iexists v
    simp only [depT]
    iframe HL Hsn
    iunfold hsT; iexists x, D; iframe HD Hrd; ipureintro; exact Hv
  isplitr
  · iintro !> %hs !> %Φ ⟨HR, HT, Hhh⟩ HΦ
    iapply wp_fupd
    wp_apply (hRLs l rt (ownToks γ.γt 1) (heldT γ d) (depT γ) none) $$ [$Htx $Hrt $HR HT]
      as ⟨⟨%x, %D, %Hwf, HD, HL, #Hrd⟩, Hlc⟩
    · simp only [depT]; iexact HT
    simp only [depT]
    imod real_viewIdle γ d s0 q0 _ x D hs $$ [$Hinv $HD $HL $Hhh $Hlc] with ⟨HD, HT, Hhh, %st, %Hv, #Hsn⟩
    imodintro
    iapply HΦ
    iexists st
    iframe HT Hhh Hsn
    isplitl [HD]
    · iunfold hsT; iexists x, D; iframe HD Hrd; ipureintro; exact Hv.1
    ipureintro; exact Hv.2
  iunfold auth.authTxReadsV
  isplitr
  · iunfold auth.authReaderOkV
    isplitr
    · iintro !> %v %name !> %Φ Hs HΦ
      iunfold hsT at Hs
      icases Hs with ⟨%x, %D, HD, #Hrd, %Hv⟩
      obtain ⟨-, ⟨dU, hu⟩, -⟩ := id Hv
      iapply wp_fupd
      wp_apply (hGU l rt lg name (heldT γ d x D) D dU hlg (schema.usersAt_dec hu)) $$ [$Htx $Hlg $Hrd $HD]
        as %u ⟨HD, Hu⟩
      imod schema.userOutDX_persist u D.users name dU $$ Hu with Hu
      imodintro
      iapply HΦ
      isplitl [HD]
      · iunfold hsT; iexists x, D; iframe HD Hrd; ipureintro; exact Hv
      iapply schema.userOutD_are v.atUsers D.users u name dU hu $$ Hu
    isplitr
    · iintro !> %v %name !> %Φ Hs HΦ
      iunfold hsT at Hs
      icases Hs with ⟨%x, %D, HD, #Hrd, %Hv⟩
      obtain ⟨-, -, ⟨dR, hr⟩⟩ := id Hv
      iapply wp_fupd
      wp_apply (hGR l rt lg name (heldT γ d x D) D dR hlg (schema.rolesAt_dec hr)) $$ [$Htx $Hlg $Hrd $HD]
        as %u ⟨HD, Hu⟩
      imod schema.roleOutDX_persist ⊤ u D.roles name dR $$ Hu with Hu
      imodintro
      iapply HΦ
      isplitl [HD]
      · iunfold hsT; iexists x, D; iframe HD Hrd; ipureintro; exact Hv
      iapply schema.roleOutD_are v.atRoles D.roles u name dR hr $$ Hu
    isplitr
    · iintro !> %v !> %Φ Hs HΦ
      iunfold hsT at Hs
      icases Hs with ⟨%x, %D, HD, #Hrd, %Hv⟩
      wp_apply (hEn l rt (heldT γ d x D) D) $$ [$Htx $Hrd $HD] as %b ⟨HD, %Hb⟩
      iapply HΦ
      isplitl [HD]
      · iunfold hsT; iexists x, D; iframe HD Hrd; ipureintro; exact Hv
      ipureintro
      rw [Hb, enabledOf_auth]; exact Hv.1.1
    isplitr
    · iintro !> %v !> %Φ Hs HΦ
      iunfold hsT at Hs
      icases Hs with ⟨%x, %D, HD, #Hrd, %Hv⟩
      wp_apply (hRev l rt (heldT γ d x D) D Hv.1.2.2) $$ [$Htx $Hrd $HD] as %r ⟨HD, %Hr⟩
      iapply HΦ
      isplitl [HD]
      · iunfold hsT; iexists x, D; iframe HD Hrd; ipureintro; exact Hv
      ipureintro
      rw [Hr, revisionOf_auth]; exact Hv.1.2.1
    · iintro !> %v !> %Φ Hs HΦ
      iunfold hsT at Hs
      icases Hs with ⟨%x, %D, HD, #Hrd, %Hv⟩
      obtain ⟨-, ⟨dU, hu⟩, -⟩ := id Hv
      wp_apply (hGA l rt lg (heldT γ d x D) D dU (schema.usersAt_dec hu)) $$ [$Htx $Hlg $Hrd $HD]
        as %s ⟨HD, Hs⟩
      ihave Hs := usersOutD_at v.atUsers D.users dU s hu $$ Hs
      iunfold auth.usersOut at Hs
      icases Hs with ⟨%us, %names, Hs, %Hn, Hl⟩
      iapply HΦ
      iframe Hs Hl
      isplitl [HD]
      · iunfold hsT; iexists x, D; iframe HD Hrd; ipureintro; exact Hv
      ipureintro; exact Hn
  · iintro !> %v !> %Φ Hs HΦ
    iunfold hsT at Hs
    icases Hs with ⟨%x, %D, HD, -, -⟩
    wp_apply (hRUs l rt (ownToks γ.γt 1) (heldT γ d) (depT γ) x D) $$ [$Htx $Hrt $HD] as HR
    iapply HΦ
    iexact HR

/-- **Schema's auth backend meets the store's guarded read contract** (`auth.authBackendOk` in `on γa`, at
the ticket). -/
theorem real_backendOk (hRTs : schema.authBackend.ReadTx.spec (GF := GF) (hG := hG))
    (hRLs : schema.authReadTx.RLock.spec (GF := GF) (hG := hG))
    (hRUs : schema.authReadTx.RUnlock.spec (GF := GF) (hG := hG))
    (hGU : schema.authReadTx.UnsafeGetUser.spec (GF := GF) (hG := hG))
    (hGR : schema.authReadTx.UnsafeGetRole.spec (GF := GF) (hG := hG))
    (hEn : schema.authReadTx.UnsafeReadAuthEnabled.spec (GF := GF) (hG := hG))
    (hRev : schema.authReadTx.UnsafeReadAuthRevision.spec (GF := GF) (hG := hG))
    (hGA : schema.authReadTx.UnsafeGetAllUsers.spec (GF := GF) (hG := hG))
    (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (abl lg : Loc) (hlg : lg ≠ null) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ realInv γ d s0 q0 ∗
      ablOn abl d.be lg ∗ schema.authBE (schema.beIface d.be) (ownToks γ.γt 1) (depT γ) (heldT γ d) ⊢
      auth.authBackendOk (authBkIface abl) (ownToks γ.γt 1) (.on γ.γa) γ.γc := by
  iintro ⟨#Hpkg, #Hinv, #Habl, #Hbe⟩
  iunfold ablOn at Habl
  icases Habl with ⟨#Hb, #Hl⟩
  iunfold auth.authBackendOk
  iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty, #abl⟩
  isplitr
  · ipureintro; rfl
  iintro !> %Φ !> - HΦ
  wp_apply (hRTs abl (schema.beIface d.be) lg (ownToks γ.γt 1) (heldT γ d) (depT γ)) $$ [$Hb $Hl $Hbe]
    as %tx ⟨%l, %rt, %Htx, #Htxf, #Hlgf, #Hrtx⟩
  iapply HΦ
  rw [Htx]
  iapply real_readTxOk hRLs hRUs hGU hGR hEn hRev hGA γ d s0 q0 l rt lg hlg $$ [$Hpkg $Hinv $Htxf $Hlgf $Hrtx]

end rd

end authReal
end EtcdGrove
end Perennial
