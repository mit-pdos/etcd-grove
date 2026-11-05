/-
Proof of the spec of the same name (the mvcc store's compaction, units 5b/5c).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Compact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__checkPrevCompactionCompleted
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__updateCompactRev
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Step
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__compact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.CmpCb
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.store.Compact.wp_proof
    (h0 : mvcc.store.checkPrevCompactionCompleted.spec (GF := GF) (hG := hG))
    (h1 : mvcc.store.updateCompactRev.spec (GF := GF) (hG := hG))
    (h2 : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (h3 : mvcc.store.compact.spec (GF := GF) (hG := hG)) :
    mvcc.store.Compact.spec (GF := GF) (hG := hG) := by
  -- the core (`mvcc.store.Compact.core`), then the contract over it (`store.Compact.wp_api`)
  have hcore : mvcc.store.Compact.core (GF := GF) (hG := hG) := by
    intro s γ trace rev c P hk dq Pre Q Post S Fok Fce Ffr XB YB te htr hcmp hc hpos1 hS1 hS2
    wp_start as ⟨#Hs, Hright, #HpermR, Hctx, Htrc, HRTok, #HsupM, HS, Hcb, HXB, #HreqB⟩
    ihave #Hs' := Hs
    iunfold mvcc.isStore at Hs'
    iNamed Hs'
    ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
    · iPkgInit
    ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
    · iPkgInit
    (try wp_auto)
    wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hwl, HmuP⟩
    wp_auto_lc 1
    imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.muInv s γ 1)) $$ Hlc1 HmuP with HmuP
    iunfold mvcc.muInv at HmuP
    icases HmuP with ⟨%c', HmuP, Hwr⟩
    iunfold mvcc.muInvAt at HmuP
    iNamed HmuP
    icases mvcc.compactRightR_crev s γ c $$ Hright with ⟨Hcr, Hrclose⟩
    ihave %Hcc := mvcc.crevUB_agree γ.idx _ _ c' c HcM hc $$ HcrevM Hcr
    subst Hcc
    ihave Hmu1 : mvcc.muInvLag s γ c' c' $$ [HcmpM HcrevM HwcM]
    · iunfold mvcc.muInvLag; iframe HcmpM HcrevM HwcM; iframe #; ipureintro; exact ⟨HcM, Int.le_refl c'⟩
    ihave Hright := Hrclose $$ Hcr
    -- `s.b`, read through the right's closer's eighth (M2, the storage side, item 17)
    icases mvcc.compactRightR_take s γ c' $$ Hright with ⟨%o, Hfs, Hq, Hrclose⟩
    wp_apply (h0 s γ mvcc.q8 o hcmp) $$ [$HRTok $Hfs] as %pcc ⟨Hfs, HRTok⟩
    · iframe #
    ihave Hright := Hrclose $$ Hfs Hq
    (try wp_auto)
    wp_apply (h1 s γ rev c' c' P hk dq Pre Q Post S Fok Fce Ffr XB YB hcmp
        (fun h => absurd h (Int.lt_irrefl c')) hpos1 hS1 hS2)
      $$ [$Hmu1 $Hright $HRTok $Hctx $HS $Hcb $HXB] as %ch %prev %err ⟨HRTok, Hback, HS, Hres⟩
    · iframe #
    (try wp_auto)
    wp_apply (h2 trace te _ slice.nil) $$ [Htrc] as Htrc
    · iframe #; iframe Htrc; iapply traceutil.ownFields_nil
    (try wp_auto)
    icases Hres with (⟨⟨%Herr, %Hch, %Hprev, %Hlt, %Hle0⟩, Hmu, Hright, HPost, #Hjob, -, HFok, HYB⟩ |
      ⟨⟨%Hle, %Hprev⟩, ⟨%ec, #Hec, %Herr⟩, Hmu, Hright, HPre, #Hch, HFce, HXB⟩ |
      ⟨⟨%Hch, %Hprev⟩, ⟨%ef, #Hef, %Herr⟩, Hmu, Hright, HPre, HFfr, HXB⟩)
    · subst Herr
      (try wp_auto)
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hmu Hwr]
      · inext; iunfold mvcc.muInv; iexists (sint.Z rev); iframe Hwr; iexact Hmu
      (try wp_auto)
      icases mvcc.compactRightR_take s γ (sint.Z rev) $$ Hright with ⟨%o', Hfs, Hq, Hrclose⟩
      wp_apply (h3 s γ trace rev prev pcc te mvcc.q8 o' htr) $$ [$Hjob $Hq $Htrc $Hfs]
        as %ch' ⟨#Hch', Hq, Htrc, Hfs⟩
      ihave Hright := Hrclose $$ Hfs Hq
      (try wp_auto)
      iapply HΦ
      iframe Htrc HRTok Hback HS
      ileft
      iframe HPost Hch' HFok HYB
      isplitr
      · ipureintro; exact ⟨rfl, Hlt⟩
      iframe Hright
      iunfold mvcc.compactJobPre at Hjob
      icases Hjob with ⟨-, -, -, #Hlb, -, -⟩
      iexact Hlb
    · subst Herr
      (try wp_auto)
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hmu Hwr]
      · inext; iunfold mvcc.muInv; iexists c'; iframe Hwr; iexact Hmu
      (try wp_auto)
      iapply HΦ
      iframe Htrc HRTok Hback HS
      iright
      ileft
      iframe Hright HPre Hch HFce HXB
      isplitr
      · ipureintro; exact Hle
      iexists ec; iframe Hec; ipureintro; rfl
    · subst Herr
      (try wp_auto)
      ihave Hmu : mvcc.muInvAt (GF := GF) s γ 1 c' $$ [Hmu]
      · iapply (mvcc.muInvLag_at s γ c').1; iexact Hmu
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hmu Hwr]
      · inext; iunfold mvcc.muInv; iexists c'; iframe Hwr; iexact Hmu
      (try wp_auto)
      iapply HΦ
      iframe Htrc HRTok Hback HS
      iright
      iright
      iframe Hright HPre HFfr HXB
      isplitr
      · ipureintro; exact Hch
      iexists ef; iframe Hef; ipureintro; rfl

  exact mvcc.store.Compact.wp_api hcore

end proof

end EtcdGrove
end Perennial
