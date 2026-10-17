/-
Proof of the spec of the same name (the mvcc store's compaction; etcd-io/etcd#21968's no-op case).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Compact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__checkPrevCompactionCompleted
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__updateCompactRev
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Step
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__compact

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `store.Compact` (etcd-io/etcd#21968: the no-op compaction of the head, and `s.mu` released
before the error check). -/
theorem mvcc.store.Compact.wp_proof
    (h0 : mvcc.store.checkPrevCompactionCompleted.spec (GF := GF) (hG := hG))
    (h1 : mvcc.store.updateCompactRev.spec (GF := GF) (hG := hG))
    (h2 : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (h3 : zap.Int64.spec (GF := GF) (hG := hG))
    (h4 : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (h5 : mvcc.store.compact.spec (GF := GF) (hG := hG)) :
    mvcc.store.Compact.spec (GF := GF) (hG := hG) := by
  intro s γ trace rev c P f Pre Q Post log te htr hcmp hc
  wp_start as ⟨#Hs, #Hstop, Hright, #HcertC, %HndC, #Hhook, Hcs, Htrc⟩
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
  icases HmuP with ⟨%c', HmuP⟩
  iunfold mvcc.muInvAt at HmuP
  iNamed HmuP
  iunfold mvcc.compactRight at Hright
  icases Hright with ⟨Hcr, Hq⟩
  ihave %Hcc := mvcc.crevUB_agree γ.idx _ _ c' c HcM hc $$ HcrevM Hcr
  subst Hcc
  ihave Hmu1 : mvcc.muInvAt s γ 1 c' $$ [HcmpM HcrevM]
  · iunfold mvcc.muInvAt; iframe HcmpM HcrevM; iframe #; ipureintro; exact HcM
  ihave Hright : mvcc.compactRight γ c' $$ [Hcr Hq]
  · iunfold mvcc.compactRight; iframe Hcr Hq
  wp_apply (h0 s γ hcmp) $$ [] as %pcc -
  · iframe #
  (try wp_auto)
  wp_apply (h1 s γ rev c' P f Pre Q Post log hcmp) $$ [$Hmu1 $Hright $Hcs] as %ch %prev %cur %err Hres
  · iframe #; ipureintro; exact HndC
  (try wp_auto)
  wp_apply (h2 trace te _ slice.nil) $$ [Htrc] as Htrc
  · iframe #; iframe Htrc; iapply traceutil.ownFields_nil
  (try wp_auto)
  icases Hres with (⟨⟨%Herr, %Hch, %Hprev, %Hlt, -⟩, Hmu, Hright, HPost, #Hjob⟩ |
    ⟨⟨%Hle, %Hprev, %Hcur⟩, ⟨%ec, #Hec, %Herr⟩, ⟨%logh, #Hcerth, %Hlogh⟩, Hmu, Hright, HPre, #Hch⟩ |
    ⟨⟨%Hlt, %Hch, %Hprev⟩, ⟨%ef, #Hef, %Herr⟩, #Hcert, Hmu, Hright, HPre⟩)
  · subst Herr
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hmu]
    · inext; iunfold mvcc.muInv; iexists (sint.Z rev); iexact Hmu
    (try wp_auto)
    iunfold mvcc.compactRight at Hright
    icases Hright with ⟨Hcr, Hq⟩
    wp_apply (h5 s γ trace rev prev pcc te htr) $$ [$Hjob $Hq $Htrc] as %ch' ⟨#Hch', Hq, Htrc⟩
    (try wp_auto)
    iapply HΦ
    iframe Htrc
    ileft
    iframe HPost Hch'
    isplitr
    · ipureintro; exact ⟨rfl, Hlt⟩
    isplitl [Hcr Hq]
    · iunfold mvcc.compactRight; iframe Hcr Hq
    iunfold mvcc.compactJobPre at Hjob
    icases Hjob with ⟨-, -, -, #Hlb, -⟩
    iexact Hlb
  · subst Herr
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hmu]
    · inext; iunfold mvcc.muInv; iexists c'; iexact Hmu
    (try wp_auto)
    wp_if_destruct
    · -- `rev == currentRev`: the head is already compacted, a no-op
      have hrc0 : sint.Z rev = sint.Z cur := by rw [Hif]
      obtain ⟨hcur, hlen⟩ := Hlogh
      have hrc : sint.Z rev = c' := by omega
      ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
      · iPkgInit
      wp_apply h3 as %f1 -
      (try wp_auto)
      wp_apply h3 as %f2 -
      (try wp_auto)
      wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1, f2]
      isplitr
      · ipureintro; rfl
      iintro %fsl ⟨-, -⟩
      (try wp_auto)
      wp_apply (h4 lg) $$ []
      · iframe #; ipureintro; exact Hlgnn
      (try wp_auto)
      iapply HΦ
      iframe Htrc
      iright; ileft
      iframe Hright HPre Hch
      ipureintro; exact ⟨rfl, hrc, by omega⟩
    · -- the head moved past `rev`: `ErrCompacted`
      have hlt : sint.Z rev < sint.Z cur := by
        have : sint.Z rev ≠ sint.Z cur := fun h => by
          apply Hif; apply BitVec.eq_of_toInt_eq; exact h
        omega
      (try wp_auto)
      iapply HΦ
      iframe Htrc
      iright; iright; ileft
      iframe Hright HPre Hch
      isplitr
      · ipureintro; exact Hle
      isplitr
      · iexists ec; iframe Hec; ipureintro; rfl
      iexists logh; iframe Hcerth; ipureintro; obtain ⟨hcur, hlen⟩ := Hlogh; omega
  · subst Herr Hch
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hmu]
    · inext; iunfold mvcc.muInv; iexists c'; iexact Hmu
    (try wp_auto)
    icases Hcert with ⟨%logf, #Hcertf, %Hlogf⟩
    obtain ⟨hlenf, hcurf⟩ := Hlogf
    wp_if_destruct
    · -- `rev == currentRev` is impossible: `currentRev < rev`
      have : sint.Z rev = sint.Z cur := by rw [Hif]
      omega
    (try wp_auto)
    iapply HΦ
    iframe Htrc
    iright; iright; iright
    iframe Hright HPre
    isplitr
    · ipureintro; exact ⟨Hlt, rfl⟩
    isplitr
    · iexists ef; iframe Hef; ipureintro; rfl
    iexists logf; iframe Hcertf; ipureintro; exact hlenf

end proof

end EtcdGrove
end Perennial
