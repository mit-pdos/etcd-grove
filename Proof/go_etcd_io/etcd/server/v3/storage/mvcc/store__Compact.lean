/-
Proof of the spec of the same name: pending (the mvcc store's compaction, units 5b/5c; `sorry`).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Compact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__checkPrevCompactionCompleted
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__updateCompactRev
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Step
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__compact

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

/-- `store.Compact` for a compaction right at a revision `c ≥ -1` (the store's compaction
revisions are: `-1` at `NewStore`, then each `Compact`'s `rev > c`). -/
theorem mvcc.store.Compact.wp_of_le
    (h0 : mvcc.store.checkPrevCompactionCompleted.spec (GF := GF) (hG := hG))
    (h1 : mvcc.store.updateCompactRev.spec (GF := GF) (hG := hG))
    (h2 : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (h3 : mvcc.store.compact.spec (GF := GF) (hG := hG))
    (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (rev : w64) (c : Int) (P : IProp GF) (f : val)
    (Pre Q Post : IProp GF) (log : mvcc.Log) (te : Bool) (htr : trace ≠ null)
    (hcmp : mvcc.storeCmp γ) (hc : -1 ≤ c) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeStop s γ ∗ mvcc.compactRight γ c ∗
      mvcc.idxCert γ.idx log ∗ ⌜sint.Z rev < log.length ∧ mvcc.NoDelPutAt log (sint.Z rev)⌝ ∗
      mvcc.hookIs γ P f ∗
      mvcc.csContract P f Pre Q Post ∗ traceutil.ownTrace trace te ∗ mvcc.storeRT γ }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Compact")) (Val #trace)) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err); traceutil.ownTrace trace te ∗ mvcc.storeRT γ ∗
      ((⌜err = GoInterface.nil ∧ c < sint.Z rev⌝ ∗ mvcc.compactRight γ (sint.Z rev) ∗
        mvcc.crevLb γ.idx (sint.Z rev) ∗ Post ∗ mvcc.compactChan ch (mvcc.compactDone s γ (sint.Z rev))) ∨
      (⌜sint.Z rev ≤ c⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        mvcc.compactRight γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True)) ∨
      (⌜c < sint.Z rev ∧ ch = chan.nil⌝ ∗
        (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∗
        (∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗ ⌜(log.length : Int) ≤ sint.Z rev⌝) ∗
        mvcc.compactRight γ c ∗ Pre)) }} := by
  wp_start as ⟨#Hs, #Hstop, Hright, #HcertC, %HndC, HhookW, Hcs, Htrc, HRTok⟩
  ihave #Hs' := Hs
  iunfold mvcc.isStore at Hs'
  iNamed Hs'
  -- the compaction's objects, the current ones for good (D22 receiver epochs, S5b: until then
  -- `isStore`'s, pinned)
  icases mvcc.storeStop_open s γ $$ Hstop with
    ⟨%b, %ti, %ssched, %sstop, #Hb, #Hidx, #Hsched, #Hstopc, #Hstopch, #Hrstd, #Hph, #Hcurd⟩
  iunfold mvcc.physOk at Hph
  iNamed Hph
  try simp only
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
  iunfold mvcc.compactRight at Hright
  icases Hright with ⟨Hcr, Hq, #Hlive⟩
  ihave %Hcc := mvcc.crevUB_agree γ.idx _ _ c' c HcM hc $$ HcrevM Hcr
  subst Hcc
  ihave Hmu1 : mvcc.muInvAt s γ 1 c' $$ [HcmpM HcrevM]
  · iunfold mvcc.muInvAt; iframe HcmpM HcrevM; iframe #; ipureintro; exact HcM
  ihave Hright : mvcc.compactRight γ c' $$ [Hcr Hq]
  · iunfold mvcc.compactRight; iframe Hcr Hq Hlive
  wp_apply (h0 s γ hcmp) $$ [$HRTok] as %pcc HRTok
  · iframe #
  (try wp_auto)
  wp_apply (h1 s γ rev c' P f Pre Q Post log hcmp) $$ [$Hmu1 $Hright $Hcs $HhookW $HRTok] as %ch %prev %err ⟨HRTok, Hres⟩
  · iframe #; ipureintro; exact HndC
  (try wp_auto)
  wp_apply (h2 trace te _ slice.nil) $$ [Htrc] as Htrc
  · iframe #; iframe Htrc; iapply traceutil.ownFields_nil
  (try wp_auto)
  icases Hres with (⟨⟨%Herr, %Hch, %Hprev, %Hlt⟩, Hmu, Hright, HPost, #Hjob⟩ |
    ⟨⟨%Hle, %Hprev⟩, ⟨%ec, #Hec, %Herr⟩, Hmu, Hright, HPre, #Hch⟩ |
    ⟨⟨%Hlt, %Hch, %Hprev⟩, ⟨%ef, #Hef, %Herr⟩, #Hcert, Hmu, Hright, HPre⟩)
  · subst Herr
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hmu Hwr]
    · inext; iunfold mvcc.muInv; iexists (sint.Z rev); iframe Hwr; iexact Hmu
    (try wp_auto)
    iunfold mvcc.compactRight at Hright
    icases Hright with ⟨Hcr, Hq, #Hlive⟩
    wp_apply (h3 s γ trace rev prev pcc te htr) $$ [$Hjob $Hq $Htrc] as %ch' ⟨#Hch', Hq, Htrc⟩
    (try wp_auto)
    iapply HΦ
    iframe Htrc HRTok
    ileft
    iframe HPost Hch'
    isplitr
    · ipureintro; exact ⟨rfl, Hlt⟩
    isplitl [Hcr Hq]
    · iunfold mvcc.compactRight; iframe Hcr Hq Hlive
    iunfold mvcc.compactJobPre at Hjob
    icases Hjob with ⟨-, -, -, -, #Hlb, -⟩
    iexact Hlb
  · subst Herr
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hmu Hwr]
    · inext; iunfold mvcc.muInv; iexists c'; iframe Hwr; iexact Hmu
    (try wp_auto)
    iapply HΦ
    iframe Htrc HRTok
    iright; ileft
    iframe Hright HPre Hch
    isplitr
    · ipureintro; exact Hle
    iexists ec; iframe Hec; ipureintro; rfl
  · subst Herr Hch
    (try wp_auto)
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hmu Hwr]
    · inext; iunfold mvcc.muInv; iexists c'; iframe Hwr; iexact Hmu
    (try wp_auto)
    iapply HΦ
    iframe Htrc HRTok
    iright; iright
    iframe Hright HPre Hcert
    isplitr
    · ipureintro; exact ⟨Hlt, rfl⟩
    iexists ef; iframe Hef; ipureintro; rfl

theorem mvcc.store.Compact.wp_proof
    (h0 : mvcc.store.checkPrevCompactionCompleted.spec (GF := GF) (hG := hG))
    (h1 : mvcc.store.updateCompactRev.spec (GF := GF) (hG := hG))
    (h2 : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (h3 : mvcc.store.compact.spec (GF := GF) (hG := hG)) :
    mvcc.store.Compact.spec (GF := GF) (hG := hG) := by
  intro s γ trace rev c P f Pre Q Post log te htr hcmp hc
  exact mvcc.store.Compact.wp_of_le h0 h1 h2 h3 s γ trace rev c P f Pre Q Post log te htr hcmp hc

end proof

end EtcdGrove
end Perennial
