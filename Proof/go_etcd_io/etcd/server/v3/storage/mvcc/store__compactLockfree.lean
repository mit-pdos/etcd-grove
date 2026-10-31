/-
Proof of the spec of the same name: pending (the mvcc store's compaction, units 5b/5c; `sorry`).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__compactLockfree
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__checkPrevCompactionCompleted
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__updateCompactRev
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
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

theorem mvcc.store.compactLockfree.wp_proof
    (h0 : mvcc.store.checkPrevCompactionCompleted.spec (GF := GF) (hG := hG))
    (h1 : mvcc.store.updateCompactRev.spec (GF := GF) (hG := hG))
    (h2 : traceutil.TODO.spec (GF := GF) (hG := hG))
    (h3 : mvcc.store.compact.spec (GF := GF) (hG := hG)) :
    mvcc.store.compactLockfree.spec (GF := GF) (hG := hG) := by
  intro s γ rev c P hk Pre Q Post log hcmp
  wp_start as ⟨#Hs, Hmu, Hright, #HcertC, %HrevC, Hctx, HRTok, #HsupM⟩
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  (try wp_auto)
  -- `s.b`, read through the right's closer's eighth (M2, the storage side, item 17)
  icases mvcc.compactRightR_take s γ c $$ Hright with ⟨%o, Hfs, Hq, Hrclose⟩
  wp_apply (h0 s γ mvcc.q8 o hcmp) $$ [$HRTok $Hfs] as %pcc ⟨Hfs, HRTok⟩
  · iframe #
  ihave Hright := Hrclose $$ Hfs Hq
  (try wp_auto)
  wp_apply (h1 s γ rev c P hk Pre Q Post log hcmp) $$ [$Hmu $Hright $Hctx $HRTok] as %ch %prev %err ⟨HRTok, Hhook, Hres⟩
  · iframe #; ipureintro; exact HrevC
  (try wp_auto)
  icases Hres with (⟨⟨%Herr, %Hch, %Hprev, %Hlt⟩, Hmu, Hright, HPost, #Hjob⟩ |
    ⟨⟨%Hle, %Hprev⟩, ⟨%ec, #Hec, %Herr⟩, Hmu, Hright, HPre, #Hch⟩)
  · subst Herr
    (try wp_auto)
    wp_apply h2 as %t ⟨%Ht, Htrc⟩
    (try wp_auto)
    icases mvcc.compactRightR_take s γ (sint.Z rev) $$ Hright with ⟨%o', Hfs, Hq, Hrclose⟩
    wp_apply (h3 s γ t rev prev pcc true mvcc.q8 o' Ht) $$ [$Hjob $Hq $Htrc $Hfs]
      as %ch' ⟨#Hch', Hq, -, Hfs⟩
    ihave Hright := Hrclose $$ Hfs Hq
    (try wp_auto)
    iapply HΦ
    iframe HRTok Hhook
    ileft
    iframe Hmu HPost Hch'
    isplitr
    · ipureintro; exact ⟨rfl, Hlt⟩
    iframe Hright
    iunfold mvcc.compactJobPre at Hjob
    icases Hjob with ⟨-, -, -, #Hlb, -, -⟩
    iexact Hlb
  · subst Herr
    (try wp_auto)
    iapply HΦ
    iframe HRTok Hhook
    iright
    iframe Hmu Hright HPre Hch
    isplitr
    · ipureintro; exact Hle
    iexists ec; iframe Hec; ipureintro; rfl

end proof

end EtcdGrove
end Perennial
