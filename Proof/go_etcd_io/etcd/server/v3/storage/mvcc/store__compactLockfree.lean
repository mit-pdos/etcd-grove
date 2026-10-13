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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
  intro s γ rev c P f Pre Q Post log hcmp
  wp_start as ⟨#Hs, #Hstop, Hmu, Hright, #HcertC, %HndC, #Hhook, Hcs⟩
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (h0 s γ hcmp) $$ [] as %pcc -
  · iframe #
  (try wp_auto)
  wp_apply (h1 s γ rev c P f Pre Q Post log hcmp) $$ [$Hmu $Hright $Hcs] as %ch %prev %err Hres
  · iframe #; ipureintro; exact HndC
  (try wp_auto)
  icases Hres with (⟨⟨%Herr, %Hch, %Hprev, %Hlt⟩, Hmu, Hright, HPost, #Hjob⟩ |
    ⟨⟨%Hle, %Hprev⟩, ⟨%ec, #Hec, %Herr⟩, Hmu, Hright, HPre, #Hch⟩ |
    ⟨⟨%Hlt, %Hch, %Hprev⟩, ⟨%ef, #Hef, %Herr⟩, #Hcert, Hmu, Hright, HPre⟩)
  · subst Herr
    (try wp_auto)
    wp_apply h2 as %t %Ht
    (try wp_auto)
    iunfold mvcc.compactRight at Hright
    icases Hright with ⟨Hcrev, Hq⟩
    wp_apply (h3 s γ t rev prev pcc Ht) $$ [$Hjob $Hq] as %ch' ⟨#Hch', Hq⟩
    (try wp_auto)
    iapply HΦ
    ileft
    iframe Hmu HPost Hch'
    isplitr
    · ipureintro; exact ⟨rfl, Hlt⟩
    isplitl [Hcrev Hq]
    · iunfold mvcc.compactRight; iframe Hcrev Hq
    iunfold mvcc.compactJobPre at Hjob
    icases Hjob with ⟨-, -, -, #Hlb, -⟩
    iexact Hlb
  · subst Herr
    (try wp_auto)
    iapply HΦ
    iright; ileft
    iframe Hmu Hright HPre Hch
    isplitr
    · ipureintro; exact Hle
    iexists ec; iframe Hec; ipureintro; rfl
  · subst Herr Hch
    (try wp_auto)
    iapply HΦ
    iright; iright
    iframe Hmu Hright HPre
    isplitr
    · ipureintro; exact ⟨Hlt, rfl⟩
    iexists ef; iframe Hef; ipureintro; rfl

end proof

end EtcdGrove
end Perennial
