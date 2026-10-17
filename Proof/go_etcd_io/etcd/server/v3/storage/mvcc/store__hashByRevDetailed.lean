/-
Proof of `Spec/.../mvcc/store__hashByRevDetailed.lean` (etcd-io/etcd#21202,
pr-verify/etcd-21202). Lean-first. The hypotheses are the callees' specs, in the order of
`etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__hashByRevDetailed
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__prepareHashParams
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.unsafeHashByRevDetailed
public import Spec.time.Since
public import Spec.time.Duration__Seconds
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBatch

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

set_option maxHeartbeats 1000000 in
theorem mvcc.store.hashByRevDetailed.wp_proof
    (hPrep : mvcc.store.prepareHashParams.spec (GF := GF) (hG := hG))
    (hUH : mvcc.unsafeHashByRevDetailed.spec (GF := GF) (hG := hG))
    (hSince : time.Since.spec (GF := GF) (hG := hG))
    (hSec : time.Duration.Seconds.spec (GF := GF) (hG := hG)) :
    mvcc.store.hashByRevDetailed.spec (GF := GF) (hG := hG) := by
  intro s γ rev compactRev Hcmp Hrev0
  wp_start as ⟨#Hhist, #Hs, Hrd, Hcok⟩
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  iunfold mvcc.hashRevSecOk at Hhist
  icases Hhist with ⟨%hh, #HhG, #HhS⟩
  iunfold histSpec at HhS
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply time.wp_Now as %t0 -
  (try wp_auto)
  wp_apply (hPrep s γ rev compactRev Hcmp Hrev0) $$ [$Hs $Hrd $Hcok]
    as %prev %pc %keep %cur %tx %cl %err ⟨Hrd, Hcok, %log, %cm, #Hcert, #Hlb, %Hlg, Hcase⟩
  (try wp_auto)
  icases Hcase with (⟨%Hok, ⟨%A, Hkeep, %HA⟩, ⟨%rt, %Htx, #Hrt⟩, #Hcl⟩ |
    ⟨%Hce, %ec, #Hec, %Herr⟩ | ⟨%Hfe, %ef', #Hef, %Herr⟩)
  · obtain ⟨Herr, Hcur, Hpc, Hprev, Hb1, Hb2, Hb3, Hb4⟩ := Hok
    subst Herr Htx
    (try wp_auto)
    wp_apply (hUH rt pc prev keep _ A) $$ [$Hkeep] as %h %herr ⟨Hkeep, %Hh⟩
    · iframe #
    (try wp_auto)
    wp_apply hSince as %d -
    (try wp_auto)
    wp_apply (hSec d) $$ [$Htime] as %f -
    (try wp_auto)
    wp_apply HhS
    (try wp_auto)
    -- the deferred `cleanup()`
    iunfold mvcc.hashCleanup at Hcl
    wp_apply Hcl
    (try wp_auto)
    iapply HΦ
    iframe Hrd Hcok
    iexists log, cm
    iframe #
    isplitr
    · ipureintro; exact Hlg
    ileft
    ipureintro
    subst Hpc Hprev
    exact ⟨Hcur, Hb1, Hb2, Hb3, Hb4, fun he => by
      obtain ⟨Hh1, Hh2, Hh3, Hh4⟩ := Hh he
      exact ⟨Hh1, Hh2, Hh3, Hh4⟩⟩
  all_goals
    subst Herr
    (try wp_auto)
    iapply HΦ
    iframe Hrd Hcok
    iexists log, cm
    iframe #
    isplitr
    · ipureintro; exact Hlg
    iright
    first
      | (ileft; isplitr; · (ipureintro; assumption)
         iframe #; try (ipureintro; rfl))
      | (iright; isplitr; · (ipureintro; assumption)
         iframe #; try (ipureintro; rfl))

end proof

end EtcdGrove
end Perennial
