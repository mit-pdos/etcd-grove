/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/BackendHooks__SetConfState.lean`. Lean-first
(no Rocq counterpart); D43 M5b′ (2026-10-26): under `confStateLock`, `proto.Clone`'s fresh copy
(a nil one for nil) stored, the dirty flag set.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.BackendHooks__SetConfState

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage backend storage go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- (S1b) A conf state's points-to, read-only for good (`csPts_persist`'s, at the storage package's
assumptions). -/
private theorem csPts_persist_st (p : Loc) (dq : DFrac) (c : ConfStateM) (al : Bool) :
    csPts (GF := GF) p dq c al ⊢ |==> csPts p DFrac.discard c al := by
  iintro H
  iNamed H
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HV with #HV
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hv with #Hv
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HL with #HL
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hl with #Hl
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HO with #HO
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Ho with #Ho
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HN with #HN
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hn with #Hn
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HA with #HA
  imodintro
  iunfold csPts
  iexists sv, sl, so, sn, pa
  isplitr
  · ipureintro; exact Hnn
  iframe HV Hv HL Hl HO Ho HN Hn HA cA Hpb
  ipureintro; exact Hal

theorem storage.BackendHooks.SetConfState.wp_proof
    (hClone : proto.CloneConfState.spec (GF := GF) (hG := hG)) :
    storage.BackendHooks.SetConfState.spec (GF := GF) (hG := hG) := by
  intro bh ix lg cs
  wp_start as ⟨#Hbh, Hcs⟩
  iunfold storage.isBackendHooks at Hbh
  icases Hbh with ⟨#Hix, #Hlg, #Hmu⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold storage.csInv at Hinv
  icases Hinv with ⟨%cs0, %d, Hcsf, Hd, -⟩
  (try wp_auto)
  iunfold storage.csOkN at Hcs
  icases Hcs with (%Hnil | ⟨%c, #Hc, %Hcn⟩)
  · subst Hnil
    wp_apply hClone.2
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcsf Hd]
    · inext
      iunfold storage.csInv
      iexists _, _
      iframe
      iunfold storage.csOkN; ileft; ipureintro; rfl
    (try wp_auto)
    iapply HΦ
    itrivial
  · wp_apply hClone.1 cs DFrac.discard c $$ [] as %p' ⟨-, Hp'⟩
    · iframe #
    imod csPts_persist_st _ _ _ _ $$ Hp' with #Hp'
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcsf Hd]
    · inext
      iunfold storage.csInv
      iexists _, _
      iframe
      iunfold storage.csOkN; iright; iexists c; iframe Hp'; ipureintro; exact Hcn
    (try wp_auto)
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
