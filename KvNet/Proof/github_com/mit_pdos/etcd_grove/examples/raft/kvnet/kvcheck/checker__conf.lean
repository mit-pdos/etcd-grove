/-
Proof of `KvNet/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/kvcheck/checker__conf.lean`: the
status request (`reqOk` of a status is `True`), `GetStatus` on the answer, the decoded conf state made
read-only (`csPts_persist`, `csPts_weaken`) and stored in `lastConf` under `mu`.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker__conf
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker__request
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.checker__randomID
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.GetStatus

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Iris.ProofMode Net raft_kvnet go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.kvcheck.Assumptions]

theorem checker.conf.wp_proof (wp_randomID : checker.randomID.spec (GF := GF) (hG := hG))
    (wp_request : checker.request.spec (GF := GF) (hG := hG))
    (wp_GetStatus : GetStatus.spec (GF := GF) (hG := hG)) :
    checker.conf.spec (GF := GF) (hG := hG) := by
  intro F c γ ls
  wp_start as #Hc
  ihave #Hc0 := Hc
  iunfold isCheckerP at Hc0
  icases Hc0 with ⟨#Hck, %Hls, -, -⟩
  ihave #Hck0 := Hck
  iunfold isChecker at Hck0
  icases Hck0 with ⟨%sl, #Ha, #Hsl, #Hmu⟩
  ihave #Hkv : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_randomID c γ ls Hls.1 $$ [$Hpkg $Hck] as %id %Hid
  ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  wp_apply wp_request F c γ ls id (W8 5) slice.nil [] (DFrac.own 1) Hid.1 Hid.2
      (by simp) $$ [$Hpkg $Hc $Hnil] as %r %ok ⟨-, Hans⟩
  · unfold reqOk; simp [reqProposeB, reqReadB, reqConfB, reqDisruptB]; itrivial
  icases Hans with (%Hok | ⟨%x, %Hok, Hr, -⟩)
  · subst Hok
    try wp_auto
    iapply HΦ
    iexists ConfStateM.mk [] [] [] [] false
    unfold csOpt
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  subst Hok
  try wp_auto
  wp_apply wp_GetStatus r (DFrac.own 1) x $$ [$Hkv $Hr] as %st %good Hst
  try wp_auto
  cases good with
  | false =>
    try wp_auto
    iapply HΦ
    iexists ConfStateM.mk [] [] [] [] false
    unfold csOpt
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  | true =>
  simp only [↓reduceIte]
  icases Hst with ⟨%cs, Hcs⟩
  imod csPts_persist _ _ _ _ $$ Hcs with #Hcs
  ihave #Hcs' := csPts_weaken _ _ _ _ $$ Hcs
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold checkerInv at HL
  icases HL with ⟨%a, %b, %lc, %cs0, Hop, Hrd, Hlc, -, HMa, HMb⟩
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hop Hrd Hlc HMa HMb]
  · inext
    iunfold checkerInv
    iexists a, b, st.Conf', cs
    iframe
    unfold csOpt; iright; iexact Hcs'
  try wp_auto
  iapply HΦ
  iexists cs
  unfold csOpt; iright; iexact Hcs'

end proof

end raft_kvcheck
end EtcdGrove
end Perennial
