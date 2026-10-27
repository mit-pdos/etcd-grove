/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/streamWriter__close.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamWriter__close
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamWriter__closeUnlocked

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.streamWriter.close.wp_proof
    (hCloseUnlocked : rafthttp.streamWriter.closeUnlocked.spec (GF := GF) (hG := hG)) :
    rafthttp.streamWriter.close.spec (GF := GF) (hG := hG) := by
  intro Rh ty lid pid Rr cw mc wk cl Q
  wp_start as ⟨#Hf, Hrun, Hcls, HR⟩
  ihave #Hf' := Hf
  iunfold swFixed at Hf'
  icases Hf' with ⟨%lg, %ps, %fs, %r, %γd, %cc, %sc, %dc, %γc, %γs, %γdn, -, -, -, -, -, -, -, -,
    -, -, #Hmu, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.Mutex.wp_Lock _ (swLockInv Rh ty lid pid cw) $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold swLockInv at Hinv
  icases Hinv with ⟨%mc0, %γm0, %wk0, %cl0, Hmc0, Hwk0, Hcl0, #Hbag0⟩
  iunfold swRunOwn at Hrun
  icases Hrun with ⟨%γm, Hmc, Hwk, Hcl, #Hbag⟩
  ihave ⟨%Hemc, Hmc⟩ := typedPointsto_combine_halves _ _ _ $$ [$Hmc $Hmc0]
  ihave ⟨%Hewk, Hwk⟩ := typedPointsto_combine_halves _ _ _ $$ [$Hwk $Hwk0]
  ihave ⟨%Hecl, Hcl⟩ := typedPointsto_combine_halves _ _ _ $$ [$Hcl $Hcl0]
  subst Hemc Hewk Hecl
  (try wp_auto)
  wp_apply hCloseUnlocked Rh ty lid pid Rr cw mc γm wk cl Q $$ [$Hmc $Hwk $Hcl $Hcls $HR]
    as %b ⟨%Hb, HR, %mc', %γm', Hmc, Hwk, Hcl, #Hbag'⟩
  · iframe #
  (try wp_auto)
  ihave ⟨Hmc, Hmc0⟩ := (typedPointsto_halves _ _).1 $$ Hmc
  ihave ⟨Hwk, Hwk0⟩ := (typedPointsto_halves _ _).1 $$ Hwk
  ihave ⟨Hcl, Hcl0⟩ := (typedPointsto_halves _ _).1 $$ Hcl
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hmc0 Hwk0 Hcl0]
  · inext
    iunfold swLockInv
    iexists mc', γm', false, cl
    iframe; iframe #
  iapply HΦ
  iframe HR
  isplitr
  · ipureintro; exact Hb
  iexists mc'
  iunfold swRunOwn
  iexists γm'
  iframe; iframe #

end proof

end EtcdGrove
end Perennial
