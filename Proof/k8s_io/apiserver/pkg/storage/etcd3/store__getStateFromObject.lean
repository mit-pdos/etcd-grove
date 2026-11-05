/-
Lean-first (no Rocq counterpart).

The proof of `(*store).getStateFromObject` (stage 7b): the versioner's `ObjectResourceVersion`
parses the object's resource version string `fmtRV r` back to `r` (`parse_fmt`), its
`PrepareObjectForStorage` clears it, `runtime.Encode` gives the object's encoding (or the codec's
error), and `UpdateObject` sets `r` again (`versionerOk`, `encodeOk`).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__getStateFromObject

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem store.getStateFromObject.wp_proof :
    store.getStateFromObject.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ sp c x o r
  wp_start as ⟨#Hst, Hobj⟩
  iunfold isStore at Hst
  icases Hst with ⟨%Hsp, #Fcl, #Fcodec, #Fvi, #Fti, #Fdi, #Fpp, #Frp, #Fgr, #Fmt, #Flt, %Hlt, #Hkc,
    #Hcl, #Hone, #Hregs, #Hcon⟩
  iunfold contractOk at Hcon
  icases Hcon with ⟨%Hty, #Henc, #Hver, #Htr, #Hdec, #Hzero, #Hmeta⟩
  iunfold versionerOk at Hver
  icases Hver with ⟨#HORV, #HPrep, #HUpd, #HParse⟩
  iunfold encodeOk at Henc
  wp_auto
  wp_bind
  iapply HORV $$ Hobj
  inext
  iintro %n %err Hobj %hn
  rw [c.S.parse_fmt r] at hn
  obtain ⟨rfl, rfl⟩ := hn
  wp_auto
  wp_bind
  iapply HPrep $$ Hobj
  inext
  iintro %err ⟨Hobj, %he⟩
  subst he
  wp_auto
  wp_bind
  iapply Henc $$ Hobj
  inext
  iintro %dsl %err Hobj Hres
  icases Hres with (⟨%he, Hdsl⟩ | ⟨%he, #Herr⟩)
  · subst he
    wp_auto
    ipersist Hdsl
    wp_bind
    iapply HUpd $$ Hobj
    inext
    iintro %err ⟨Hobj, %he⟩
    subst he
    wp_auto
    icases (typedPointsto_not_null_dup _ _ _) $$ «$r0» with ⟨Hstp, %Hnn⟩
    have hz : (zero_val k8s_io.apiserver.pkg.storage.ResponseMeta).TTL' = W64 0 := rfl
    isimp only [hz] at Hstp «$v1»
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iunfold ownState
    iexists x, «$v1_ptr», dsl
    iframe Hstp Hobj Hdsl «$v1»
    ipureintro; exact Hnn
  · obtain ⟨hne, henc⟩ := he
    cases err with
    | nil => exact absurd rfl hne
    | ok ie =>
      wp_auto
      iapply HΦ
      iright
      iapply unkErr_enc c _ hne henc

end proof

end k8s
end EtcdGrove
end Perennial
