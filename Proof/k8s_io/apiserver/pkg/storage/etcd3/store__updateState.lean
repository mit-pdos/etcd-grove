/-
Lean-first (no Rocq counterpart).

The proof of `(*store).updateState`: the callback, then the versioner's `PrepareObjectForStorage`.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__updateState

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 16384

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem store.updateState.wp_proof : store.updateState.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ E _ sp c st s f uf
  wp_start as ⟨#Hst, Hos, #Hup⟩
  ihave Hst' := Hst
  iunfold isStore at Hst'
  icases Hst' with ⟨%Hsp, #Fcl, #Fcodec, #Fvi, #Fti, #Fdi, #Fpp, #Frp, #Fgr, #Fmt, #Flt, %Hlt,
    #Hkc, #Hcl, #Hone, #Hregs, #Hcon⟩
  iunfold contractOk at Hcon
  icases Hcon with ⟨-, #Henc, #Hver, #Htr, #Hdec, #Hzero⟩
  iunfold versionerOk at Hver
  icases Hver with ⟨-, #HvPrep, -, -⟩
  iunfold ownState at Hos
  icases Hos with ⟨%x, %m, %dsl, %Hstn, Hstp, Hobj, #Hdsl, Hm⟩
  (try wp_auto)
  iunfold tryUpdateOk at Hup
  wp_apply Hup $$ [$Hobj] as %ret %ttlp %err Hres
  (try wp_auto)
  ihave Hx : ownStateX c st s x $$ [Hstp Hm]
  · iunfold ownStateX
    iexists m, dsl
    iframe Hstp Hdsl Hm
    ipureintro; exact Hstn
  cases hf : f s.o (uint.nat s.rev) with
  | error e =>
    isimp only [hf] at Hres
    icases Hres with %Herr
    cases err with
    | nil => exact absurd rfl Herr.1
    | ok ei =>
      (try wp_auto)
      iapply HΦ
      isplitl [Hx]
      · iexists x; iexact Hx
      ipureintro; exact Herr
  | ok o' =>
    isimp only [hf] at Hres
    icases Hres with ⟨%Herr, %rv', Hret⟩
    obtain ⟨rfl, rfl⟩ := Herr
    (try wp_auto)
    wp_apply HvPrep $$ [$Hret] as %perr ⟨Hret, %Hperr⟩
    subst Hperr
    (try wp_auto)
    iapply HΦ
    isplitl [Hx]
    · iexists x; iexact Hx
    simp only
    iframe Hret
    ipureintro; exact ⟨trivial, rfl⟩

end proof

end k8s
end EtcdGrove
end Perennial
