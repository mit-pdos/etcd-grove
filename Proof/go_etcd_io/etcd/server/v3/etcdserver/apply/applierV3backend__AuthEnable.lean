/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__AuthEnable
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__newHeader

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]


theorem apply.applierV3backend.AuthEnable.wp_proof
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.AuthEnable.spec (GF := GF) (hG := hG) := by
  intro E p log Pre Q Post
  wp_start as ⟨#Hb, Hpre⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  ihave #Hb' := Hb
  iunfold apply.backendIs at Hb'
  icases Hb' with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨-, -, -, -, #Has, -⟩
  iunfold apply.isAuthStore at Has
  icases Has with ⟨%ai, %Hai, -, -, -, -, -, -, -, #HM, -⟩
  iStructNamed Hopts
  wp_auto
  rw [Hai]
  wp_apply HM $$ %Pre %Q %Post [$Hcs] as %err ⟨HPP, #HeI⟩
  iunfold apply.kvOwn at Hkv
  icases Hkv with ⟨Hrd, Hsw, Hknown⟩
  rcases err with ei | _
  · -- the store's error
    wp_auto
    iapply HΦ
    isplitl; rotate_left
    · first | iexact HeI | iapply applyErrIs_nil
    iunfold apply.mPost
    iunfold apply.kvOwn
    iframe
  · -- enabled: a fresh response with the header
    wp_auto
    wp_apply (hHdr E p log) $$ [$Hpkg $Hb $Hrd $Hsw] as %h ⟨Hrd, Hsw, -⟩
    wp_alloc l as Hl
    wp_auto
    iapply HΦ
    isplitl; rotate_left
    · first | iexact HeI | iapply applyErrIs_nil
    iunfold apply.mPost
    iunfold apply.kvOwn
    iframe

end proof

end EtcdGrove
end Perennial
