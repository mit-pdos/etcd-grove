/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.checkPut
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.checkLease
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.checkAndGetPrevKV

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.checkPut.wp_proof
    (hLease : txn.checkLease.spec (GF := GF) (hG := hG))
    (hCheck : txn.checkAndGetPrevKV.spec (GF := GF) (hG := hG)) :
    txn.checkPut.spec (GF := GF) (hG := hG) := by
  intro trace mw s γ kind le γl p o L
  wp_start as ⟨%Htr, Htx, #Hp, #Hle, Hu⟩
  (try wp_auto)
  wp_apply (hLease le γl p o L) $$ [$Hle $Hp $Hu] as %err ⟨Hu, Herr⟩
  (try wp_auto)
  icases Herr with (⟨%Herr, #Hlok⟩ | ⟨%Hne, #He⟩)
  · subst Herr
    (try wp_auto)
    wp_apply (hCheck trace mw s γ kind p o) $$ [$Htx $Hp] as %r %err2 ⟨Htx, Hout⟩
    · ipureintro; exact Htr
    (try wp_auto)
    iapply HΦ
    iframe Htx Hu
    icases Hout with (⟨%He2, %Hn, -⟩ | ⟨%Hn, #He2⟩)
    · ileft
      isplitl []
      · ipureintro; exact ⟨He2, Hn⟩
      iexact Hlok
    · iright; iright
      isplitl []
      · ipureintro; exact ⟨Hn.1, Hn.2.1⟩
      iexact He2
  · -- the lease not found
    ihave #He' := He
    iunfold txn.errVarIs at He'
    icases He' with ⟨%e, -, %Hee⟩
    subst Hee
    (try wp_auto)
    iapply HΦ
    iframe Htx Hu
    iright; ileft
    isplitl []
    · ipureintro; exact Hne
    iexact He

end proof

end EtcdGrove
end Perennial
