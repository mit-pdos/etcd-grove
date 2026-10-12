/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.checkLease

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.checkLease.wp_proof : txn.checkLease.spec (GF := GF) (hG := hG) := by
  intro le γl p o
  wp_start as ⟨#Hle, #Hp⟩
  ihave Hti : (txn.txnInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hti with ⟨⟨%eL, #HeL⟩, -⟩
  iunfold txn.isTxnLessor at Hle
  icases Hle with ⟨-, %li, %Hli, #HLookup⟩
  subst Hli
  iunfold txn.putRequestIs at Hp
  icases Hp with ⟨%Hpnn, %ksl, %vsl, %k, %v, %lease, %pk, %iv, %il, #Hk, #Hks, #Hv, #Hvs, #Hl,
    #Hpk, #Hiv, #Hil, -, %Ho⟩
  subst Ho
  (try wp_auto)
  wp_if_destruct
  · -- no lease
    iapply HΦ
    ileft
    isplitl []
    · ipureintro; rfl
    iunfold txn.leaseOk
    ileft
    ipureintro; rfl
  · -- a lease: the lessor's `Lookup`
    ihave #HL := HLookup $$ %lease
    wp_apply HL as %l Hl
    (try wp_auto)
    wp_if_destruct
    · -- not found
      (try wp_auto)
      iapply HΦ
      iright
      isplitl []
      · ipureintro; exact Hif
      iunfold txn.errVarIs
      iexists eL
      iframe HeL
      ipureintro; rfl
    · icases Hl with (%Hl | #Hk)
      · exact absurd Hl Hif
      (try wp_auto)
      iapply HΦ
      ileft
      isplitl []
      · ipureintro; rfl
      iunfold txn.leaseOk
      iright
      simp only [txn.putOpOf]
      iexact Hk

end proof

end EtcdGrove
end Perennial
