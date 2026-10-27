/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/Lease__persistTo.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Lease__persistTo
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.MustUnsafePutLease

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.Lease.persistTo.wp_proof
    (hPut : schema.MustUnsafePutLease.spec (GF := GF) (hG := hG)) :
    lease.Lease.persistTo.spec (GF := GF) (hG := hG) := by
  intro l b P f T R Rb rb Pre Q Post id t r dq1 dq2 dq3
  wp_start as ⟨#Hbk, Hcs, HT, HR, HRb, Hid, Ht, Hr⟩
  ihave #Hschema : isPkgInit (PROP := IProp GF)
    pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  iunfold leaseBackend at Hbk
  icases Hbk with ⟨⟨%bk, #Hbkv⟩, %bi, %Hbi, #HBatch⟩
  subst Hbi
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_bind (App (Val #(methods bi.ty go!"BatchTx" bi.v)) (Val #()))
  iapply HBatch $$ [] [-]
  · itrivial
  inext
  iintro %tx #Htx
  iunfold leaseBatchTx at Htx
  icases Htx with ⟨%Lk, #HLock, #HUnsafePut, #HUnlock⟩
  (try wp_auto)
  wp_bind (App (Val #(methods tx.ty go!"LockInsideApply" tx.v)) (Val #()))
  iapply HLock $$ [Hcs HT HR] [-]
  · iframe Hcs HT HR
  inext
  iintro HLk
  (try wp_auto)
  wp_bind (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.MustUnsafePutLease))
    (Val #(GoInterface.ok tx))) (Val #lpb_ptr))
  iapply (hPut tx lpb_ptr _ bk iprop(Lk iprop(Post ∗ R) ∗ Rb rb)
      iprop(Lk iprop(Post ∗ R) ∗
        Rb (mvcc.rbSet rb mvcc.leaseName (u64Le id).reverse (leaseEnc id t r)))) $$ [lpb HLk HRb] [-]
  · iframe Hschema Hbkv lpb HLk HRb
    isplitr
    · ipureintro; rfl
    iintro !> %key %val %Φ' !> ⟨#Hk, #Hv, HL, HRb⟩ HΦ'
    iapply HUnsafePut $$ [HL HRb] HΦ'
    iframe HL Hbkv Hk Hv HRb
    ipureintro; rw [List.length_reverse, u64Le_length]
  inext
  iintro ⟨-, HLk, HRb⟩
  (try wp_auto)
  wp_bind (App (Val #(methods tx.ty go!"Unlock" tx.v)) (Val #()))
  iapply HUnlock $$ [HLk] [-]
  · iexact HLk
  inext
  iintro ⟨HPost, HR⟩
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
