/-
**The `UberApplier`'s KV triples at the latest state from its construction** (the auth plan's
E3k, 2026-10-27). Lean-first (no Rocq counterpart).

`uberKVL_of_base`: the uber-applier's base applier's auth layer as `NewUberApplier` leaves it
(`uberBaseAuth`, `uberIs`'s `baseAuth`), its store's checks at the latest state (`isAuthStoreL`, the real store's from
its invariant: `isAuthStoreL_of_authInv`) and its lessor finding no lease (`lookupNil`) give its
latest-state KV triples (`uberKVL`, at the inner chain `quota` over `backend`), through the auth
applier's (`applierKVL_auth`, E2y).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.BaseAuth
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyFnKVL
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.DispatchKVL

@[expose] public section

set_option linter.unusedSectionVars false

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

/-- **The uber-applier's KV triples at the latest state, from its construction** (see the file
header). -/
theorem apply.uberKVL_of_base
    (hRange : apply.authApplierV3.Range.specL (GF := GF) (hG := hG))
    (hDel : apply.authApplierV3.DeleteRange.specL (GF := GF) (hG := hG))
    (hPut : apply.authApplierV3.Put.specL (GF := GF) (hG := hG))
    (hTxn : apply.authApplierV3.Txn.specL (GF := GF) (hG := hG))
    (ua : GoInterface) (E : apply.AEnv GF) (au le : GoInterface) (L : List auth.AuthState → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.uberBaseAuth ua E au le ∗ apply.isAuthStoreL au E.RD E.authMode L ∗ apply.lookupNil le ⊢
      apply.uberKVL ua E (.quota .backend) L := by
  iintro ⟨#Hpkg, #Hb, #HsL, #Hnil⟩
  iunfold apply.uberBaseAuth at Hb
  icases Hb with ⟨%p, %opts, %Hpo, #Hu⟩
  obtain ⟨Hua, Hau, Hle⟩ := Hpo
  subst Hau Hle
  ihave #Hu' := Hu
  iunfold apply.uberIs at Hu'
  icases Hu' with ⟨-, -, -, -, -, %base, #Hbf, -, -, #Hbase⟩
  iunfold apply.baseAuth at Hbase
  icases Hbase with ⟨%pa, %inner, %Hpa, #Hai, #Hin, #Has, #Hle⟩
  subst Hpa
  ihave #HaL : apply.authIsL E pa L $$ []
  · iunfold apply.authIsL
    iexists opts.AuthStore'
    iframe Has HsL
  ihave #Hln : apply.lessorNil pa $$ []
  · iunfold apply.lessorNil
    iexists opts.Lessor'
    iframe Hle Hnil
  ihave #Hkvl := apply.applierKVL_auth hRange hDel hPut hTxn E (.quota .backend) inner pa L $$
    [Hpkg Hai HaL Hln Hin]
  · iframe Hpkg Hai HaL Hln Hin
  iunfold apply.uberKVL
  iexists p, opts
  isplitr
  · ipureintro; exact Hua
  iframe Hu
  iexists _
  iframe Hbf
  simp only [apply.baseChain]
  iexact Hkvl

end proof

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.apply.uberKVL_of_base
