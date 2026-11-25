/-
`grantPut(cli, k)` (`examples/etcd/authlease/authlease.go`; auth-lease S4, item 9): **proved**, over its
callees' specs: the grant through `client_lease_grant_on` (the client's `Lease`, a `*lessor` over its
connection, `clientTokAt`), the caller's ghost step `Fix` at the granted id, then the leased put through
`client_put_on` (`cli.Put` unfolded to its `KV`'s, as `auth/ClientOn.lean`'s `client_Put_onG`), its one
option `WithLease(id)`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.grantPut
public import Spec.go_etcd_io.etcd.client.v3.WithLease
public import Spec.context.ErrAny
public import Spec.context.WithTimeoutBackgroundMd
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.ClientOn
public import Proof.go_etcd_io.etcd.client.v3.ResultsOn
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver client etcd_auth

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]

/-- `WithLease(id)`'s request: it does not panic and is a put. -/
theorem opPutModel_lease_ok (k : GoString) (id : w64) :
    ¬ (opPutModel k go!"v" [withLeaseM id]).putPanics ∧ (opPutModel k go!"v" [withLeaseM id]).t = W64 2 := by
  refine ⟨?_, rfl⟩
  simp [opPutModel, OpFull.putPanics, opFold, withLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero]

theorem grantPut.wp_proof
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_WithTimeout : context.WithTimeoutBackgroundMd.spec (GF := GF) (hG := hG))
    (wp_WithLease : WithLease.spec (GF := GF) (hG := hG)) :
    grantPut.spec (GF := GF) (hG := hG) := by
  intro CS ES FS RS cli k addr s E ρ cid mid n F P Qg Qp R R' hon hrev hsz hAs
  wp_start as ⟨Hlt, #Htk, #Hn, #Hgr, #Hput, #HF, #HQg, HR, HFix⟩
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Htk0 := Htk
  iunfold clientTokAt at Htk0
  icases Htk0 with ⟨%api, %conn, #Hkvf, #Hobj, #Htok, -, -, %lp, #Hlf, #Hrem⟩
  (try wp_auto)
  -- `ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd wp_WithTimeout wp_ErrAny hAs _)
    as %gctx %gcd %gcancel ⟨#Hgcancel, #Hgctx, #Hgce, -, #Hgout, -⟩
  (try wp_auto)
  -- `g, err := cli.Lease.Grant(ctx, grantTTL)`
  wp_apply (client_lease_grant_on lp conn addr (srvTLSId s) E ρ (mvcc.api.mvccLeases E.γ) gctx none gcd n grantTTLv Qg)
    $$ [$Hlt] as %gr %gerr ⟨Hlt, Hg⟩
  · iframe #
    iintro !> %id
    iapply HQg
  (try wp_auto)
  wp_apply Hgcancel
  (try wp_auto)
  icases Hg with (⟨%Hgerr, %mg, %hg, #Hghdr, #Hghf, #Hgid, -, %Hid, -, -, %md, -, Hres, -⟩ | ⟨%Hgfail, -⟩)
  rotate_left
  · cases gerr with
    | nil => exact absurd rfl Hgfail.1
    | ok ei =>
      (try wp_auto)
      iapply HΦ; iframe Hlt; ileft; ipureintro; rfl
  subst Hgerr
  (try wp_auto)
  -- the caller's ghost step at the granted id
  iunfold v3rpc.leaseGrantResT at Hres
  ihave Hres := Hres $$ %hon
  icases Hres with ⟨%hm, %L, -, -, HQgid⟩
  imod HFix $$ %mg.id %Hid [HQgid] HR with ⟨HR', #Hpu⟩
  · iexists _; iexact HQgid
  -- `ctx, cancel = context.WithTimeout(...)`
  wp_apply context.wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bgMd wp_WithTimeout wp_ErrAny hAs _)
    as %pctx %pcd %pcancel ⟨#Hpcancel, #Hpctx, #Hpce, -, #Hpout, -⟩
  (try wp_auto)
  -- `clientv3.WithLease(g.ID)`, the options slice
  wp_apply wp_WithLease mg.id as %f #Hf
  (try wp_auto)
  wp_apply wp_slice_literal (l := [f])
  isplitr
  · ipureintro; rfl
  iintro %slo ⟨Hslo, -⟩
  ipersist Hslo
  ihave #Hopts : optsAt (GF := GF) _ [withLeaseM mg.id] $$ []
  · unfold optsAt
    iexists [f]
    iframe Hslo
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %i %f' %g %Hf' %Hg'
    rcases i with _ | i
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hf' Hg'; subst Hf' Hg'; iexact Hf
    · simp at Hf'
  (try wp_auto)
  -- `cli.Put(ctx, k, "v", opts...)`
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Put_unfold.method_unfold]
  wp_pures
  (try wp_auto)
  have hok := opPutModel_lease_ok k mg.id
  wp_apply (client_put_on api conn addr (srvTLSId s) E ρ cid mid pctx none pcd k go!"v" _ [withLeaseM mg.id] (Qp mg.id) F
      (hsz mg.id) hok.1 hok.2 (Or.inr hrev)) $$ [$Hlt] as %presp %perr ⟨Hlt, Hp⟩
  · iframe #
    ileft
    imodintro
    rw [leasePut_wire]
    iapply Hpu
    · iexact Htok
    · ipureintro; rfl
  (try wp_auto)
  wp_apply Hpcancel
  (try wp_auto)
  icases Hp with (⟨%Hperr, %mp, -, Hrep, -⟩ | ⟨%Hperr, -⟩)
  · subst Hperr
    (try wp_auto)
    iapply HΦ
    iframe Hlt
    iright
    isplitl []
    · ipureintro; rfl
    iframe HR'
    iunfold putReplied at Hrep
    icases Hrep with ⟨%hm', %x, %x', %l, %skip, -, -, -, -, -, %lt, -, HQp⟩
    iexists _; iexact HQp
  · cases perr with
    | nil => exact absurd rfl Hperr.1
    | ok ei =>
      (try wp_auto)
      iapply HΦ; iframe Hlt; ileft; ipureintro; rfl

end proof

end etcd_authlease
end EtcdGrove
end Perennial
