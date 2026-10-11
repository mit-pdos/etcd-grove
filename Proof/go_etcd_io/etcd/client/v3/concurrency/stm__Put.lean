/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/stm__Put.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.stm__Put
public import Spec.go_etcd_io.etcd.client.v3.OpPut
public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTMMaps

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem stm.Put.wp_proof (hPut : EtcdGrove.OpPut.spec (GF := GF) (hG := hG)) :
    stm.Put.spec (GF := GF) (hG := hG) := by
  intro b pfx writes k v sl gs
  wp_start as ⟨Hws, #Hopts, %Hok⟩
  obtain ⟨Hpk, Hnp, Htx⟩ := Hok
  unfold stmWsetOwn
  icases Hws with ⟨%m, %wsMap, Hf, Hm, #Hat⟩
  wp_auto
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_apply hPut k v sl gs $$ [$Hcv $Hopts] as %op #Hop
  · ipureintro; exact Hnp
  (try wp_auto)
  wp_apply wp_mapInsert $$ Hm as Hm
  iapply HΦ
  iexists m, _
  iframe Hf Hm
  iapply writesAt_insert
  iframe Hat
  unfold writeAt
  isplitr
  · ipureintro; exact ⟨rfl, Hpk⟩
  iexists _
  iframe Hop
  ipureintro; exact Htx

end proof

end concurrency
end EtcdGrove
end Perennial
