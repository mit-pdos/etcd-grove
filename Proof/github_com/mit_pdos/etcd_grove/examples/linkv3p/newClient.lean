/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/linkv3p/newClient.lean` (the partition
plan's S3a, 2026-10-20). Lean-first (no Rocq counterpart). linkv3's `Main`'s `clientv3.New` step
(`Proof/.../linkv3/Main.lean`): the endpoint slice literal, read-only; `New` over `clientCfgOk` of
the configuration's literal (`MaxUnaryRetries: 1`, so `clientKVOnce`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.newClient
public import Spec.go_etcd_io.etcd.client.v3.New

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

theorem newClient.wp_proof (wp_New : clientv3.New.spec (GF := GF) (hG := hG)) :
    newClient.spec (GF := GF) (hG := hG) := by
  intro eps addrs lg V Htb Hlg Hplain
  wp_start as #Heps
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  wp_auto
  -- `clientv3.New(Config{Endpoints: eps, Logger: lg, MaxUnaryRetries: 1})`
  wp_apply (wp_New _ addrs V) $$ [] as %cl %cerr Hcl
  · iframe #
    iunfold clientCfgOk
    simp only
    iframe #
    isplitr
    · isplitr
      · iapply ownSlice_nil
      ipureintro
      refine ⟨?_, ?_⟩
      · exact Hplain
      · simp [Hlg]
    ipureintro; exact Htb
  icases Hcl with (⟨%Hcerr, #Hnc, Hone⟩ | %Hcfail)
  · subst Hcerr
    ihave #Hone := Hone $$ []
    · ipureintro; trivial
    iapply HΦ
    ileft
    iframe #
    ipureintro; rfl
  · obtain ⟨Hcerr, Hnull⟩ := Hcfail
    iapply HΦ
    iright
    ipureintro; exact ⟨Hcerr, Hnull⟩

end proof

end linkv3p
end EtcdGrove
end Perennial
