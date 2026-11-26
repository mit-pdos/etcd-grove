/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/lib/etcdstart/NewClients.lean` (2026-10-23; linkv3p's
`newClient` proof until then, the partition plan's S3a). Lean-first (no Rocq counterpart). `New` over
`clientCfgOk` of the configuration's literal (the endpoints read-only, one dial option,
`grpc.WithNoProxy()`'s since 2026-11-24, no TLS, no credentials, the logger; `DialTimeout` and the
keepalive pair unconstrained, the default retries); the client's `cfg` field, from `New`'s post, gives
`clientNoProxy`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewClients

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]

theorem NewClients.wp_proof (wp_New : clientv3.New.spec (GF := GF) (hG := hG))
    (wp_WithNoProxy : grpc.WithNoProxy.spec (GF := GF) (hG := hG)) :
    NewClients.spec (GF := GF) (hG := hG) := by
  intro eps addrs lg V Htb Hplain
  wp_start as ⟨Hlt, #Hzlg, #Heps⟩
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hzlg
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Pg : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc $$ []
  · iPkgInit
  wp_auto
  -- (2026-11-24) `[]grpc.DialOption{grpc.WithNoProxy()}`, read-only from here on
  wp_apply wp_WithNoProxy as %o #Ho
  wp_apply wp_slice_literal (V := GoInterface) [o]
  try (isplitr; (ipureintro; rfl))
  iintro %dol ⟨Hdol, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hdol with #Hdol
  -- `clientv3.New(Config{Endpoints: eps, DialTimeout: ..., DialKeepAliveTime: ..., Logger: lg})`
  haveI : ThreadBoundLe GF (2 ^ 30) := ⟨Htb⟩
  wp_apply (wp_New _ addrs V (fun _ => iprop(False))) $$ [$Hlt] as %cl %cerr ⟨Hlt, Hcl⟩
  · iframe #
    iunfold clientCfgOk
    simp only
    iframe #
    isplitr
    · isplitr
      · iexists 1
        iunfold noProxyOptsAt, dialOptsAt
        iexists [o]
        iframe Hdol
        (try simp only [List.replicate_succ, List.replicate_zero])
        iapply BigSepL2.bigSepL2_singleton.2
        iexact Ho
      ipureintro
      refine ⟨?_, ?_⟩
      · exact Hplain
      · simp [Hlg]
    iapply clientAuthPre_anon; rfl
  icases Hcl with (⟨%Hcerr, #Hnc, #Htok, #Hcfg⟩ | %Hcfail)
  · subst Hcerr
    -- the client dials with no proxy: its configuration's one option is `WithNoProxy()`'s
    ihave #HNP : clientNoProxy (GF := GF) cl $$ []
    · iunfold clientNoProxy
      iexists _, 1
      isplitr
      · ipureintro; omega
      isplitr
      · iexact Hcfg
      iunfold noProxyOptsAt, dialOptsAt
      iexists [o]
      (try simp only)
      iframe Hdol
      (try simp only [List.replicate_succ, List.replicate_zero])
      iapply BigSepL2.bigSepL2_singleton.2
      iexact Ho
    iapply HΦ
    iframe Hlt
    ileft
    iframe #
    isplitr
    · ipureintro; rfl
    iexists _
    iframe Hcfg
    ipureintro
    first | exact ⟨rfl, rfl, rfl⟩ | simp
  · obtain ⟨Hcerr, Hnull⟩ := Hcfail
    iapply HΦ
    iframe Hlt
    iright
    ipureintro; exact ⟨Hcerr, Hnull⟩

end proof

end etcdstart
end EtcdGrove
end Perennial
