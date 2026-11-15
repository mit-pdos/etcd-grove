/-
`Main()` (`examples/etcd/auth/authkv.go`; the auth plan's E2b): **proved** (2026-10-31), over its
callees' specs. Lean-first (no Rocq counterpart).

The steps: the logger; the member's ghost state with auth on (`ak_alloc`) and the history invariant
(`akHist_alloc`); `startServer` (`memberUpOn`); then `Run` on the started member at authkv's client
address (`Run.lean`: `Serve` with auth on, the set-up, the user clients, the workloads, root's last
write, the history's check and u's watch check; until the auth3 Scope's Q6, 2026-11-14, those steps
were this proof's, and `Run` is the same code moved into a function auth3 shares). An error of
`startServer` returns `Failed`.

What the result rests on (`etc/tcb-collections/authkv.txt`; no `sorry` since 2026-11-13): the
trust-boundary axioms its callees' proofs reach, and `startServer`'s spec, a premise here, linked in
`Results.lean` (`authkv_startServer`, at D22's named hypothesis `authSchemaSrv`), and so in the
closed theorem (`Adequacy.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.auth.startServer
public import Spec.go_uber_org.zap.NewNop
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.MainAlloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Hist
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth.Assumptions]

set_option maxHeartbeats 1600000 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_startServer : startServer.spec (GF := GF) (hG := hG))
    (wp_Run : Run.spec (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS ES FS RS CRE CEC N id ctxs boot Hbf Htb HLv Hrb48 HrbN HwbN Haf Hbuq Hrf Hdbo Hms hAs
  wp_start as ⟨Hstart, Htok, #Hprem⟩
  -- (hub step 7) the client address's listen right, out of the member's start bundle (to `Serve`)
  icases etcdstart.memberStartRes_client _ _ _ rfl $$ Hstart with ⟨Haddr, Hstart⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hboot, #Hmarsh, #Hzap, #Htd, #Hns⟩
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_NewNop as %lg #Hlgz
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hlgz
  (try wp_auto)
  -- the member's ghost state with auth on, the client's half of the KV state, its view of the
  -- auth history (`ak_alloc`), and the history invariant over the former (`akHist_alloc`)
  have hblen0 : boot.length = 1 := by rw [Hbf.boot.1]; rfl
  imod (ak_alloc hne id ctxs boot Hbf (by omega) (by omega)) $$ Hmarsh
    with ⟨%γ, %ρ, %E₀, %Φs, %γn, %σ₀, %Hal, Hmb, #Hnet, Hetcd, Hview⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hσ₀, hc0, hlog⟩ := Hal
  imod (akHist_alloc ρ.rd.kv σ₀ hσ₀) $$ Hetcd with #Hhist
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  ihave #Hcom : etcdstart.commonPremises (GF := GF) $$ []
  · iunfold etcdstart.commonPremises; iframe #
  have Hdirok : netDirOk (akDir id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) (by decide)
  -- `startServer(lg)`: the member with auth on
  -- (hub step 7) no peer address: the start bundle is the fresh bundle at the network `γn`
  ihave Hfresh := etcdstart.memberStartRes_fresh _ _ γn rfl $$ Hstart
  wp_apply (wp_startServer N lg (LogEntry.toEntries boot 0) ctxs (akDir id) id γ ρ E₀ Φs γn Htb
      Hrb48 HrbN HwbN hvs hrule hboot hblen hγn1 hγn2 Hdirok (by simp [akDir, dirOne]) (rafthttp.bootCfg_dirOne id _) Haf
      Hbuq Hdbo)
    $$ [Htok Hmb Hfresh] as %srv %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, %γa, Hup⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; left; rfl
  subst Herr
  wp_auto
  -- `return Run(s, clientAddr, lg)`: the rest of `Main` (`Run.lean`), on the started member
  wp_apply (wp_Run srv lg go!"127.0.0.1:23916" ρ E₀ γn id γa (by unfold plainEndpoint; decide) Htb HLv
      Hrb48 Hbuq Hrf Hms hAs hc0 hlog) $$ [Haddr Hup Hview] as %r %Hr
  · iframe; iframe #
  iapply HΦ; ipureintro; exact Hr

end proof

end etcd_auth
end EtcdGrove
end Perennial
