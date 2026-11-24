/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/putget/Member.lean` (2026-11-23,
`notes/putget-dist-plan.md` section 10). Lean-first (no Rocq counterpart).

The in-process putget's `Main` up to `Serve` (`Proof/.../examples/etcd/putget/Main.lean`), on a machine of its
own, after its addresses' check (`AddrOk` twice and their comparison; an invalid or repeated address returns, and
the wand of the precondition is then never opened): `zap.NewNop()`; the
member's start bundle from `ETCD_VERIFY` off (the precondition's `envVerifyOff`) and the fresh data directory and WAL area
(`etcdstart.memberStartRes_one`); `etcdstart.StartServer` from the named premises (`etcdstart.wp_StartServer1`,
shared with the in-process `Main`: `alloc1` inside); the client's putget invariant allocated from the
bootstrap log's KV state (`client.putGetInv_alloc_log`, as the in-process `Main`); the member's view
published with `Pub` (`etcd_dist.env_publish`, `Pub` from the invariant by `memberPubOk`); `etcdstart.Serve`
on a member machine (`etcd_dist.Serve_dist`, a trust-boundary axiom until #24's S2,
`notes/putget-dist-plan.md` §12); `holdForever()`, which does not return. Every step's error ends `Member` (`return`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Member
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.holdForever
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ServeDist
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartOne
public import Proof.go_etcd_io.etcd.client.v3.PutGetInvAlloc
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.AddrOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AddrPlain

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putget_dist

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Assumptions]

set_option maxHeartbeats 800000 in
theorem Member.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_StartServer : etcdstart.StartServer.spec (GF := GF) (hG := hG))
    (wp_holdForever : holdForever.spec (GF := GF) (hG := hG))
    (wp_Serve_dist : etcd_dist.Serve_dist.spec (GF := GF) (hG := hG))
    (wp_AddrOk : AddrOk.spec (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law)
    -- (premises to axioms, 2026-11-24: until then the premise `bootMarshal`) `proto.Marshal`'s spec at a boot conf change
    (wp_MarshalBoot : proto.MarshalBootConfChange.spec (GF := GF) (hG := hG)) :
    Member.spec (GF := GF) (hG := hG) := by
  intro CS π TB RB peer client id ctxs boot γE Pub Hbf hlp hlc HLv Haf Hbuq Hrf Hdbo Hms
  have Htb : threadBound GF ≤ 2 ^ 28 := TB.threadBound_le
  have Hrb48 : receiptBound GF ≤ 2 ^ 48 := RB.receiptBound_le
  have HrbN : receiptBound GF ≤ 2 ^ 48 - 1 + 1 := Nat.le_trans RB.receiptBound_le (by decide)
  have HwbN : 2 ^ 48 - 1 + 7 + bootWB ≤ backend.wbInit := by unfold bootWB backend.wbInit; omega
  wp_start as ⟨Htok, Hw⟩
  (try wp_auto)
  -- the addresses' check: `!AddrOk(peer) || !AddrOk(client) || peer == client` returns
  wp_apply wp_AddrOk _ hlp
  cases hp : Net.addrOk peer
  · simp only [Bool.not_false]
    try wp_auto
    iapply HΦ; itrivial
  simp only [Bool.not_true]
  try wp_auto
  wp_apply wp_AddrOk _ hlc
  cases hc : Net.addrOk client
  · simp only [Bool.not_false]
    try wp_auto
    iapply HΦ; itrivial
  simp only [Bool.not_true]
  try wp_auto
  by_cases hpc : peer = client
  · simp only [hpc, decide_true]
    try wp_auto
    iapply HΦ; itrivial
  simp only [hpc, decide_false]
  try wp_auto
  have hpl := etcd_dist.addrOk_plainPeerURL hp
  have Hpf := etcd_dist.addrOk_addrFits hp
  have Hcf := etcd_dist.addrOk_addrFits hc
  ispecialize Hw $$ %(by simp [hp, hc, hpc])
  icases Hw with ⟨#Hprem, #Hvoff, Hwa, Hshare, #Hpub⟩
  iunfold memberShare at Hshare
  icases Hshare with ⟨#Haddr, Hhalf, #Hinv⟩
  -- the imports' package facts
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Pes : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  (try wp_auto)
  -- `zap.NewNop()`
  wp_apply wp_NewNop as %lg #Hlgz
  (try wp_auto)
  -- `StartServer(Name, peer, client, lg)`
  ihave Hstart := etcdstart.memberStartRes_one (GF := GF) name $$ [Hwa]
  · iframe; iframe #
  wp_apply (etcdstart.wp_StartServer1 wp_StartServer wp_MarshalBoot hne (2 ^ 48 - 1) name peer client lg id ctxs boot Hbf hpl
      (by decide) (by decide) Hpf Hcf Htb Hrb48 HrbN HwbN Haf Hbuq Hdbo) $$ [Htok Hstart] as %srv %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, %ρ, %E₀, %γn, Hup, Hetcd⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  wp_auto
  -- the client's invariant, at the bootstrap log's KV state
  imod (EtcdGrove.client.putGetInv_alloc_log ρ.rd (kvModel ρ.rd.kv (bootEntries (LogEntry.toEntries boot 0)))
      go!"k" go!"v" ⊤) $$ Hetcd with ⟨%γf, #Hpg⟩
  -- the member's view published at `γE`, with `Pub` (from the invariant)
  ihave #HP : □ Pub (etcd_dist.memberView ρ) $$ []
  · iunfold memberPubOk at Hpub
    imodintro
    ihave HPg := Hpub $$ %ρ.rd %γf Hpg
    iexact HPg
  imod (etcd_dist.env_publish_h ⊤ γE CoPset.subseteq_top Pub (etcd_dist.memberView ρ)) $$ Hhalf Hinv HP
    with #Hν
  -- `Serve(s, client)` on a member machine (`Serve_dist`)
  wp_apply (wp_Serve_dist srv client ρ E₀ lg γn id γE (etcd_dist.memberView ρ)) $$ [Hup] as %serr -
  · iframe; iframe #
    ipureintro; exact ⟨Hms, Hbuq, Hrf, HLv, rfl⟩
  cases serr with
  | ok ei =>
    wp_auto
    iapply HΦ; itrivial
  | nil =>
  wp_auto
  -- `holdForever()`: it does not return
  wp_apply wp_holdForever as HF
  iexfalso
  iexact HF

end proof

end etcd_putget_dist
end EtcdGrove
end Perennial
