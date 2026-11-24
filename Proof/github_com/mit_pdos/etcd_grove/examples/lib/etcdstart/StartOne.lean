/-
**The one member of a new cluster started from its named premises** (2026-11-23,
`notes/putget-dist-plan.md` section 10). Lean-first (no Rocq counterpart).

`wp_StartServer1`: `StartServer.spec` (a hypothesis, as `Start.lean`'s `wp_Start_built`) at the one-member
cluster of member `id`, from what a one-member program holds: the member's named Iris premises
(`premises`, `OneMember.lean`: `bootstrap`'s contract, `proto.Marshal`'s at the bootstrap log, the raft
wrapper's), its start bundle without addresses (`memberStartRes name {}`: `ETCD_VERIFY` off, its data
directory and WAL area fresh), the logger, the main thread's token, `context`'s `closedchan`. Inside, the
ghost state `NewServer` takes (`alloc1`) and the one-member directory of the peer URL `http://peer`. The
result: an error with the token, or the member started (`memberUp`) with the KV state of the bootstrap log
(`etcdKV`, what a client's invariant is allocated from: `client.putGetInv_alloc_log`).

The in-process putget's `Main` (`examples/etcd/putget`) and `putget_safe`'s member (`examples/etcd/dist/putget`,
`Member`) start their member this way.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartServer
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.OneMember

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section bundle
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- **The start bundle of a member that listens on no address** (`memberStartRes_intro` at one member and
no address): `ETCD_VERIFY` off, its data directory and its WAL area fresh. -/
theorem memberStartRes_one (n : GoString) :
    envVerifyOff (GF := GF) ∗ dataDirFresh (GF := GF) (memberDataDir n) ∗
        memberAreasFresh (GF := GF) (memberDataDir n) ⊢
      memberStartRes (GF := GF) n {} := by
  iintro ⟨#Hv, Hd, Hw⟩
  ihave H := memberStartRes_intro (GF := GF) [(n, {})] [] [] [memberDataDir n]
    (by simp [MemberAddrs.addrs]) (List.Perm.refl _) $$ [Hd Hw]
  · isplitl [Hd]
    · isplitr
      · iapply BigSepL.bigSepL_nil.2; iempintro
      isplitr
      · iapply BigSepL.bigSepL_nil.2; iempintro
      isplitl [Hd]
      · iapply BigSepL.bigSepL_cons.2
        iframe Hd
        iapply BigSepL.bigSepL_nil.2; iempintro
      iexact Hv
    iapply BigSepL.bigSepL_cons.2
    iframe Hw
    iapply BigSepL.bigSepL_nil.2; iempintro
  icases H with ⟨H, -⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H, -⟩
  iexact H

end bundle

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Assumptions]

set_option maxHeartbeats 800000 in
/-- See the file header. -/
theorem wp_StartServer1 (wp_StartServer : StartServer.spec (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law) [go_etcd_io.etcd.cache.v3.Assumptions]
    (N : Nat) (name peer client : GoString) (lg : Loc) (id : w64) (ctxs : List (List w8))
    (boot : List LogEntry) (Hbf : BootFacts id ctxs boot)
    (hpl : types.plainPeerURL (go!"http://" ++ peer)) (hu : utf8Valid name) (hn : name.length ≤ 200)
    (hpf : addrFits peer) (hcf : addrFits client)
    (Htb : threadBound GF ≤ 2 ^ 28) (Hrb48 : receiptBound GF ≤ 2 ^ 48)
    (HrbN : receiptBound GF ≤ N + 1) (HwbN : N + 7 + bootWB ≤ backend.wbInit)
    (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota) (Hdbo : storage.diskOk) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart ∗
        zapLoggerOk lg ∗ threadTok ∗ premises (GF := GF) name peer client N id ctxs boot ∗
        context.isClosedchanInit ∗ memberStartRes (GF := GF) name {} }}
      (App (App (App (App
        (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartServer))
        (Val #name)) (Val #peer)) (Val #client)) (Val #lg))
    {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
        (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
        (⌜err = GoInterface.nil⌝ ∗ ∃ (ρ : ReqNames) (E₀ : apply.AEnv GF) (γn : NetNames GF),
          memberUp s ρ E₀ lg γn id ∗
          etcdKV ρ.rd.kv (kvStateOf (kvModel ρ.rd.kv (bootEntries (LogEntry.toEntries boot 0))))) }} := by
  iintro %Φ ⟨#Hpkg, #Hlgz, Htok, #Hprem, #Hcci, Hstart⟩ HΦ
  iunfold premises at Hprem
  icases Hprem with ⟨#Hboot, #Hmarsh, #Hzap, #Htd, #Hns⟩
  ihave #Hb := bootPremise_of N [id] (LogEntry.toEntries boot 0) ctxs (dir1 peer id) name name
      (urls1 name peer client) id (cfgOk name name) (urls1 name peer client)
      (fun _ h => h) (fun _ h => h) $$ Hboot
  ihave #Hcom : commonPremises (GF := GF) $$ []
  · iunfold commonPremises; iframe #
  -- the ghost state `NewServer` takes (`alloc1`)
  have hblen0 : boot.length = 1 := by rw [Hbf.boot.1]; rfl
  imod (alloc1_false hne id ctxs boot Hbf (dir1 peer id) (dirOne_member id _)
      (by omega) (by omega)) $$ Hmarsh
    with ⟨%γ, %ρ, %E₀, %Φs, %γn, %Hal, Hmb, #Hnet, Hetcd⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hlog⟩ := Hal
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  -- the one-member directory is well formed
  have Hdirok : netDirOk (dir1 peer id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) hpl
  -- no peer address: the start bundle is the fresh bundle at the network `γn`
  ihave Hfresh := memberStartRes_fresh _ _ γn rfl $$ Hstart
  wp_apply (wp_StartServer N name peer client lg (LogEntry.toEntries boot 0) ctxs (dir1 peer id) id γ
      ρ E₀ Φs γn .none Htb Hrb48 HrbN HwbN hvs hrule hboot hblen hγn1 hγn2 Hdirok
      (by simp [dir1, dirOne]) (rafthttp.bootCfg_dirOne id _) hu hn hpf hcf Haf Hbuq Hdbo)
    $$ [Htok Hmb Hfresh] as %srv %err Hr
  · iframe; iframe #
  rw [kvModelSt_boot _ (fun _ _ => True) _ _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot)]
  iapply HΦ
  icases Hr with (⟨%Herr, Htok⟩ | ⟨%Herr, Hup, -⟩)
  · ileft; iframe Htok; ipureintro; exact Herr
  · iright
    isplitr
    · ipureintro; exact Herr
    iexists ρ, E₀, γn
    iframe

end proof

end etcdstart
end EtcdGrove
end Perennial
