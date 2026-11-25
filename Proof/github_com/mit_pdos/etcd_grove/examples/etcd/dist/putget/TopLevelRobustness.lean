/- Lean-first (no Rocq counterpart).

# `etcd/dist/putget`: the proof skeleton of `putget_safe` (`notes/putget-dist-plan.md`, section 5)

**`putget_safe`** (`theorem putget_safe : putget_safe.spec`): `putget_safe_of_boot` proves the statement from
one named hypothesis, `PutgetBoot`, which `putget_safe` discharges over the interim cross-machine axioms
(below). No `sorry`, no hypothesis left. The bridge from one WP per machine to `Robust []` is proved
(`Net.robust_of_distBootIT`, `Net/Statement/DistBridgeExts.lean`, over any list of extensions with the net
extension, through Perennial's `goose_dist_adequacy_below`: the statement's thread bound `putgetThreads`
is each machine's `threadBound`, independent of the receipts), with the interpretations' initial-state conditions from the statement's `FsInit` premises
(`etcdNetExts_initP`).

`PutgetBoot`: at the statement's premises (and the addresses valid, from `DistDeploy`), the start update
from the two addresses unset to a share per machine, each machine's boot program safe from its share and
its whole start (`DistBootWpST putgetSteps putgetThreads`: its files' and listeners' start resources, its
main thread's token, the logic's bounds: at most `2 ^ 48` receipts, the member's ceiling, and the thread
bound `putgetThreads`, which also gives the served member's `srvLevels`; the bridge `robust_of_distBootIT`
runs an execution of `n` steps at `n + 1` receipts). Over the interim cross-machine axioms
(`notes/putget-dist-plan.md` §12; `etcd/dist/S2Interim.lean` and the axioms `Serve_dist`,
`Client_Put_dist`, `Client_Get_dist`), `putget_safe` discharges it:
* the start (`putget_start`, proved): the publication name and invariant (`envPub_start`), the client
  address set (`etcdAddr_set`), the member's and the client's shares (`Defs.lean`);
* the member's boot (`member_boot`, `AdequacyMember.lean`, proved): the in-process `Main.wp_proof`'s first
  half (`etcdstart.wp_StartServer1`, shared with it), the view published (`env_publish`), `Serve` on a
  member machine (`Serve_dist`), from the statement's `envVerifyOff` (`HEnvTok`) and the machine's own
  start (its files' fresh areas; the metric IDs' registration rights allocated by each machine's boot,
  prom-registry);
* the client's boot (`client_boot`, `AdequacyClient.lean`, proved): the in-process second half, its
  `Put` learning the view (`Client_Put_dist`), its `Get` at it (`Client_Get_dist`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.TopLevelRobustness
public import Net.Statement.DistBridgeExts
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.AdequacyMember
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.AdequacyClient

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Perennial
namespace EtcdGrove
namespace etcd_putget_dist

open Iris Iris.BI Iris.ProgramLogic Robustness go_etcd_io.raft.v3 Net

attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem GooseGlobalGS.gooseInvGS

/-- **The addresses the start sets**: the peer address if the member's check passes (`AddrOk` of both,
distinct), the client address if the client's does; distinct and valid by construction
(`startAddrs_nodup`, `startAddrs_ok`), what the bridge needs to hand out their `addrUnset`. -/
def startAddrs (peer client : GoString) : List GoString :=
  (if Net.addrOk peer = true ∧ Net.addrOk client = true ∧ peer ≠ client then [peer] else []) ++
    (if Net.addrOk client = true then [client] else [])

theorem startAddrs_nodup (peer client : GoString) : (startAddrs peer client).Nodup := by
  unfold startAddrs
  split <;> split <;> simp_all

theorem startAddrs_ok (peer client : GoString) : ∀ a ∈ startAddrs peer client, Net.addrOk a = true := by
  intro a ha
  simp only [startAddrs, List.mem_append] at ha
  rcases ha with ha | ha
  · split at ha
    · rename_i h; simp only [List.mem_singleton] at ha; subst ha; exact h.1
    · simp at ha
  · split at ha
    · rename_i h; simp only [List.mem_singleton] at ha; subst ha; exact h
    · simp at ha

/-- **The two machines' boot WPs** (see the file header): at `putget_safe.spec`'s premises, the start
update from the deployment's addresses unset to a share per machine from which its boot program is safe.
The member's and the client's proofs (`member_boot`, `client_boot`). -/
def PutgetBoot : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    (_Hctx : ∀ hG : HeapGS .hasLC putgetGF,
      ContextReadErrs (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    (_Hcec : ∀ hG : HeapGS .hasLC putgetGF,
      ContextErrsClient (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    (peer client : GoString)
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry) (_Hbf : etcdstart.BootFacts id ctxs boot)
    (_Haf : authRecordsFit) (_Hbuq : apply.backendUnderQuota) (_Hrf : grpcRepliesFit)
    (_Hdbo : storage.diskOk)
    (_Hbg : etcdstart.BootGo1 name peer client id ctxs boot) (_Hfips : crypto.fips140.GodebugFips140Off)
    (σm σc : state) (_Hm : MemberFiles σm) (_Hc : ClientFiles σc)
    (_Hlp : peer.length + 1 < 2 ^ 63) (_Hlc : client.length + 1 < 2 ^ 63)
    (_HEnv : ∀ m ∈ system peer client σm σc, verifyEnvOff m.1)
    (_HEnvTok : ⊢ envVerifyOff (GF := putgetGF)),
    ∀ [GooseGlobalGS .hasLC putgetGF], receiptBound putgetGF ≤ putgetSteps →
      ⊢ ([∗list] a ∈ startAddrs peer client, Net.addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp putgetGF,
          ⌜∀ (i : Nat) (m : Expr × state), (system peer client σm σc)[i]? = some m →
            Net.DistBootWpST putgetSteps putgetThreads m.1 m.2 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ system peer client σm σc, Ps i

/-- **`putget_safe` from the two machines' boot WPs** (see the file header), by the all-stable bridge
over `etcdNetExts` with `Robust`'s thread bound (`Net.robust_of_distBootIT`), with each machine's `FsInit` from the statement. -/
theorem putget_safe_of_boot (HS : PutgetBoot) : putget_safe.spec := by
  intro _ _ _ _ _ _ _ _ _ _ Hctx Hcec peer client id ctxs boot Hbf Haf Hbuq Hrf Hdbo Hbg Hfips σm σc g
    Hm Hc Hlp Hlc HEnv HEnvTok
  refine Net.robust_of_distBootIT (GF := putgetGF) (startAddrs peer client) (system peer client σm σc) g
    putgetThreads putgetSteps ?_
    (fun hb => HS Hctx Hcec peer client id ctxs boot Hbf Haf Hbuq Hrf Hdbo Hbg Hfips σm σc Hm Hc
      Hlp Hlc HEnv HEnvTok hb) (startAddrs_nodup peer client) (startAddrs_ok peer client)
  refine etcdNetExts_initP g _ ?_
  intro m hm
  simp only [system, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact Hm.1
  · exact Hc

/-! ## Over the interim cross-machine axioms (`notes/putget-dist-plan.md` §12) -/

section start
variable [GoGlobalContext] [GoLocalContext] [go.Semantics]
  [go_etcd_io.etcd.client.v3.Assumptions]

/-- **The deployment's start** (#24's §1.3 steps 1-4, over the interim vocabulary): `γE` allocated with
the publication invariant at `Pub` (`etcd_dist.envPub_start`), the client address set to serve etcd's KV
calls for `(γE, mid)` (`etcd_dist.etcdAddr_set`, spending its `addrUnset`), the member's and the client's
shares. The peer address's `addrUnset` is unused (nothing listens there). -/
theorem putget_start [G : GooseGlobalGS .hasLC putgetGF] [π : NetProtoGS]
    (peer client : GoString) (mid : w64) (Pub : etcd_dist.EnvView → IProp putgetGF) :
    ⊢ regCtx -∗ addrUnset peer -∗ addrUnset client ={⊤}=∗
      ∃ γE, memberShare client γE mid Pub ∗ clientShare client γE mid Pub := by
  iintro #Hreg - Hc
  imod (etcd_dist.envPub_start ⊤ Pub) with ⟨%γE, Hhalf, #Hinv⟩
  imod (etcd_dist.etcdAddr_set ⊤ client γE mid) $$ Hreg Hc with #Ha
  imodintro
  iexists γE
  unfold memberShare clientShare
  iframe Hhalf
  iframe #

/-- **The start, at the addresses that pass the programs' checks** (`startAddrs`): the shares, each owed only
once its machine's check passes (`memberShareIf`, `clientShareIf`). With both checks passing, `putget_start`;
with only the client's, the publication invariant and the client address set (`envPub_start`,
`etcdAddr_set`), the member's share vacuous; with neither, the publication invariant alone. -/
theorem putget_shares [G : GooseGlobalGS .hasLC putgetGF] [π : NetProtoGS]
    (peer client : GoString) (mid : w64) :
    ⊢ regCtx -∗ ([∗list] a ∈ startAddrs peer client, addrUnset a) ={⊤}=∗
      ∃ γE, memberShareIf peer client γE mid (putgetPub (GF := putgetGF)) ∗
        clientShareIf client γE mid (putgetPub (GF := putgetGF)) := by
  unfold memberShareIf clientShareIf
  by_cases hg : Net.addrOk peer = true ∧ Net.addrOk client = true ∧ peer ≠ client
  · have hc := hg.2.1
    simp only [startAddrs, if_pos hg, if_pos hc, List.singleton_append]
    iintro #Hreg ⟨Hp, Hcl, -⟩
    imod putget_start peer client mid (putgetPub (GF := putgetGF)) $$ Hreg Hp Hcl with ⟨%γE, Hms, #Hcs⟩
    imodintro
    iexists γE
    isplitl [Hms]
    · iintro -; iexact Hms
    · iintro -; iexact Hcs
  by_cases hc : Net.addrOk client = true
  · simp only [startAddrs, if_neg hg, if_pos hc, List.nil_append, BigSepL.bigSepL_cons,
      BigSepL.bigSepL_nil]
    iintro #Hreg ⟨Hcl, -⟩
    imod (etcd_dist.envPub_start ⊤ (putgetPub (GF := putgetGF))) with ⟨%γE, -, #Hinv⟩
    imod (etcd_dist.etcdAddr_set ⊤ client γE mid) $$ Hreg Hcl with #Ha
    imodintro
    iexists γE
    isplitl []
    · iintro %h; exact absurd h hg
    · iintro -
      unfold clientShare
      iframe #
  · have hg' : ¬(Net.addrOk peer = true ∧ Net.addrOk client = true ∧ peer ≠ client) :=
      fun h => hc h.2.1
    simp only [startAddrs, if_neg hg', if_neg hc, List.nil_append, BigSepL.bigSepL_nil]
    iintro - -
    imod (etcd_dist.envPub_start ⊤ (putgetPub (GF := putgetGF))) with ⟨%γE, -, -⟩
    imodintro
    iexists γE
    isplitl []
    · iintro %h; exact absurd h hg'
    · iintro %h; exact absurd h hc

end start

/-- **`putget_safe`** (see the file header): the start is proved (`putget_start`), the member's boot is
proved (`member_boot`, at `Pub = putgetPub`), the client's boot is proved (`client_boot`), the bridge is
proved (`putget_safe_of_boot`); the cross-machine steps are the interim axioms of
`notes/putget-dist-plan.md` §12 (the table `etcd_dist.etcdSvc`, `Serve_dist`, `Client_Put_dist`,
`Client_Get_dist`; the start law `etcdAddr_set` proved over grpc's `grpc_addr_set` since the S2 interface
switch). -/
theorem putget_safe : putget_safe.spec := by
  refine putget_safe_of_boot ?_
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx Hcec peer client id ctxs boot Hbf Haf Hbuq Hrf Hdbo Hbg Hfips σm σc
    Hm Hc Hlp Hlc HEnv HEnvTok G hb
  iintro Hs
  imod netProto_alloc ⊤ with ⟨%π, #Hreg⟩
  imod putget_shares peer client id $$ Hreg Hs with ⟨%γE, Hms, Hcs⟩
  imodintro
  iexists (fun i => if i = 0 then memberShareIf peer client γE id (putgetPub (GF := putgetGF))
    else clientShareIf client γE id (putgetPub (GF := putgetGF)))
  isplitr
  · ipureintro
    intro i m hm
    match i, hm with
    | 0, hm =>
      simp only [system, List.getElem?_cons_zero, Option.some.injEq] at hm; subst hm
      exact member_boot Hctx HEnvTok peer client Hlp Hlc id ctxs boot Hbf Haf Hbuq Hrf Hdbo Hbg Hfips σm Hm γE
    | 1, hm => simp only [system, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hm; subst hm; exact client_boot Hctx Hcec client Hlc σc γE id
    | k + 2, hm => simp [system] at hm
  simp only [system, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
  isplitl [Hms]
  · iapply (show memberShareIf peer client γE id (putgetPub (GF := putgetGF)) ⊢ (if (0 : Nat) = 0 then
        memberShareIf peer client γE id (putgetPub (GF := putgetGF))
        else clientShareIf client γE id (putgetPub (GF := putgetGF))) by
      rw [if_pos rfl])
    iexact Hms
  isplitl [Hcs]
  · iapply (show clientShareIf client γE id (putgetPub (GF := putgetGF)) ⊢ (if (0 : Nat) + 1 = 0 then
        memberShareIf peer client γE id (putgetPub (GF := putgetGF))
        else clientShareIf client γE id (putgetPub (GF := putgetGF))) by
      rw [if_neg (by decide)])
    iexact Hcs
  iempintro

end etcd_putget_dist
end EtcdGrove
end Perennial

end
