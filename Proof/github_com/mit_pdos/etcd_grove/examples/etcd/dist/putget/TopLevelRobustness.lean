/- Lean-first (no Rocq counterpart).

# `etcd/dist/putget`: the proof skeleton of `putget_safe` (`notes/putget-dist-plan.md`, section 5)

**`putget_safe`** (`theorem putget_safe : putget_safe.spec`): `putget_safe_of_boot` proves the statement from
one named hypothesis, `PutgetBoot`, which `putget_safe` discharges over the interim cross-machine axioms
(below). No `sorry`, no hypothesis left. The bridge from one WP per machine to `Robust []` is proved
(`Net.robust_of_distBootI`, `Net/Statement/DistBridgeExts.lean`, over any list of extensions with the net
extension), with the interpretations' initial-state conditions from the statement's `FsInit` premises
(`etcdNetExts_initP`).

`PutgetBoot`: at the statement's premises (and the addresses valid, from `DistDeploy`), the start update
from the two addresses unset to a share per machine, each machine's boot program safe from its share and
its whole start (`DistBootWpSL srvLevelK`: its files' and listeners' start resources, its main thread's
token, the logic's bounds with at least `srvLevelK` receipts, which the served member's `srvLevels` needs;
the bridge `robust_of_distBootIL` picks them). Over the interim cross-machine axioms
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

/-- **The two machines' boot WPs** (see the file header): at `putget_safe.spec`'s premises, the start
update from the deployment's addresses unset to a share per machine from which its boot program is safe.
The member's and the client's proofs (`member_boot`, `client_boot`). -/
def PutgetBoot : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel] [net.FieldAssumptions]
    (_Hctx : ∀ hG : HeapGS .hasLC putgetGF,
      ContextReadErrs (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    (_Hcec : ∀ hG : HeapGS .hasLC putgetGF,
      ContextErrsClient (GF := putgetGF) (hG := putgetHeapAt hG lctx))
    (peer client : GoString)
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry) (_Hbf : etcdstart.BootFacts id ctxs boot)
    (_Haf : authRecordsFit) (_Hbuq : apply.backendUnderQuota) (_Hrf : grpcRepliesFit)
    (_Hdbo : storage.diskOk)
    (_Hprem : ∀ n : Nat, n + 12 ≤ 2 ^ 40 → ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ etcdstart.premises (GF := putgetGF) (hG := putgetHeapAt hG lctx) name peer client n id ctxs
          boot)
    (σm σc : state) (_Hm : MemberFiles σm) (_Hc : ClientFiles σc)
    (_Hok : ∀ a ∈ addrs peer client, Net.addrOk a = true)
    (_HEnv : ∀ m ∈ system peer client σm σc, verifyEnvOff m.1)
    (_HEnvTok : ⊢ envVerifyOff (GF := putgetGF)),
    ∀ [GooseGlobalGS .hasLC putgetGF], srvLevelK ≤ receiptBound putgetGF →
      receiptBound putgetGF ≤ 2 ^ 28 - 1 →
      ⊢ ([∗list] a ∈ addrs peer client, Net.addrUnset a) ={⊤}=∗
        ∃ Ps : Nat → IProp putgetGF,
          ⌜∀ (i : Nat) (m : Expr × state), (system peer client σm σc)[i]? = some m →
            Net.DistBootWpSL srvLevelK (2 ^ 28 - 1) m.1 m.2 (Ps i)⌝ ∗
          [∗list] i ↦ _m ∈ system peer client σm σc, Ps i

/-- **`putget_safe` from the two machines' boot WPs** (see the file header), by the all-stable bridge
over `etcdNetExts` (`Net.robust_of_distBootI`), with each machine's `FsInit` from the statement. -/
theorem putget_safe_of_boot (HS : PutgetBoot) : putget_safe.spec := by
  intro _ _ _ _ _ _ _ _ Hctx Hcec peer client id ctxs boot Hbf Haf Hbuq Hrf Hdbo Hprem σm σc g
    Hm Hc Hd HEnv HEnvTok
  refine Net.robust_of_distBootIL (GF := putgetGF) (addrs peer client) (system peer client σm σc) g
    (2 ^ 28) (2 ^ 28 - 1) srvLevelK (by unfold srvLevelK srvRevokeK; omega) ?_
    (fun hlo hb => HS Hctx Hcec peer client id ctxs boot Hbf Haf Hbuq Hrf Hdbo Hprem σm σc Hm Hc
      Hd.2.1 HEnv HEnvTok hlo hb) Hd
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

end start

/-- **`putget_safe`** (see the file header): the start is proved (`putget_start`), the member's boot is
proved (`member_boot`, at `Pub = putgetPub`), the client's boot is proved (`client_boot`), the bridge is
proved (`putget_safe_of_boot`); the cross-machine steps are the interim axioms of
`notes/putget-dist-plan.md` §12 (the table `etcd_dist.etcdSvc`, `Serve_dist`, `Client_Put_dist`,
`Client_Get_dist`; the start law `etcdAddr_set` proved over grpc's `grpc_addr_set` since the S2 interface
switch). -/
theorem putget_safe : putget_safe.spec := by
  refine putget_safe_of_boot ?_
  intro _ _ _ _ _ _ _ _ _ _ _ Hctx Hcec peer client id ctxs boot Hbf Haf Hbuq Hrf Hdbo Hprem σm σc
    Hm Hc Hok HEnv HEnvTok G hlo hb
  have hpeer : Net.addrOk peer = true := Hok peer (by simp [addrs])
  have hcl : Net.addrOk client = true := Hok client (by simp [addrs])
  iintro Hs
  imod netProto_alloc ⊤ with ⟨%π, #Hreg⟩
  simp only [addrs, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
  icases Hs with ⟨Hp, Hcl, -⟩
  imod putget_start peer client id (putgetPub (GF := putgetGF)) $$ Hreg Hp Hcl with ⟨%γE, Hms, #Hcs⟩
  imodintro
  iexists (fun i => if i = 0 then memberShare client γE id (putgetPub (GF := putgetGF))
    else clientShare client γE id (putgetPub (GF := putgetGF)))
  isplitr
  · ipureintro
    intro i m hm
    match i, hm with
    | 0, hm =>
      simp only [system, List.getElem?_cons_zero, Option.some.injEq] at hm; subst hm
      exact member_boot Hctx HEnvTok peer client hpeer id ctxs boot Hbf Haf Hbuq Hrf Hdbo Hprem σm Hm γE
    | 1, hm => simp only [system, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hm; subst hm; exact client_boot Hctx Hcec client hcl σc γE id
    | k + 2, hm => simp [system] at hm
  simp only [system, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
  isplitl [Hms]
  · iapply (show memberShare client γE id (putgetPub (GF := putgetGF)) ⊢ (if (0 : Nat) = 0 then
        memberShare client γE id (putgetPub (GF := putgetGF)) else clientShare client γE id (putgetPub (GF := putgetGF))) by
      rw [if_pos rfl])
    iexact Hms
  isplitl []
  · iapply (show clientShare client γE id (putgetPub (GF := putgetGF)) ⊢ (if (0 : Nat) + 1 = 0 then
        memberShare client γE id (putgetPub (GF := putgetGF)) else clientShare client γE id (putgetPub (GF := putgetGF))) by
      rw [if_neg (by decide)])
    iexact Hcs
  iempintro

end etcd_putget_dist
end EtcdGrove
end Perennial

end
