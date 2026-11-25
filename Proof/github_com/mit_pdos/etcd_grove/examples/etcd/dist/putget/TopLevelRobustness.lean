/- Lean-first (no Rocq counterpart).

# `etcd/dist/putget`: the proof skeleton of `putget_safe` (`notes/putget-dist-plan.md`, section 5)

Not closed yet: `putget_safe_of_boot` proves `putget_safe.spec` from one named hypothesis, `PutgetBoot`, and
`putget_safe` (the plain name, `theorem putget_safe : putget_safe.spec`) is declared once it is discharged.
No axiom and no `sorry`. The bridge from one WP per machine to `Robust []` is proved
(`Net.robust_of_distBootI`, `Net/Statement/DistBridgeExts.lean`, over any list of extensions with the net
extension), with the interpretations' initial-state conditions from the statement's `FsInit` premises
(`etcdNetExts_initP`).

`PutgetBoot`: at the statement's premises (and the addresses valid, from `DistDeploy`), the start update
from the two addresses unset to a share per machine, each machine's boot program safe from its share and its
whole start (`DistBootWpSL srvLevelK`: its files' and listeners' start resources, its main thread's token,
the logic's bounds with at least `srvLevelK` receipts, which the served member's `srvLevels` needs; the
bridge `robust_of_distBootIL` picks them). Against phase 7 S2's draft names (`S2Draft`, PLACEHOLDER;
`notes/putget-dist-plan.md` sections 8 and 10), `putget_safe_of_s2` splits it:
* the start (`putget_start`, proved): the client address set to etcd's table at `γE`, the publication
  invariant, the member's and the client's shares (`Defs.lean`);
* the member's boot (`member_boot`, `AdequacyMember.lean`, proved): the in-process `Main.wp_proof`'s first half
  (`etcdstart.wp_StartServer1`, shared with it), `Serve` in S2's form publishing the view with `putgetPub`,
  from S2's names, the statement's `envVerifyOff` (`HEnvTok`) and the named hypotheses `MemberBootHyps`
  (`dataDirFresh`);
* the client's boot (`PutgetClientS2`, a hypothesis): the in-process second half over S2's `Invoke`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.TopLevelRobustness
public import Net.Statement.DistBridgeExts
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.S2Draft
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.AdequacyMember

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
The member's and the client's proofs; the client's is blocked on phase 7 S2. -/
def PutgetBoot : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
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
  intro _ _ _ _ _ _ _ Hctx Hcec peer client id ctxs boot Hbf Haf Hbuq Hrf Hdbo Hprem σm σc g
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

/-! ## Against phase 7 S2's draft names (PLACEHOLDER `S2Draft`, `S2Draft.lean`; the plan's section 8) -/

section s2
variable [GoGlobalContext]

/-- **S2's names hold** (what S2 proves, at every global ghost state and net protocol names). -/
def S2Holds : Prop :=
  ∀ [G : GooseGlobalGS .hasLC putgetGF] [π : NetProtoGS], Nonempty (S2Draft putgetGF)

/-- **The deployment's start, against S2's names** (the plan's §1.3 steps 1-4): the slot map, `γE`
allocated, the publication invariant, the client address set to `etcdSvc` (spending its `addrUnset`), the
member's and the client's shares. The peer address's `addrUnset` is unused (nothing listens there). -/
theorem putget_start [G : GooseGlobalGS .hasLC putgetGF] [π : NetProtoGS] (S : S2Draft putgetGF)
    (peer client : GoString) (mid : w64) (Pub : S.EnvView → IProp putgetGF) :
    ⊢ regCtx -∗ addrUnset peer -∗ addrUnset client ={⊤}=∗
      ∃ γE, memberShare S client γE mid Pub ∗ clientShare S client γE mid Pub := by
  iintro #Hreg - Hc
  imod S.depSlots_alloc with #Hd
  imod S.envPub_alloc with ⟨%γE, Htok⟩
  imod S.envPubInv_alloc γE Pub $$ Htok with ⟨#Hinv, Hhalf⟩
  imod (S.grpc_addr_set ⊤ client (S.etcdSvc γE mid)) $$ Hreg Hd Hc with #Ha
  ihave #Hk := S.kvRegsPub_of_addr client γE mid $$ Ha
  imodintro
  iexists γE
  unfold memberShare clientShare
  iframe Hhalf
  iframe #

/-- **The client machine's boot against S2's names** (the client half of `putget_safe`; the member's half is
`member_boot`, `AdequacyMember.lean`): under S2's names, the client's boot program safe from its share at every
`γE`, with what the member publishes (`putgetPub`: the client's putget invariant at the view's read names).
The in-process `Main.wp_proof`'s second half, reading the view from its first call's reply and then
`kvRegsPub_at`. -/
def ClientBootS2 [GoLocalContext] [go.Semantics] (client : GoString) (id : w64) (σc : state) : Prop :=
  ∀ [G : GooseGlobalGS .hasLC putgetGF] [π : NetProtoGS] (S : S2Draft putgetGF) (γE : GName),
    Net.DistBootWpSL srvLevelK (2 ^ 28 - 1) (bootClient client) σc
      (clientShare S client γE id (putgetPub S))

end s2

/-- **The client machine's boot against S2's names, at the statement's premises.** -/
def PutgetClientS2 : Prop :=
  ∀ [GoGlobalContext] [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [_root_.Perennial.errors.Assumptions]
    [_root_.Perennial.fmt.Assumptions] [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
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
    (σc : state) (_Hc : ClientFiles σc),
    ClientBootS2 client id σc

/-- **`putget_safe` from S2's names, the member's named hypotheses and the client's boot**: the start is
proved (`putget_start`), the member's boot is proved (`member_boot`, at `Pub = putgetPub`), the bridge is
proved (`putget_safe_of_boot`). The hypotheses: `S2Holds` (phase 7 S2, with `Serve`'s S2 form), the member's
start resources with no source yet (`MemberBootHyps`), and the client's boot (`PutgetClientS2`). -/
theorem putget_safe_of_s2 (HS2 : ∀ [GoGlobalContext], S2Holds)
    (HM : ∀ [GoGlobalContext] [GoLocalContext] [go.Semantics]
      [github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Assumptions], MemberBootHyps)
    (HC : PutgetClientS2) :
    putget_safe.spec := by
  refine putget_safe_of_boot ?_
  intro _ _ _ _ _ _ _ _ _ _ Hctx Hcec peer client id ctxs boot Hbf Haf Hbuq Hrf Hdbo Hprem σm σc
    Hm Hc Hok HEnv HEnvTok G hlo hb
  have HCb : ClientBootS2 client id σc := HC Hctx Hcec peer client id ctxs boot Hbf Haf Hbuq Hrf Hdbo
    Hprem σc Hc
  have hpeer : Net.addrOk peer = true := Hok peer (by simp [addrs])
  have hclient : Net.addrOk client = true := Hok client (by simp [addrs])
  iintro Hs
  imod netProto_alloc ⊤ with ⟨%π, #Hreg⟩
  obtain ⟨S⟩ := @HS2 _ G π
  simp only [addrs, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
  icases Hs with ⟨Hp, Hcl, -⟩
  imod putget_start S peer client id (putgetPub S) $$ Hreg Hp Hcl with ⟨%γE, Hms, Hcs⟩
  imodintro
  iexists (fun i => if i = 0 then memberShare S client γE id (putgetPub S)
    else clientShare S client γE id (putgetPub S))
  isplitr
  · ipureintro
    intro i m hm
    match i, hm with
    | 0, hm =>
      simp only [system, List.getElem?_cons_zero, Option.some.injEq] at hm; subst hm
      exact member_boot Hctx HM HEnvTok peer client hpeer hclient id ctxs boot Hbf Haf Hbuq Hrf Hdbo Hprem σm Hm S γE
    | 1, hm => simp only [system, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hm; subst hm; exact HCb S γE
    | k + 2, hm => simp [system] at hm
  simp only [system, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
  isplitl [Hms]
  · iapply (show memberShare S client γE id (putgetPub S) ⊢ (if (0 : Nat) = 0 then
        memberShare S client γE id (putgetPub S) else clientShare S client γE id (putgetPub S)) by
      rw [if_pos rfl])
    iexact Hms
  isplitl [Hcs]
  · iapply (show clientShare S client γE id (putgetPub S) ⊢ (if (0 : Nat) + 1 = 0 then
        memberShare S client γE id (putgetPub S) else clientShare S client γE id (putgetPub S)) by
      rw [if_neg (by decide)])
    iexact Hcs
  iempintro

end etcd_putget_dist
end EtcdGrove
end Perennial

end
