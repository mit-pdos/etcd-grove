/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ClientConnect.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`s.connect(c)` (`kit.go`): client node `c`'s SwiftPaxos client (id `c + 1`), as main.go's
`runSingleClient` makes one: `client.NewClientLog` for the master at `addrs[NC+1]`
(`10.77.0.17:7001`), the id set, `NewBufferClient`, `Connect`, and on success
`swift.NewClient(b, N)` with the configuration's `N` (the connected membership's size:
`sp.cfg_conf`), the node's claimed ghost and the registrations (stage 2); on failure
`Disconnect`. Every callee is used through its frozen spec (hypotheses), `host`/`port` of the
master's address through their instances (hypotheses: the adapter's `host`/`port` specs).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientOp
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has netShaExts_hasSha256

namespace cnode

section laws
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

/-- A connected client's view of the configuration (an unfold of `client.connected`). -/
theorem connected_cfg (b : Loc) (γ : sp.Names) (γc γm : GName) (cid : w32) (N : Nat) :
    client.connected b γ γc γm cid N ⊢
      client.connected b γ γc γm cid N ∗ ∃ fr l, sp.cfg γc γm N fr l := by
  refine (client.connected_unfold b γ γc γm cid N).1.trans ?_
  iintro ⟨%bv, %v, %l, %fr, %srvs, %rds, %wrs, Hb, Hv, Hlg, #Hcfg, H⟩
  isplitl [Hb Hv Hlg H]
  · iapply (client.connected_unfold b γ γc γm cid N).2
    iexists bv, v, l, fr, srvs, rds, wrs
    iframe Hb Hv Hlg Hcfg H
  · iexists fr, l
    iexact Hcfg

/-- A ready client's buffer client is not nil (an unfold of `client.ready`). -/
theorem ready_ne_null (b : Loc) (γ : sp.Names) (γc γm γl : GName) (cid : w32) (s : Nat) :
    client.ready b γ γc γm γl cid s ⊢ client.ready b γ γc γm γl cid s ∗ ⌜b ≠ null⌝ := by
  have h : client.ready b γ γc γm γl cid s ⊢ ⌜b ≠ null⌝ := by
    refine (client.ready_unfold b γ γc γm γl cid s).1.trans ?_
    iintro ⟨%bv, %cl, %N, %γch, %γd, #Hb, -⟩
    iapply typedPointsto_not_null $$ Hb
  refine (BI.and_intro .rfl h).trans ?_
  iintro ⟨H, %Hb⟩
  iframe H
  ipureintro; exact Hb

end laws

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [C : net.rpc.RpcCodec netDistGF]

local notation "swiftnetPkg" => pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet

/-- `host(addrs[NC+1])`: the master's host (an instance of the adapter's `host` spec). -/
abbrev hostMaster.spec : Prop :=
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg }}
    (App (Val (@! examples.swiftnet.host)) (Val #(go!"10.77.0.17:7001")))
  {{ RET #(go!"10.77.0.17"); True }}

/-- `port(addrs[NC+1])`: the master's port (an instance of the adapter's `port` spec). -/
abbrev portMaster.spec : Prop :=
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg }}
    (App (Val (@! examples.swiftnet.port)) (Val #(go!"10.77.0.17:7001")))
  {{ RET #(W64 7001); True }}

end specs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [C : net.rpc.RpcCodec netDistGF]
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions] [client.Assumptions]
variable [examples.swiftnet.Assumptions] [swift.Assumptions]

set_option goose.wp.extras true

theorem digitChar_toNat (n : Nat) (h : n < 10) : (Nat.digitChar n).toNat = 48 + n := by
  match n, h with
  | 0, _ => rw [Nat.digitChar_eq_zero.2 rfl]; rfl
  | 1, _ => rw [Nat.digitChar_eq_one.2 rfl]; rfl
  | 2, _ => rw [Nat.digitChar_eq_two.2 rfl]; rfl
  | 3, _ => rw [Nat.digitChar_eq_three.2 rfl]; rfl
  | 4, _ => rw [Nat.digitChar_eq_four.2 rfl]; rfl
  | 5, _ => rw [Nat.digitChar_eq_five.2 rfl]; rfl
  | 6, _ => rw [Nat.digitChar_eq_six.2 rfl]; rfl
  | 7, _ => rw [Nat.digitChar_eq_seven.2 rfl]; rfl
  | 8, _ => rw [Nat.digitChar_eq_eight.2 rfl]; rfl
  | 9, _ => rw [Nat.digitChar_eq_nine.2 rfl]; rfl

theorem masterAddrPort : sp.addrPort go!"10.77.0.17" (W64 7001) = masterAddr := by
  simp [sp.addrPort, masterAddr, Nat.toDigits_of_base_le, Nat.toDigits_of_lt_base,
    digitChar_toNat]

theorem Sys.connect.wp_proof (γ : SwiftNames netDistGF) (c : Nat) (hc : c < 6)
    (wp_host : hostMaster.spec) (wp_port : portMaster.spec)
    (wp_NewClientLog : client.NewClientLog.spec)
    (wp_NewBufferClient : client.NewBufferClient.spec)
    (wp_Connect : client.BufferClient.Connect.specG)
    (wp_Disconnect : client.BufferClient.Disconnect.specG)
    (wp_NewClient : swift.NewClient.spec) :
    Sys.connect.spec γ c := fun s => by
  wp_start as ⟨#Hs, Hb, Hseq, #Hreg⟩
  iunfold isSysL at Hs
  icases Hs with ⟨%conf, %asl, #Haddrs, #Hasl, #Hconf, #Hconfis, #Hmu, #Henv, #Hgok⟩
  ihave %Hasl_len := ownSlice_len $$ Hasl
  have hb1 : 0 ≤ sint.Z (W64 6 + W64 1) ∧ sint.Z (W64 6 + W64 1) < sint.Z asl.len := by
    obtain ⟨h1, h2⟩ := Hasl_len
    have : addrs.length = 13 := rfl
    constructor <;> word
  have ha1 : addrs[(sint.Z (W64 6 + W64 1)).toNat]? = some go!"10.77.0.17:7001" := rfl
  wp_auto
  simp only [hb1, and_self, ↓reduceIte]
  wp_apply wp_load_slice_index asl (sint.Z (W64 6 + W64 1)) addrs _ _ hb1.1 $$ [] as -
  · iframe Hasl; ipureintro; exact ha1
  wp_apply wp_host
  wp_apply wp_port
  ihave %Hlgnn := typedPointsto_not_null $$ «$a6»
  imod (typedPointsto_dfractional _ _).dfractional_persist $$ «$a6» with #Hlg
  wp_apply wp_NewClientLog [] go!"10.77.0.17" (W64 7001) false «$a6_ptr» $$ [] as %cl ⟨%cid0, Hfresh⟩
  · iunfold dlog.quiet
    iframe Hlg
    ipureintro; exact Hlgnn
  have hcid : W32 (uint.Z (W64 (c : Int))) + W32 1 = cidOf c := by
    unfold cidOf; word
  rw [hcid]
  ihave ⟨%v, Hcl, Hback⟩ := client.fresh_setId cl cid0 (cidOf c) _ _ $$ Hfresh
  wp_auto
  ihave Hfresh := Hback $$ Hcl
  wp_apply wp_NewBufferClient cl (cidOf c) _ (W64 7001) (W64 8) $$ [Hfresh] as %b Hbuf
  · iframe Hfresh
    ipureintro; constructor <;> decide
  iunfold nodeEnv at Henv
  icases Henv with ⟨#Hmaster, #Hrpcs, %HSS, #HcodecSet, #HcodecOk, #Hprotos, #Hinv⟩
  wp_apply wp_Connect b (cidOf c) go!"10.77.0.17" (W64 7001) γ.W γ.sp γ.conf γ.mem γ.lin $$ [Hbuf]
    as %err Herr
  · iframe Hbuf Hmaster HcodecSet HcodecOk Hprotos Hinv
    ipureintro
    refine ⟨masterAddrPort, ?_⟩
    rw [HSS]; unfold services; simp [masterAddr]
  icases Herr with (⟨%Herr, %N, Hconn⟩ | ⟨%Herr, Hfailed⟩)
  · subst Herr
    wp_auto
    ihave ⟨Hconn, %fr, %l, #Hcfg⟩ := connected_cfg $$ Hconn
    iunfold swiftpaxos.conf.is at Hconfis
    ihave %HN := sp.cfg_conf (γc := γ.conf) (γm := γ.mem) N fr l conf $$ [Hcfg Hconfis]
    · iframe Hcfg; iexact Hconfis
    obtain ⟨HN, -⟩ := HN
    subst HN
    ihave Hc2 := Hconf
    iStructNamed Hc2
    wp_auto
    unfold confV
    wp_apply wp_NewClient b γ.sp γ.conf γ.mem γ.lin (cidOf c) conf.n $$ [Hconn Hseq] as %cl' Hready
    · rw [cidOf_pnode c hc]
      iframe
      iframe Hinv Hgok Hreg
    ihave ⟨Hready, %Hbnn⟩ := ready_ne_null $$ Hready
    iapply HΦ
    simp only [↓reduceIte]
    iexists b
    iframe
    ipureintro; exact Hbnn
  · obtain ⟨ei, rfl⟩ : ∃ ei, err = GoInterface.ok ei := by
      cases err with
      | nil => exact absurd rfl Herr
      | ok ei => exact ⟨ei, rfl⟩
    wp_auto
    wp_apply wp_Disconnect b $$ [Hfailed]
    · iframe
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe

end proof

end cnode

end Perennial.github_com.imdea_software.swiftpaxos
