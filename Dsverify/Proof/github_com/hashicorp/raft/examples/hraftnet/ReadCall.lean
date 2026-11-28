/-
The hraft kit's clients' reads outside the log (notes/dsv-hraft.md, S6): a client calls `API.Read` with its
read's persistent update `□ lin`, which the world's spec `apiSvcK` lets the server turn into the drawn
protocol's deposit: the server, knowing the draw, takes the drawn protocol's frontier invariant
(`draw_frInv`) and registers the read in the frontier's read escrow (`kit_rdReg`, on its thread, after the
client's call began), which gives the snapshot `Barrier` needs and the claim `rdClaim` (`kit_rdClaim`): the
deposit `read_dep`. `readCall_law_holds` proves `readCall.law` (`ClientDeps.lean`, `Sys.try`'s read) from
`Conn.Call.spec` and the deposit.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ClientDeps
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.KitRead
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.CodecApi
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn__Call

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto
open rpctransport service

attribute [local instance] GooseGlobalGS.gooseInvGS

section pure
variable [GooseExts]

theorem encReadArgs_length (v : ReadArgsV) : (encReadArgs v).length ≤ net.rpc.maxFrameN := by
  have hF := maxFrameN_eq
  have := fU64_le v.way
  unfold encReadArgs tagged rpctransport.encStr strct
  simp only [List.flatten_cons, List.flatten_nil, List.length_append, List.length_cons, List.length_nil,
    u64Le_length, List.append_nil]
  omega

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

/-- **What a success answer of `Read` gives the client**: the reply's encoding, and with `Ok`, `Φ` of an
output whose fields are the reply's. -/
def readOk (Φ : HOut → IProp GF) (rep : List w8) : IProp GF :=
  iprop(∃ r : ReadReplyV, ⌜rep = encReadReply r⌝ ∗
    (⌜r.ok = true⌝ -∗ ∃ out : HOut, ⌜out.1 = (r.found, r.v)⌝ ∗ Φ out))

theorem apiArgsOk_Read (v : ReadArgsV) : apiArgsOk go!"Read" (encReadArgs v) :=
  ⟨fun h => absurd h (by decide), fun _ => ⟨v, rfl⟩, fun h => absurd h (by decide)⟩

theorem apiSvc_Read_eq (γ : GNames) (fc : FCtx GF) (bs : List w8) (Ψ : List w8 → GoString → IProp GF) :
    apiSvc γ fc go!"Read" bs Ψ = iprop(∃ (v : ReadArgsV) (n0 : Nat) (sc : Snap)
        (Ψr : Bool → List w8 → IProp GF),
      ⌜bs = encReadArgs v⌝ ∗ histLb γ sc ∗ ⌜n0 ≤ sc.maxDur⌝ ∗ rdClaim γ fc n0 Ψr ∗
      answers (fun rep => iprop(∃ r : ReadReplyV, ⌜rep = encReadReply r⌝ ∗
        (⌜r.ok = true⌝ -∗ Ψr r.found r.v))) Ψ) := by
  unfold apiSvc; rw [if_neg (by decide), if_pos rfl]

/-- **A client's `Read` deposit**: its read's update (persistent) and two later credits (the server's
registration: the draw's invariant's later, the frontier's), the success answer `readOk`. -/
theorem read_dep (K : HK GF) (v : ReadArgsV) (i : HIn) (Φ : HOut → IProp GF) (hw : i.1.1 = false) :
    drawInv K ∗ £ 1 ∗ £ 1 ∗ □ lin (Gg := hG.goose_globalGS) (regR K.g.st) i Φ ⊢
      apiSvcK K go!"Read" (encReadArgs v) (okAns (readOk Φ)) := by
  iintro ⟨#Hdi, Hlc1, Hlc2, #Hlin⟩
  unfold apiSvcK svcKE
  isplitr
  · ipureintro; exact apiArgsOk_Read v
  iintro %n #Hc
  imod draw_frInv K n $$ [$Hlc1 $Hdi $Hc] with #Hfi
  unfold HK.fcs
  imod kit_rdReg (K.γs n) K.g K.fr i Φ hw $$ [$Hfi $Hlc2 $Hlin] with ⟨%es0, %sc, #Hsc, %hsc, #Hc0, Htk⟩
  imodintro
  simp only [apiSvc_Read_eq]
  iexists v, es0.length, sc, (fun f w => iprop(∃ out : HOut, ⌜out.1 = (f, w)⌝ ∗ Φ out))
  isplitr
  · ipureintro; rfl
  iframe Hsc
  isplitr
  · ipureintro; exact hsc.1
  isplitl [Htk]
  · unfold rdClaim
    iintro %es %k0 %k %h #Hnc #Hlb Hl1 Hl2
    imod kit_rdClaim (K.γs n) K.g K.fr i Φ es0 es k0 k hsc.2 h $$ [$Hfi $Hl1 $Hl2 $Hc0 $Htk $Hnc $Hlb]
      with ⟨%out, %ho, HΦ⟩
    imodintro
    iexists out
    iframe HΦ
    ipureintro; exact ho
  · unfold answers okAns
    isplitl
    · iintro %rep ⟨%r, %Hrep, Hok⟩
      iright
      unfold readOk
      iexists r
      iframe Hok
      ipureintro; exact Hrep
    · iintro %msg %Hm
      ileft; ipureintro; exact Hm

variable [rpcsem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [net.rpc.Assumptions] [net.Assumptions]
variable [hsem : github_com.hashicorp.raft.examples.hraftnet.Assumptions]

/-- **`readCall.law`** from `Conn.Call.spec`: the deposit `read_dep`, the reply decoded. -/
theorem readCall_law_holds (wp_Call : rpctransport.Conn.Call.spec (GF := GF) (hG := hG)) :
    readCall.law (GF := GF) (hG := hG) := by
  intro K p k i Φ args reply d hw hway hk
  iintro %Θ ⟨#Hpkr, #Hc, %Hss, #Hcod, #Hdi, Hlc1, Hlc2, Hargs, Hrep, #Hlin⟩ HΘ
  wp_apply (wp_Call p K.W (serverAddrs.getD k go!"") go!"API.Read" go!"API" go!"Read"
      (apiSvcK K) (ptrI service.ReadArgs.ty args) (ptrI service.ReadReply.ty reply)
      (okAns (readOk Φ)) iprop(True)
      iprop(reply ↦ (Perennial.zero_val service.ReadReply))
      (fun _ _ => iprop(∃ (w : service.ReadReply) (r : ReadReplyV), reply ↦ w ∗
        ⌜w.Ok' = r.ok ∧ w.Found' = r.found ∧ w.V' = r.v⌝ ∗
        (⌜r.ok = true⌝ -∗ ∃ out : HOut, ⌜out.1 = (r.found, r.v)⌝ ∗ Φ out)))
      hraftCodec d iprop(args ↦ service.ReadArgs.mk i.1.2.1 ∗ £ 1 ∗ £ 1))
    $$ [$Hc $Hcod Hargs Hlc1 Hlc2 Hrep] as %r Hr
  · isplitr
    · ipureintro
      refine ⟨by decide, ?_, by simp [ptrI, interface.mkOk]⟩
      rw [show k = k + 1 - 1 by omega, Hss (k + 1) go!"API" (by omega) (by omega)]
      simp [rpctransport.svcName]
    isplitr
    · ipureintro; decide
    isplitl [Hargs Hlc1 Hlc2]
    · iframe Hargs Hlc1 Hlc2
    isplitr
    · iintro ⟨Hargs, Hl1, Hl2⟩
      iapply (enc_ReadArgs args (DFrac.own 1) (service.ReadArgs.mk i.1.2.1) ⟨i.1.2.1⟩)
      iframe Hargs
      isplitr
      · unfold readArgsOwn; ipureintro; rfl
      iintro - -
      isplitr
      · ipureintro; exact encReadArgs_length ⟨i.1.2.1⟩
      isplitl
      · iapply read_dep K ⟨i.1.2.1⟩ i Φ hw $$ [$Hdi $Hl1 $Hl2 $Hlin]
      itrivial
    iframe Hrep
    imodintro
    iintro HD %rep Hrep
    unfold okAns readOk
    icases Hrep with (%Hne | ⟨%r, %Hrep, Hok⟩)
    · exfalso; exact Hne rfl
    subst Hrep
    iapply (dec_ReadReply _ r)
    iframe HD
    iintro %w Hw Hown
    unfold readReplyOwn
    icases Hown with %Hown
    iexists w, r
    iframe Hw Hok
    ipureintro; exact Hown
  icases Hr with (⟨%Hr0, -, %rep, %w, %rv, Hw, %Hown, Hok⟩ | ⟨%Hr1, -, -⟩ | %Hr2)
  · iapply HΘ
    ileft
    isplitr
    · ipureintro; exact Hr0
    iexists w
    iframe Hw
    iintro %hok
    obtain ⟨h1, h2, h3⟩ := Hown
    ihave ⟨%out, %ho, HΦ⟩ := Hok $$ %(h1 ▸ hok)
    iexists out
    iframe HΦ
    ipureintro; rw [ho, h2, h3]
  · iapply HΘ
    iright; ileft; ipureintro; exact Hr1
  · iapply HΘ
    iright; iright; ipureintro; exact Hr2

end defs

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
