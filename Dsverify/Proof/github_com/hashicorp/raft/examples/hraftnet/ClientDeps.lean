/-
The hraft kit's clients' deposits (notes/dsv-hraft.md, S5f; coordinator-E's (e1), #48 7233410712): a client,
which does not know the drawn protocol, calls `API.Apply` with its operation's state `opSt`, which the
world's spec `apiSvcK` (`svcKE`) lets the server turn into the drawn protocol's deposit: the server, knowing
the draw, takes the drawn protocol's frontier invariant from the draw's invariant (`draw_frInv`) and
registers the operation there (`kit_register`, on its thread), and its success answer hands the client the
draw, that invariant, the reply's facts and the claim (`applyOk`), for `kit_claim`. An answer of no effect
gives the command's token back, so the client's next attempt deposits the registered operation.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ClientDefs
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ServerShare
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.CodecDefs
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.CodecLaws
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.WireLen

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

theorem encApplyArgs_length (v : ApplyArgsV) (h : v.data.length ≤ 1000) :
    (encApplyArgs v).length ≤ net.rpc.maxFrameN := by
  have hF := maxFrameN_eq
  have := fBytes_le v.data
  unfold encApplyArgs tagged rpctransport.encStr strct
  simp only [List.flatten_cons, List.flatten_nil, List.length_append, List.length_cons, List.length_nil,
    u64Le_length, List.append_nil]
  omega

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

/-- **A client's operation's state** (its datum `d`, input `i`, continuation `Φ`): not registered yet (its
id's reservation and the update), or registered in the drawn protocol (the draw, its frontier invariant,
the command's token, the claim). -/
def opSt (K : HK GF) (d : List w8) (i : HIn) (Φ : HOut → IProp GF) : IProp GF :=
  iprop((idTok K.g (idOf d) ∗ slotUpd (Gg := hG.goose_globalGS) (regR K.g.st) i Φ) ∨
    (∃ n k : Nat, chosen K.γc n ∗ frInv (K.γs n) (K.fcs n) ∗ opTok (K.γs n) d k ∗ kitTicket K.g d i Φ))

/-- **What a success answer of `Apply` gives the client** of the datum `d`: the draw, the drawn protocol's
frontier invariant, the reply's facts (`applyOut`), the claim. -/
def applyOk (K : HK GF) (d : List w8) (i : HIn) (Φ : HOut → IProp GF) (rep : List w8) : IProp GF :=
  iprop(∃ (n k : Nat) (r : ApplyReplyV), chosen K.γc n ∗ frInv (K.γs n) (K.fcs n) ∗
    ⌜rep = encApplyReply r⌝ ∗ applyOut (K.γs n) (K.fcs n) d k (applyRepOf r) ∗ kitTicket K.g d i Φ)

theorem apiSvc_Apply_eq (γ : GNames) (fc : FCtx GF) (bs : List w8) (Ψ : List w8 → GoString → IProp GF) :
    apiSvc γ fc go!"Apply" bs Ψ = iprop(∃ (v : ApplyArgsV) (n : Nat), ⌜bs = encApplyArgs v⌝ ∗
      opTok γ v.data n ∗ answers (fun rep => iprop(∃ r : ApplyReplyV, ⌜rep = encApplyReply r⌝ ∗
        applyOut γ fc v.data n (applyRepOf r))) Ψ) := by
  unfold apiSvc; rw [if_pos rfl]

theorem apiArgsOk_Apply (v : ApplyArgsV) : apiArgsOk go!"Apply" (encApplyArgs v) := by
  refine ⟨fun _ => ⟨v, rfl⟩, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

/-- The answers of the drawn protocol's `Apply` give `applyOk` (the claim rides along). -/
theorem answers_applyOk (K : HK GF) (n k : Nat) (v : ApplyArgsV) (i : HIn) (Φ : HOut → IProp GF) :
    chosen K.γc n ∗ frInv (K.γs n) (kitFC (K.γs n) K.g K.fr) ∗ kitTicket K.g v.data i Φ ⊢
      answers (fun rep => iprop(∃ r : ApplyReplyV, ⌜rep = encApplyReply r⌝ ∗
        applyOut (K.γs n) (kitFC (K.γs n) K.g K.fr) v.data k (applyRepOf r))) (okAns (applyOk K v.data i Φ)) := by
  iintro ⟨#Hc, #Hfi, Htk⟩
  unfold answers okAns
  isplitl [Htk]
  · iintro %rep ⟨%r, %Hrep, Hout⟩
    iright
    unfold applyOk
    iexists n, k, r
    unfold HK.fcs
    iframe Hc Hfi Hout Htk
    ipureintro; exact Hrep
  · iintro %msg %Hm
    ileft; ipureintro; exact Hm

/-- **A client's `Apply` deposit**: its operation's state and two later credits (for the server's
registration: the draw's invariant's later, the frontier's), the success answer `applyOk`. -/
theorem apply_dep (K : HK GF) (v : ApplyArgsV) (i : HIn) (Φ : HOut → IProp GF)
    (hd : datumOf i v.data) :
    drawInv K ∗ £ 1 ∗ £ 1 ∗ opSt K v.data i Φ ⊢
      apiSvcK K go!"Apply" (encApplyArgs v) (okAns (applyOk K v.data i Φ)) := by
  iintro ⟨#Hdi, Hlc1, Hlc2, Hst⟩
  unfold apiSvcK svcKE opSt HK.fcs
  isplitr
  · ipureintro; exact apiArgsOk_Apply v
  iintro %n #Hc
  icases Hst with (⟨Hid, Hupd⟩ | ⟨%n', %k, #Hc', #Hfi', Htok, Htk⟩)
  · imod draw_frInv K n $$ [$Hlc1 $Hdi $Hc] with #Hfi
    unfold HK.fcs
    imod kit_register (K.γs n) K.g K.fr v.data i Φ hd $$ [$Hfi $Hlc2 $Hid $Hupd] with ⟨%k, Htok, Htk⟩
    imodintro
    simp only [apiSvc_Apply_eq]
    iexists v, k
    isplitr
    · ipureintro; rfl
    iframe Htok
    iapply answers_applyOk K n k v i Φ $$ [$Hc $Hfi $Htk]
  · ihave %He := chosen_agree K.γc n n' $$ [Hc Hc']
    · iframe Hc Hc'
    subst He
    imodintro
    simp only [apiSvc_Apply_eq]
    iexists v, k
    isplitr
    · ipureintro; rfl
    iframe Htok
    iapply answers_applyOk K n k v i Φ $$ [$Hc $Hfi' $Htk]

theorem applyOut_noEffect (γ : GNames) (fc : FCtx GF) (d : List w8) (n : Nat) (rep : ApplyReply)
    (h : rep.Status' = W64 2) : applyOut γ fc d n rep ⊢ opTok γ d n := by
  unfold applyOut
  iintro (⟨-, H⟩ | %h3 | ⟨%h1, -⟩)
  · iexact H
  · exfalso; rw [h] at h3; exact absurd h3 (by decide)
  · exfalso; rw [h] at h1; exact absurd h1 (by decide)

/-- **A client claims its operation's output** from `Apply`'s done answer `r`: `Φ` of the output, whose
fields are the reply's (nothing found for a put). -/
theorem apply_done (K : HK GF) (d : List w8) (i : HIn) (Φ : HOut → IProp GF) (n k : Nat)
    (r : ApplyReplyV) (hs : r.status = W64 1) :
    £ 1 ∗ £ 1 ∗ frInv (K.γs n) (K.fcs n) ∗ applyOut (K.γs n) (K.fcs n) d k (applyRepOf r) ∗
      kitTicket K.g d i Φ ⊢
      |={⊤}=> ∃ out : HOut, Φ out ∗ ⌜out.1 = if i.1.1 then (false, []) else (r.found, r.v)⌝ := by
  unfold HK.fcs
  iintro ⟨Hlc1, Hlc2, #Hfi, Hout, Htk⟩
  unfold applyOut
  icases Hout with (⟨%h2, -⟩ | %h3 | ⟨-, %k', %e, %es, #He, %Hp, #Hcs, #Hlb⟩)
  · exfalso; simp only [applyRepOf] at h2; rw [hs] at h2; exact absurd h2 (by decide)
  · exfalso; simp only [applyRepOf] at h3; rw [hs] at h3; exact absurd h3 (by decide)
  obtain ⟨hk, hed, hlen, hres⟩ := Hp
  imod kit_claim (K.γs n) K.g K.fr d i Φ k' e es ⟨hk, hed, hlen⟩ $$ [$Hfi $Hlc1 $Hlc2 $Htk $He $Hcs $Hlb]
    with ⟨HΦ, %Hf⟩
  obtain ⟨hd, hl, hsh⟩ := Hf
  imodintro
  iexists firedOut i es
  iframe HΦ
  ipureintro
  rw [firedOut_respAt i es e hl (by rw [hed]; exact hd) hsh, hres]

/-! ## The client's system and its answers -/

/-- An input as the Go `In` value. -/
abbrev inS (i : HIn) : In := In.mk i.1.1 i.1.2.1 i.1.2.2

/-- The client's connections to the servers' APIs (`serverConns()`): one per server, at its address. -/
def sysConns (K : HK GF) (sl : GoSlice) : IProp GF :=
  iprop(∃ ps : List Loc, sl ↦*□ ps ∗ ⌜ps.length = 6⌝ ∗
    [∗list] k ↦ p ∈ ps, isConn p K.W (serverAddrs.getD k go!""))

instance sysConns_persistent (K : HK GF) (sl : GoSlice) : Persistent (sysConns K sl) := by
  unfold sysConns; infer_instance

/-- The clients' environment: the packages, the world's services, the draw's invariant, net/rpc's
codec. -/
def cliEnv (K : HK GF) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet ∗
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
    ⌜kitSS K⌝ ∗ drawInv K ∗ net.rpc.codecSet hraftCodec)

instance cliEnv_persistent (K : HK GF) : Persistent (cliEnv K) := by
  unfold cliEnv; infer_instance

/-- An operation's answer `o`: an output with `Φ` of it, or the unknown output. -/
def outRes (Φ : HOut → IProp GF) (o : Out) : IProp GF :=
  iprop((∃ out : HOut, ⌜o = Out.mk false out.1.1 out.1.2⌝ ∗ Φ out) ∨ ⌜o = Out.mk true false []⌝)

/-- A read outside the log (`Way` not `WayLog`) keeps its update (a read's `□ lin`) for `API.Read`. -/
def readUpd (K : HK GF) (i : HIn) (Φ : HOut → IProp GF) : IProp GF :=
  iprop(⌜i.1.1 = true ∨ i.1.2.1 = W64 0⌝ ∨ □ lin (Gg := hG.goose_globalGS) (regR K.g.st) i Φ)

instance readUpd_persistent (K : HK GF) (i : HIn) (Φ : HOut → IProp GF) :
    Persistent (readUpd K i Φ) := by
  unfold readUpd; infer_instance

/-- An operation's update keeps a read's for `API.Read`. -/
theorem slotUpd_readUpd (K : HK GF) (i : HIn) (Φ : HOut → IProp GF) :
    slotUpd (Gg := hG.goose_globalGS) (regR K.g.st) i Φ ⊢
      readUpd K i Φ ∗ slotUpd (Gg := hG.goose_globalGS) (regR K.g.st) i Φ := by
  by_cases h : i.1.1 = true ∨ i.1.2.1 = W64 0
  · iintro H
    iframe H
    unfold readUpd
    ileft; ipureintro; exact h
  · have hw : (regR (GF := GF) (Gg := hG.goose_globalGS) K.g.st).B.isWrite
        ((regR (GF := GF) (Gg := hG.goose_globalGS) K.g.st).mi i) = false := by
      have : i.1.1 = false := by cases hh : i.1.1 <;> simp_all
      exact this
    rw [slotUpd_read _ hw]
    iintro #H
    isplitr
    · unfold readUpd; iright; iexact H
    · iexact H

variable [rpcsem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [net.rpc.Assumptions] [net.Assumptions]

/-- **A read outside the log at a server's API** (S6; proved by `readCall_law_holds`, `ReadCall.lean`):
`p.Call("API.Read", &ReadArgs{Way}, reply, d)` at server `k + 1` with a read's update (and the draw's
invariant and two later credits, for the server's registration of the read, `kit_rdReg`) answers, when
`reply.Ok`, an output with `Φ` of it whose fields are the reply's. -/
abbrev readCall.law : Prop :=
  ∀ (K : HK GF) (p : Loc) (k : Nat) (i : HIn) (Φ : HOut → IProp GF) (args reply : Loc) (d : w64),
    i.1.1 = false → i.1.2.1 ≠ W64 0 → k < 6 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
        isConn p K.W (serverAddrs.getD k go!"") ∗ ⌜kitSS K⌝ ∗ net.rpc.codecSet hraftCodec ∗
        drawInv K ∗ £ 1 ∗ £ 1 ∗
        args ↦ service.ReadArgs.mk i.1.2.1 ∗ reply ↦ (zero_val service.ReadReply) ∗
        □ lin (Gg := hG.goose_globalGS) (regR K.g.st) i Φ }}
      (App (App (App (App (Val (p @!! go.GoType.PointerType rpctransport.Conn.ty @!! go!"Call"))
        (Val #(go!"API.Read"))) (Val #(ptrI service.ReadArgs.ty args)))
        (Val #(ptrI service.ReadReply.ty reply))) (Val #d))
    {{ (r : w64), RET #r; (⌜r = W64 0⌝ ∗ ∃ w : service.ReadReply, reply ↦ w ∗
          (⌜w.Ok' = true⌝ -∗ ∃ out : HOut, ⌜out.1 = (w.Found', w.V')⌝ ∗ Φ out)) ∨
        ⌜r = W64 1⌝ ∨ ⌜r = W64 2⌝ }}

end defs

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
