/-
The clients' calls (`NetRpc/Specs.lean`: `btlCall.spec`, `pingCall.spec`, `registerCall.spec`),
from Net's `Client.Call.spec` (a hypothesis: the callee's spec) and the codec's `CodecLaws`. As
dsv-craq's `Craq/Netrpc/Defs.lean` (`wp_Call_tag`) and its clients: the method's answer
`Φ rep []`, which the decoding obligation has in hand, pins the reply's bytes (`btlReplyBytes`,
`pingReplyBytes`, an `encRegisterReply`), whence the reply's type tag (`tagOk`) the decoding lemmas
ask for.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.NetRpc.Specs
public import Net.Spec.net.rpc.Client__Call

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open github_com.imdea_software.swiftpaxos_epaxos.netrpcw

namespace github_com.imdea_software.swiftpaxos_epaxos

/-! ## Type tags -/

theorem getU64_enc (x : w64) (rest : List w8) : getU64 (u64Le x ++ rest) = some (x, rest) := by
  unfold getU64
  rw [ite_eq_left (by simp [u64Le_length])]
  have h8 := u64Le_length x
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append,
    u64Le_to_word]

theorem getTag_encStr (s : GoString) (rest : List w8) (hs : s.length < 2 ^ 64) :
    getTag (encStr s ++ rest) = some (s, rest) := by
  unfold getTag encStr
  rw [List.append_assoc, getU64_enc]
  have hn : uint.nat (W64 s.length) = s.length := by
    show (BitVec.ofNat 64 s.length).toNat = s.length
    simp only [BitVec.toNat_ofNat]; omega
  simp only [hn, List.length_append, Nat.le_add_right, ite_true, List.take_left', List.drop_left']

theorem tagOk_tagged (t : GoString) (body : List w8) (ht : t.length < 2 ^ 64) :
    tagOk t (tagged t body) := by
  intro t' rest h
  unfold tagged at h
  rw [getTag_encStr t body ht] at h
  cases h; rfl

theorem tagOk_btlReply : tagOk tBeTheLeaderReply btlReplyBytes :=
  tagOk_tagged _ _ (by unfold tBeTheLeaderReply; decide)

theorem tagOk_pingReply : tagOk tPingReply pingReplyBytes :=
  tagOk_tagged _ _ (by unfold tPingReply; decide)

theorem tagOk_registerReply (id : w64) (nl : List GoString) (r il : Bool) :
    tagOk tRegisterReply (encRegisterReply id nl r il) :=
  tagOk_tagged _ _ (by unfold tRegisterReply; decide)

section calls
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [examples.epaxosnet.Assumptions] [master.Assumptions] [epaxos.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem replicaSvc_btl (args : List w8) (Φ : List w8 → GoString → IProp GF) :
    replicaSvc go!"BeTheLeader" args Φ = btlSpec args Φ := by
  unfold replicaSvc; rw [if_pos rfl]

theorem replicaSvc_ping (args : List w8) (Φ : List w8 → GoString → IProp GF) :
    replicaSvc go!"Ping" args Φ = pingSpec args Φ := by
  unfold replicaSvc; rw [if_neg (by decide), if_pos rfl]

theorem masterSvc_register (γ : EpNames) (args : List w8) (Φ : List w8 → GoString → IProp GF) :
    masterSvc γ go!"Register" args Φ = registerSpec γ args Φ := by
  unfold masterSvc; rw [if_pos rfl]

/-- Net's `Client.Call`, its outcomes merged: success with the decoded reply `Θ rep true`, or an
error (not `nil`) with the decoding resource `D` or a failed decoding. -/
theorem wp_Call_simple (Hcall : net.rpc.Client.Call.spec (GF := GF)) (c : Loc)
    (W : net.rpc.RpcWorld GF) (a sm svc M : GoString) (S : net.rpc.MethodSpec GF)
    (args reply : GoInterface) (Φ : List w8 → GoString → IProp GF) (D : IProp GF)
    (Θ : List w8 → Bool → IProp GF)
    (Hs : net.rpc.splitSM sm = some (svc, M) ∧ W.SS a svc = some S ∧ reply ≠ interface.nil) :
  {{ net.rpc.isClient c W a ∗ net.rpc.codecSet epCodec ∗
      epCodec.enc args (fun bs => iprop(S M bs Φ ∗ True)) ∗ D ∗
      □ (D -∗ ∀ rep, Φ rep [] -∗ epCodec.dec rep reply (Θ rep)) }}
    (App (App (App (Val (c @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Call"))
      (Val #sm)) (Val #args)) (Val #reply))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ ∃ rep, Θ rep true) ∨
      (⌜err ≠ interface.nil⌝ ∗ (D ∨ ∃ rep, Θ rep false)) }} := by
  iintro %Ψ ⟨#Hc, #Hcs, Henc, HD, #Hdec⟩ HΨ
  wp_apply (Hcall c W a sm svc M S args reply Φ iprop(True) D Θ epCodec) $$ [Henc HD]
  · isplitr
    · iexact Hc
    isplitr
    · ipureintro; exact Hs
    isplitr
    · iexact Hcs
    isplitl [Henc]
    · iexact Henc
    isplitl [HD]
    · iexact HD
    imodintro
    iexact Hdec
  iintro %err Hpost
  iapply HΨ
  icases Hpost with (⟨%Herr, -, Hok⟩ | ⟨%msg, ⟨%Hm, %Herr⟩, -, -, -, HD⟩ |
    ⟨⟨%Herr, -⟩, -, (⟨-, HD⟩ | ⟨-, HD⟩)⟩)
  · ileft
    isplitr
    · ipureintro; exact Herr
    iexact Hok
  · iright
    isplitr
    · ipureintro; rw [Herr]; exact net.rpc.serverErr_ne_nil msg
    ileft; iexact HD
  · iright
    isplitr
    · ipureintro; exact Herr
    iexact HD
  · iright
    isplitr
    · ipureintro; exact Herr
    ileft; iexact HD

theorem btlCall_holds (L : CodecLaws (GF := GF)) (Hcall : net.rpc.Client.Call.spec (GF := GF)) :
    btlCall.spec (GF := GF) := by
  intro W k cl la bl l0 nl0 hk hss
  iintro %Ψ ⟨#Hr, #Hc, Hla, Hbl⟩ HΨ
  unfold rpcReady
  icases Hr with ⟨-, #Hcs⟩
  wp_apply (wp_Call_simple Hcall cl W (rpcAddrOf k) go!"Replica.BeTheLeader" go!"Replica"
    go!"BeTheLeader" replicaSvc _ _ (fun rep msg => iprop(⌜msg = [] → rep = btlReplyBytes⌝))
    (bl ↦ replica.defs.BeTheLeaderReply.mk l0 nl0)
    (fun _ ok => if ok then bl ↦ replica.defs.BeTheLeaderReply.mk l0 nl0
      else iprop(∃ v : replica.defs.BeTheLeaderReply, bl ↦ v))
    ⟨by decide, hss, by intro h; cases h⟩) $$ [Hla Hbl]
  · isplitr
    · iexact Hc
    isplitr
    · iexact Hcs
    isplitl [Hla]
    · iapply L.enc_BtlArgs la (DFrac.own 1)
      iframe
      iintro _
      rw [replicaSvc_btl]
      unfold btlSpec errAns
      isplitl
      · isplitr
        · ipureintro; rfl
        isplit
        · ipureintro; intro _; rfl
        · iintro %_ %Hm; ipureintro; intro h; exact absurd h Hm
      · itrivial
    isplitl [Hbl]
    · iexact Hbl
    · imodintro
      iintro Hbl %rep %Hrep
      have hrep := Hrep rfl
      subst hrep
      iapply L.dec_BtlReply
      isplitr
      · ipureintro; exact tagOk_btlReply
      iframe
      iintro %ok Hok
      cases ok
      · simp only [Bool.false_eq_true, ite_false]
        iexact Hok
      · simp only [ite_true]
        icases Hok with ⟨%l, %nl, Hbl, %Heq⟩
        obtain ⟨rfl, rfl⟩ := Heq (W32 0) (W32 0) rfl
        try simp only [mergeI32, ite_true]
        iexact Hbl
  iintro %err Hpost
  iapply HΨ
  icases Hpost with (⟨%Herr, %rep, Hbl⟩ | ⟨%Herr, (Hbl | ⟨%rep, Hbl⟩)⟩)
  · ileft
    simp only [ite_true]
    iframe
    ipureintro; exact Herr
  · iright
    isplitr
    · ipureintro; exact Herr
    iexists _
    iexact Hbl
  · iright
    simp only [Bool.false_eq_true, ite_false]
    iframe
    ipureintro; exact Herr

theorem pingCall_holds (L : CodecLaws (GF := GF)) (Hcall : net.rpc.Client.Call.spec (GF := GF)) :
    pingCall.spec (GF := GF) := by
  intro W k cl la lr hk hss
  iintro %Ψ ⟨#Hr, #Hc, Hla, Hlr⟩ HΨ
  unfold rpcReady
  icases Hr with ⟨-, #Hcs⟩
  wp_apply (wp_Call_simple Hcall cl W (rpcAddrOf k) go!"Replica.Ping" go!"Replica"
    go!"Ping" replicaSvc _ _ (fun rep msg => iprop(⌜msg = [] → rep = pingReplyBytes⌝))
    (lr ↦ replica.defs.PingReply.mk) (fun _ _ => iprop(True))
    ⟨by decide, hss, by intro h; cases h⟩) $$ [Hla Hlr]
  · isplitr
    · iexact Hc
    isplitr
    · iexact Hcs
    isplitl [Hla]
    · iapply L.enc_PingArgs la (DFrac.own 1)
      iframe
      iintro _
      rw [replicaSvc_ping]
      unfold pingSpec errAns
      isplitl
      · isplitr
        · ipureintro; rfl
        isplit
        · ipureintro; intro _; rfl
        · iintro %_ %Hm; ipureintro; intro h; exact absurd h Hm
      · itrivial
    isplitl [Hlr]
    · iexact Hlr
    · imodintro
      iintro Hlr %rep %Hrep
      have hrep := Hrep rfl
      subst hrep
      iapply L.dec_PingReply
      isplitr
      · ipureintro; exact tagOk_pingReply
      iframe
      iintro %ok _
      itrivial
  iintro %err _
  iapply HΨ
  itrivial

theorem registerCall_holds (L : CodecLaws (GF := GF))
    (Hcall : net.rpc.Client.Call.spec (GF := GF)) : registerCall.spec (GF := GF) := by
  intro γ W k cl pa pr hk hss
  iintro %Ψ ⟨#Hr, #Hc, #Hpa, Hpr⟩ HΨ
  unfold rpcReady
  icases Hr with ⟨-, #Hcs⟩
  wp_apply (wp_Call_simple Hcall cl W masterAddr go!"Master.Register" go!"Master"
    go!"Register" (masterSvc γ) _ _
    (fun rep msg => iprop(⌜msg = []⌝ -∗ ∃ (id : w64) (nl : List GoString) (r il : Bool),
      ⌜rep = encRegisterReply id nl r il⌝ ∗ regReplyOk γ k id nl r))
    (pr ↦ replica.defs.RegisterReply.mk (W64 0) slice.nil false false)
    (fun _ ok => if ok then iprop(∃ (id : w64) (sl : GoSlice) (nl : List GoString) (r il : Bool),
        pr ↦ replica.defs.RegisterReply.mk id sl r il ∗ sl ↦* nl ∗ regReplyOk γ k id nl r)
      else iprop(∃ v : replica.defs.RegisterReply, pr ↦ v))
    ⟨by decide, hss, by intro h; cases h⟩) $$ [Hpr]
  · isplitr
    · iexact Hc
    isplitr
    · iexact Hcs
    isplitr [Hpr]
    · iapply L.enc_RegisterArgs pa DFrac.discard
      isplitr
      · iexact Hpa
      iintro _
      rw [masterSvc_register]
      unfold registerSpec errAns
      isplitl
      · iexists k
        isplitr
        · ipureintro; exact ⟨hk, rfl⟩
        isplit
        · iintro %id %nl %ready %il #Hok _
          iexists id, nl, ready, il
          isplitr
          · ipureintro; rfl
          iexact Hok
        · iintro %_ %Hm %Heq
          exact absurd Heq Hm
      · itrivial
    isplitl [Hpr]
    · iexact Hpr
    · imodintro
      iintro Hpr %rep HΦ
      ispecialize HΦ $$ %rfl
      icases HΦ with ⟨%id', %nl', %r', %il', %Hrep, #Hok⟩
      subst Hrep
      iapply L.dec_RegisterReply
      isplitr
      · ipureintro; exact tagOk_registerReply id' nl' r' il'
      iframe
      iintro %ok Hres
      cases ok
      · simp only [Bool.false_eq_true, ite_false]
        iexact Hres
      · simp only [ite_true]
        icases Hres with ⟨%id, %sl, %nl, %r, %il, Hpr, Hsl, %Heq⟩
        obtain ⟨rfl, rfl, rfl, rfl⟩ := Heq id' nl' r' il' rfl
        iexists id, sl, nl, r, il
        iframe
        iexact Hok
  iintro %err Hpost
  iapply HΨ
  icases Hpost with (⟨%Herr, %rep, Hpr⟩ | ⟨%Herr, (Hpr | ⟨%rep, Hpr⟩)⟩)
  · ileft
    simp only [ite_true]
    isplitr
    · ipureintro; exact Herr
    iexact Hpr
  · iright
    isplitr
    · ipureintro; exact Herr
    iexists _
    iexact Hpr
  · iright
    simp only [Bool.false_eq_true, ite_false]
    iframe
    ipureintro; exact Herr

end calls

end github_com.imdea_software.swiftpaxos_epaxos

end Perennial
