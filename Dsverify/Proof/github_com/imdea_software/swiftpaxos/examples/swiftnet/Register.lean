/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/Register.lean (lab master
915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md), onto `RpcHttpHyp`'s `DialHTTP`, `Net/`'s
client and the generated codec's per-type laws (`CodecLaws`, as `master.wp_call_btl`).

kit.go's `register(ip, port, maddr)`: runReplica's registration with the master, retried (a
new client after a failed call), until the master's `Register` answers `Ready`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ServersSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.NetRpc.CodecSrvProof
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.RpcHttpHyps
public import Net.Spec.net.rpc.Client__Call
public import Net.Spec.net.rpc.Client__Close
public import Perennial.Proof.time

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [examples.swiftnet.Assumptions]
variable [C : net.rpc.RpcCodec netDistGF] [KitLike C]
variable [net.rpc.Assumptions] [log.Assumptions] [net.http.Assumptions] [RpcHttpAddr netDistGF]
  [H : RpcHttpHyp netDistGF]

set_option goose.wp.extras true

/-- A tagged encoding's type tag is its own. -/
theorem reg_tagOk (t body : List w8) (ht : t.length < 2 ^ 64) :
    tagOk t (netrpcw.tagged t body) := by
  intro t' rest h
  rw [getTag_tagged t body ht] at h
  cases h; rfl

/-- `c.Call("Master.Register", args, &reply)` with the zero reply: no error and the reply's
fields (with, if ready, the membership's configuration fact and the replica's place in it), or
an error. -/
theorem wp_call_register (L : CodecLaws (GF := netDistGF))
    (wp_Call : net.rpc.Client.Call.spec (GF := netDistGF) (hG := hG)) (c : Loc)
    (W : net.rpc.RpcWorld netDistGF) (γc γm : GName) (cf : Conf) (ip : GoString) (port : w64)
    (k : Nat) (hk : replicaAddrs[k]? = some (sp.addrPort ip port)) (hkc : k < cf.n)
    (pa rp : Loc) :
    {{ net.rpc.codecSet net.rpc.RpcCodec.spec ∗
        net.rpc.isClient c W masterAddr ∗
        ⌜W.SS masterAddr go!"Master" = some (withErr (sp.masterSpec γc γm))⌝ ∗
        confIs γc cf ∗ pa ↦□ replica.defs.RegisterArgs.mk ip port ∗
        rp ↦ replica.defs.RegisterReply.mk (W64 0) slice.nil false false }}
      (App (App (App (Val (c @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Call"))
        (Val #(go!"Master.Register")))
        (Val #(interface.mkOk (go.GoType.PointerType replica.defs.RegisterArgs.ty) #pa)))
        (Val #(interface.mkOk (go.GoType.PointerType replica.defs.RegisterReply.ty) #rp)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ (id : w64) (sl : GoSlice) (nl : List GoString) (r il : Bool),
          rp ↦ replica.defs.RegisterReply.mk id sl r il ∗ sl ↦* nl ∗
          (if r then ∃ fr, sp.cfg γc γm nl.length fr nl ∗
            ⌜nl[id.toNat]? = some (sp.addrPort ip port)⌝ else True)) ∨
        ⌜err ≠ interface.nil⌝ }} := by
  wp_start_folded as ⟨#Hcs, #Hc, %HSS, #Hcc, #Hpa, Hrp⟩
  let Φr : List w8 → GoString → IProp netDistGF := fun rep _ =>
    iprop(∃ (id : w64) (nodes : List GoString) (ready isL : Bool),
      ⌜rep = (sp.KitVal.registerReply id nodes ready isL).encode⌝ ∗
      (if ready then iprop(∃ fr, sp.cfg γc γm nodes.length fr nodes ∗
          ⌜nodes[id.toNat]? = some (sp.addrPort ip port)⌝) else iprop(True)))
  let rv := interface.mkOk (go.GoType.PointerType replica.defs.RegisterReply.ty) #rp
  let Θ : List w8 → Bool → IProp netDistGF := fun rep ok =>
    if ok then iprop(∃ (id : w64) (sl : GoSlice) (nl : List GoString) (r il : Bool),
        rp ↦ replica.defs.RegisterReply.mk id sl r il ∗ sl ↦* nl ∗
        ⌜∀ id' nl' r' il', rep = netrpcw.encRegisterReply id' nl' r' il' →
          id = id' ∧ nl = nl' ∧ r = r' ∧ il = il'⌝)
      else iprop(∃ v : replica.defs.RegisterReply, rp ↦ v)
  wp_apply wp_Call c W masterAddr go!"Master.Register" go!"Master" go!"Register"
    (withErr (sp.masterSpec γc γm)) _ rv (fun rep msg => iprop(⌜msg ≠ []⌝ ∨ Φr rep msg))
    iprop(True)
    (rp ↦ replica.defs.RegisterReply.mk (W64 0) slice.nil false false)
    (fun rep ok => iprop(Φr rep [] ∗ Θ rep ok))
    $$ [$Hc Hrp] as %err Hres
  · ihave %Hpan := typedPointsto_not_null _ _ _ $$ Hpa
    ihave %Hrn := typedPointsto_not_null _ _ _ $$ Hrp
    iframe Hcs
    isplitr
    · ipureintro; exact ⟨by decide, HSS, by simp [rv, interface.mkOk]⟩
    isplitr
    · simp only [net.rpc.RpcCodec.spec]
      iapply enc_sw C
      iapply L.enc_RegisterArgs pa DFrac.discard ip port
      isplitr
      · iexact Hpa
      iintro -
      isplitl
      · unfold withErr
        isplit
        rotate_left
        · iintro %msg %Hmsg
          ileft; ipureintro; exact Hmsg
        iapply (sp.masterSpec_register (γc := γc) (γm := γm) _ _).2
        iexists ip, port, cf, k
        isplitr
        · ipureintro; exact ⟨rfl, hk, hkc⟩
        isplitr
        · iexact Hcc
        iintro %id %nodes %ready %isL Hif
        iright
        iexists id, nodes, ready, isL
        iframe Hif
        ipureintro; rfl
      itrivial
    iframe Hrp
    imodintro
    iintro Hrp %rep HΦr
    icases HΦr with (%Hne | HΦr)
    · exfalso; exact Hne rfl
    simp only [net.rpc.RpcCodec.spec]
    iapply dec_sw C
    icases HΦr with ⟨%id, %nodes, %ready, %isL, %Hrep, Hif⟩
    iapply L.dec_RegisterReply
    isplitr
    · ipureintro; rw [Hrep]; exact reg_tagOk _ _ (by decide)
    iframe Hrp
    iintro %ok Hok
    isplitl [Hif]
    · iexists id, nodes, ready, isL; iframe Hif; ipureintro; exact Hrep
    iexact Hok
  iapply HΦ
  icases Hres with (⟨%He, -, %rep, ⟨%rid, %rns, %rrd, %ril, %Hrep, Hif⟩, Hth⟩ |
    ⟨%msg, %Hm, -⟩ | ⟨%Hne, -⟩)
  · ileft
    isplitr
    · ipureintro; exact He
    simp only [Θ, ite_true]
    icases Hth with ⟨%id1, %sl1, %nl1, %r1, %il1, Hp', Hsl, %Hy⟩
    obtain ⟨rfl, rfl, rfl, rfl⟩ := Hy rid rns rrd ril (by rw [Hrep]; rfl)
    iexists id1, sl1, nl1, r1, il1
    iframe Hp' Hsl Hif
  · iright; ipureintro; rw [Hm.2]; exact net.rpc.serverErr_ne_nil msg
  · iright; ipureintro; exact Hne.1

theorem register.wp_proof (L : CodecLaws (GF := netDistGF))
    (wp_Call : net.rpc.Client.Call.spec (GF := netDistGF) (hG := hG))
    (wp_Close : net.rpc.Client.Close.spec (GF := netDistGF) (hG := hG)) :
    register.spec (hG := hG) (sem := sem) := by
  intro γ ip port k c hk hkc
  wp_start as ⟨#Hc, %HW, #Ha, #Hcs, #Hko⟩
  have hS : γ.W.SS masterAddr go!"Master" = some (withErr (sp.masterSpec γ.conf γ.mem)) := by
    rw [HW]; unfold services; rw [if_pos ⟨by decide, rfl⟩]
  ihave #Hcc := (conf.is_confIs γ c).1 $$ Hc
  wp_auto
  ipersist «$r0»
  ipersist args
  ipersist maddr
  wp_for
  wp_apply DialHTTP_tcp γ.W masterAddr $$ [$Ha] as %mc %err Hd
  icases Hd with (⟨%Herr, #Hcl⟩ | ⟨%Herr, -⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl Herr
    | ok i =>
      wp_auto
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
  subst Herr
  wp_auto
  wp_for
  have hz : (zero_val replica.defs.RegisterReply) =
      replica.defs.RegisterReply.mk (W64 0) slice.nil false false := by
    simp [zero_val, ZeroVal.zeroValDef]
  rw [hz]
  wp_apply wp_call_register (C := kitCodec) L wp_Call mc γ.W γ.conf γ.mem c ip port k hk hkc «$r0_ptr» reply_ptr
    $$ [$reply] as %e Hres
  · iframe Hcs Hcl Hcc «$r0»
    ipureintro; exact hS
  icases Hres with (⟨%He, %id, %sl, %nl, %r, %il, Hrep, Hsl, Hif⟩ | %He)
  rotate_left
  · rcases e with ei | _
    · wp_auto
      wp_for_post
      wp_apply wp_Close mc γ.W masterAddr $$ [$Hcl] as %e2 -
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
    · exact absurd rfl He
  subst He
  wp_auto
  cases r
  · wp_auto
    wp_apply time.wp_Sleep
    wp_for_post
    iframe
  · simp only [↓reduceIte]
    icases Hif with ⟨%fr, #Hcfg, %Hid⟩
    wp_auto
    wp_apply wp_Close mc γ.W masterAddr $$ [$Hcl] as %e2 -
    wp_for_post
    wp_for_post
    iapply HΦ
    iframe Hsl Hcfg
    ipureintro; exact Hid

end proof

end Perennial.github_com.imdea_software.swiftpaxos
