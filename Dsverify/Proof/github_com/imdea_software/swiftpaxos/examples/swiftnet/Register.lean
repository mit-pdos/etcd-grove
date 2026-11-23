/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/Register.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
kit.go's `register(ip, port, maddr)`: runReplica's registration with the master, retried (a
new client after a failed call), until the master's `Register` answers `Ready`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ServersSpecs

-- PORT: lab imports dropped: Harness.Proof.net.rpc.Results

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

-- The codec of the linked results (decision D6, HUB-REQUEST 2, Proof/swiftnet/KitLike.lean):
-- `kitCodecC`, whose `kitCodecOk` holds (`kitCodecOkC_holds`).
attribute [local instance 2000] examples.swiftnet.kitCodecC

/-! ## The reply's encoding -/

namespace regEnc
open sp

theorem w64_nat_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : (W64 a : w64) = W64 b) : a = b := by
  have := congrArg BitVec.toNat h
  simp [W64] at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem flat_inj : ∀ (ns ns' : List GoString),
    (ns.map cBytes).flatten = (ns'.map cBytes).flatten →
    (ns.map cBytes).flatten.length < 2 ^ 64 → ns = ns'
  | [], [], _, _ => rfl
  | [], s' :: t', h, _ => by
    have := congrArg List.length h
    (simp [cBytes, cU64, u64Le_length] at this) <;> omega
  | s :: t, [], h, _ => by
    have := congrArg List.length h
    (simp [cBytes, cU64, u64Le_length] at this) <;> omega
  | s :: t, s' :: t', h, hb => by
    simp only [List.map_cons, List.flatten_cons, cBytes, cU64, List.append_assoc] at h hb
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp [u64Le_length])
    have hl2 := congrArg List.length h2
    simp only [List.length_append] at hl2 hb
    have hs : s.length = s'.length :=
      w64_nat_inj (by omega) (by omega) (u64Le_inj h1)
    obtain ⟨h3, h4⟩ := List.append_inj h2 hs
    rw [h3, flat_inj t t' h4 (by omega)]

theorem rr_suffix {i i' : w64} {ns ns' : List GoString} {r r' l l' : Bool}
    (h : (KitVal.registerReply i ns r l).encode = (KitVal.registerReply i' ns' r' l').encode) :
    r = r' ∧ l = l' := by
  have h2 := congrArg (fun x => x.reverse.take 2) h
  simp only [KitVal.encode, KitVal.tag, cBool, List.append_assoc, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.take_succ_cons, List.take_zero] at h2
  simp only [List.cons.injEq, and_true] at h2
  constructor
  · cases r <;> cases r' <;> simp_all <;> exact absurd h2.2 (by decide)
  · cases l <;> cases l' <;> simp_all <;> exact absurd h2.1 (by decide)

theorem rr_inj {i i' : w64} {ns ns' : List GoString} {r r' l l' : Bool}
    (hb : (ns.map cBytes).flatten.length < 2 ^ 64)
    (h : (KitVal.registerReply i ns r l).encode = (KitVal.registerReply i' ns' r' l').encode) :
    i = i' ∧ ns = ns' ∧ r = r' ∧ l = l' := by
  obtain ⟨rfl, rfl⟩ := rr_suffix h
  simp only [KitVal.encode, KitVal.tag, cList, cU64, List.append_assoc] at h
  obtain ⟨-, h⟩ := List.append_inj h (by simp [u64Le_length])
  obtain ⟨hi, h⟩ := List.append_inj h (by simp [u64Le_length])
  obtain ⟨-, h⟩ := List.append_inj h (by simp [u64Le_length])
  have h' := (List.append_inj' h rfl).1
  exact ⟨u64Le_inj hi, flat_inj ns ns' h' hb, rfl, rfl⟩

theorem flat_len_le : ∀ (ns : List GoString), (∀ a ∈ ns, a.length ≤ 15) →
    (ns.map cBytes).flatten.length ≤ 23 * ns.length
  | [], _ => by simp
  | a :: t, h => by
    have ha := h a (by simp)
    have ht := flat_len_le t (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, List.flatten_cons, List.length_append, cBytes, cU64,
      u64Le_length, List.length_cons] at ht ⊢
    omega

theorem replicaAddrs_len : ∀ a ∈ replicaAddrs, a.length ≤ 15 := by decide

theorem nodes_bound (ns : List GoString) (hn : ns.Nodup) (hs : ∀ a ∈ ns, a ∈ replicaAddrs) :
    (ns.map cBytes).flatten.length < 2 ^ 64 := by
  have h1 := flat_len_le ns (fun a ha => replicaAddrs_len a (hs a ha))
  have h2 : ns.length ≤ replicaAddrs.length := List.Nodup.length_le_of_subset hn hs
  have h3 : replicaAddrs.length = 5 := rfl
  omega

theorem merge_x0 (i : w64) (ns : List GoString) (r l : Bool) :
    KitVal.merge (.registerReply 0 [] false false) (.registerReply i ns r l) =
      .registerReply i ns r l := by
  simp only [KitVal.merge, Bool.false_or]
  have h1 : (if i = 0 then (0 : w64) else i) = i := by split <;> simp_all
  have h2 : (if ns = [] then ([] : List GoString) else ns) = ns := by split <;> simp_all
  rw [h1, h2]

end regEnc

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [SwiftNetPkgState netDistGF] [examples.swiftnet.Assumptions] [net.model.Assumptions]

set_option goose.wp.extras true

/-- What the master's answer to `Register` gives the caller. -/
def regPhi (γ : SwiftNames netDistGF) (ip : GoString) (port : w64) :
    List w8 → GoString → IProp netDistGF := fun rep _ =>
  iprop(∃ (id : w64) (nodes : List GoString) (ready isL : Bool),
    ⌜rep = (sp.KitVal.registerReply id nodes ready isL).encode⌝ ∗
    (if ready then iprop(∃ fr, sp.cfg γ.conf γ.mem nodes.length fr nodes ∗
        ⌜nodes[id.toNat]? = some (sp.addrPort ip port)⌝) else iprop(True)))

/-- The zero reply. -/
abbrev regX0 : sp.KitVal := .registerReply 0 [] false false

/-- What decoding the reply into `rp` gives. -/
def regTheta (rp : Loc) : List w8 → Bool → IProp netDistGF := fun rep _ =>
  iprop((∃ y : sp.KitVal, ⌜rep = y.encode ∧ y.tag = 2⌝ ∗
      kitValOwn (interface.mkOk (go.GoType.PointerType replica.defs.RegisterReply.ty) #rp)
        (DFrac.own 1) (sp.KitVal.merge regX0 y)) ∨
    ⌜∀ y : sp.KitVal, y.tag = 2 → sp.KitVal.wf y → rep ≠ y.encode⌝)

instance register_rpcAddr_persistent (W : net.rpc.RpcWorld netDistGF) (a : GoString) :
    Persistent (net.rpc.rpcAddr (GF := netDistGF) W a) := by
  unfold net.rpc.rpcAddr; infer_instance


theorem wp_register : register.spec (hG := hG) (sem := sem) := by
  intro γ ip port k c hk hkc
  wp_start as ⟨#Hc, %HW, #Ha, #Hcs, #Hko⟩
  wp_auto
  ipersist «$r0»
  ipersist args
  ipersist maddr
  wp_for
  wp_apply net.rpc.DialHTTP.wp γ.W masterAddr $$ [$Ha] as %mc %err Hd
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
  have hS : γ.W.SS masterAddr go!"Master" = some (sp.masterSpec γ.conf γ.mem) := by
    rw [HW]; unfold services; simp
  ihave %Hnn := typedPointsto_not_null $$ reply
  ihave %Hnn0 := typedPointsto_not_null $$ «$r0»
  ihave HD : kitValOwn (interface.mkOk (go.GoType.PointerType replica.defs.RegisterReply.ty)
      #reply_ptr) (DFrac.own 1) regX0 $$ [reply]
  · unfold kitValOwn structOwn
    iexists replica.defs.RegisterReply.ty, reply_ptr
    isplitr
    · ipureintro; exact ⟨rfl, Hnn⟩
    isplitr
    · ipureintro; rfl
    iexists slice.nil
    iframe reply
    iapply ownSlice_nil
  wp_apply net.rpc.Client.Call.wp mc γ.W masterAddr go!"Master.Register" go!"Master"
    go!"Register" (sp.masterSpec γ.conf γ.mem) _ _ (regPhi γ ip port) iprop(True)
    (kitValOwn (interface.mkOk (go.GoType.PointerType replica.defs.RegisterReply.ty)
      #reply_ptr) (DFrac.own 1) regX0) (regTheta reply_ptr) $$ [$Hcs $Hko $Hcl $HD]
    as %err Hres
  · isplitr
    · ipureintro; exact ⟨rfl, hS⟩
    isplitr
    · iapply enc_of examples.swiftnet.kitCodecC
      simp only [net.rpc.RpcCodec.enc]
      iexists DFrac.discard, sp.KitVal.registerArgs ip port
      isplitr
      · unfold kitValOwn structOwn
        iexists replica.defs.RegisterArgs.ty, «$r0_ptr»
        isplitr
        · ipureintro; exact ⟨rfl, Hnn0⟩
        isplitr
        · ipureintro; rfl
        iexact «$r0»
      iintro %x' %Heq -
      simp only [sp.KitVal.equiv] at Heq
      subst Heq
      isplitl
      rotate_left
      · itrivial
      iapply (sp.masterSpec_register (γc := γ.conf) (γm := γ.mem) _ _).2
      iexists ip, port, c, k
      isplitr
      · ipureintro; exact ⟨rfl, hk, hkc⟩
      isplitr
      · iapply (conf.is_confIs γ c).1 $$ Hc
      iintro %id %nodes %ready %isL Hif
      unfold regPhi
      iexists id, nodes, ready, isL
      iframe Hif
      ipureintro; rfl
    iintro !> HD %rep
    iapply KitLike.dec_intro
    unfold decT
    iexists regX0
    iframe HD
    isplitr
    · ipureintro; trivial
    isplit
    · iintro %y %Hy Hown
      unfold regTheta
      ileft; iexists y; iframe Hown; ipureintro; exact ⟨Hy.1, Hy.2.1⟩
    · iintro %Hn %ok -
      unfold regTheta
      iright; ipureintro; intro y hy hw; exact Hn y hy hw
  icases Hres with (⟨%Herr, -, %rep, Hphi, Hth⟩ | ⟨%msg, %Hm, -, -, -, -⟩ | ⟨%Hm, -, -⟩)
  rotate_left
  · obtain ⟨-, rfl⟩ := Hm
    wp_auto
    wp_for_post
    wp_apply net.rpc.Client.Close.wp mc γ.W masterAddr $$ [$Hcl] as %e2 -
    wp_apply time.wp_Sleep
    wp_for_post
    iframe
  · cases err with
    | nil => exact absurd rfl Hm.1
    | ok i =>
      wp_auto
      wp_for_post
      wp_apply net.rpc.Client.Close.wp mc γ.W masterAddr $$ [$Hcl] as %e2 -
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
  subst Herr
  unfold regPhi
  icases Hphi with ⟨%id, %nodes, %ready, %isL, %Hrep, Hif⟩
  unfold regTheta
  icases Hth with (⟨%y, %Hy, Hown⟩ | %Hn)
  rotate_left
  · exfalso; exact Hn (.registerReply id nodes ready isL) rfl (by simp [sp.KitVal.wf]) Hrep
  obtain ⟨Hy, Ht⟩ := Hy
  obtain ⟨i', ns', r', l', rfl⟩ : ∃ i' ns' r' l', y = .registerReply i' ns' r' l' := by
    cases y <;> simp_all [sp.KitVal.tag]
  obtain ⟨rfl, rfl⟩ := regEnc.rr_suffix (Hrep.symm.trans Hy)
  rw [regEnc.merge_x0]
  unfold kitValOwn structOwn
  icases Hown with ⟨%ty, %p, %Hv, %Hty, %sl, Hp, Hsl⟩
  subst Hty
  have hp : p = reply_ptr := by
    have h := Hv.1
    simp [interface.mkOk] at h
    exact (go.intoVal_inj h).symm
  subst hp
  cases ready
  · wp_auto
    wp_apply time.wp_Sleep
    wp_for_post
    iframe
  · simp only [↓reduceIte]
    icases Hif with ⟨%fr, #Hcfg, %Hid⟩
    ihave ⟨#Hm, -⟩ := (sp.cfg_memIs (γc := γ.conf) (γm := γ.mem) nodes.length fr nodes) $$ Hcfg
    ihave %Hok := memIs_ok γ.mem nodes $$ Hm
    obtain ⟨rfl, rfl, -, -⟩ :=
      regEnc.rr_inj (regEnc.nodes_bound nodes Hok.1 Hok.2) (Hrep.symm.trans Hy)
    wp_auto
    wp_apply net.rpc.Client.Close.wp mc γ.W masterAddr $$ [$Hcl] as %e2 -
    wp_for_post
    wp_for_post
    iapply HΦ
    iframe Hsl Hcfg
    ipureintro; exact Hid

end proof

end Perennial.github_com.imdea_software.swiftpaxos
