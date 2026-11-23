/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/master/RunLoop.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`m.run()`, the master's goroutine (`master.Master.run.spec`, `Proof/master/Run.lean`), never
returning:

1. wait, under the lock, until `N` replicas have registered; the registrations are then fixed for
   good (`master.lists`' full state: persistent), which `run` reads without the lock (M1);
2. dial each registration's rpc port (`addrList[i]:portList[i]+1000`, replica node `k`'s
   `replicaRpcAddrs[k]`: `master.rpc_of_reg`) until it succeeds, keeping the clients in `nodes`;
   for the first leader, `Replica.BeTheLeader` (`master.wp_call_btl`: the reply decoded in
   `btlOk`'s range by `replicaRpcSpec`'s law; after a failed call the fork resets the reply, e80b31a),
   `UpdateBeTheLeaderReply`, the leader under the lock, `nextLeader` in range;
3. ping every replica (`pingNode`, inlined: `alive`/`leader` under the lock), then `finishInit`
   and the `Broadcast` (the lock invariant's registrations full: `master.lists_full_of`);
4. forever: ping, and on a lost leader `beTheLeader(nextLeader)` and then every replica
   (`beTheLeader`'s spec `Hbtl`, proved once over the closure's loaded pointer).
-/
module

public import Perennial.Proof.fmt
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Run
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.RunDefs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.replica.defs.NewBeTheLeaderReply

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv
  Perennial.fmt

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [master.Assumptions] [examples.swiftnet.Assumptions] [dlog.Assumptions]
variable [net.FieldAssumptions] [replica.defs.Assumptions]
-- the codec (decision D6, Proof/swiftnet/KitLike.lean)
variable [C : net.rpc.RpcCodec netDistGF] [KitLike C]

/-- `defs.UpdateBeTheLeaderReply(p)` (the defs package's; the master group proves its call,
stage plan: "the master group calls defs' two small functions itself"). -/
theorem master.wp_UpdateBTL (p : Loc) (l n : w32) :
    {{ (p ↦ replica.defs.BeTheLeaderReply.mk l n : IProp netDistGF) }}
      (App (Val (@! replica.defs.UpdateBeTheLeaderReply)) (Val #p))
    {{ RET #(); p ↦ replica.defs.BeTheLeaderReply.mk (if l = W32 (-2) then W32 0 else l)
        (if n = W32 (-2) then W32 0 else n) }} := by
  wp_start as Hp
  wp_auto
  wp_if_destruct
  · wp_if_destruct
    · iapply HΦ; simp; iexact Hp
    · iapply HΦ; simp [Hif]; iexact Hp
  · wp_if_destruct
    · iapply HΦ; simp [Hif]; iexact Hp
    · iapply HΦ; simp [Hif, *]; iexact Hp

/-- The master's `c.Call("Replica.BeTheLeader", &BeTheLeaderArgs{}, btl)` with `btl` the initial
reply: no error and the reply's fields in `btlOk`'s range (by `replicaRpcSpec`'s law), or an
error. -/
theorem master.wp_call_btl (c : Loc) (W : net.rpc.RpcWorld netDistGF) (a : GoString)
    (γc γm : GName) (cc : Conf) (pa btl : Loc) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.net.rpc ∗ net.rpc.codecSet net.rpc.RpcCodec.spec ∗ net.rpc.kitCodecOk ∗
        net.rpc.isClient c W a ∗ ⌜W.SS a go!"Replica" = some (sp.replicaRpcSpec γc γm)⌝ ∗
        confIs γc cc ∗ pa ↦ replica.defs.BeTheLeaderArgs.mk ∗
        btl ↦ replica.defs.BeTheLeaderReply.mk (W32 (-1)) (W32 (-1)) }}
      (App (App (App (Val (c @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Call"))
        (Val #(go!"Replica.BeTheLeader")))
        (Val #(interface.mkOk (go.GoType.PointerType replica.defs.BeTheLeaderArgs.ty) #pa)))
        (Val #(interface.mkOk (go.GoType.PointerType replica.defs.BeTheLeaderReply.ty) #btl)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ ∃ l n : w32, btl ↦ replica.defs.BeTheLeaderReply.mk l n ∗
          ⌜sp.btlOk cc.n l n⌝) ∨ ⌜err ≠ interface.nil⌝ }} := by
  wp_start_folded as ⟨#Hcs, #Hko, #Hc, %HSS, #Hcc, Hpa, Hbtl⟩
  let Φr : List w8 → GoString → IProp netDistGF := fun rep _ =>
    iprop(∃ ld nl : w32, ⌜rep = (sp.KitVal.beTheLeaderReply ld nl).encode⌝ ∗
      ∃ N fr l, sp.cfg γc γm N fr l ∗ ⌜sp.btlOk N ld nl⌝)
  let rp := interface.mkOk (go.GoType.PointerType replica.defs.BeTheLeaderReply.ty) #btl
  let Θ : List w8 → Bool → IProp netDistGF := fun rep ok =>
    iprop(∃ x1, kitValOwn rp (DFrac.own 1) x1 ∗
      ⌜ok = true → (∃ y, rep = y.encode ∧ y.tag = 10 ∧
        x1 = sp.KitVal.merge (sp.KitVal.beTheLeaderReply (W32 (-1)) (W32 (-1))) y) ∨
        (∀ y : sp.KitVal, y.tag = 10 → sp.KitVal.wf y → rep ≠ y.encode)⌝)
  wp_apply net.rpc.Client.Call.wp c W a go!"Replica.BeTheLeader" go!"Replica" go!"BeTheLeader"
    (sp.replicaRpcSpec γc γm) _ rp Φr iprop(True)
    (kitValOwn rp (DFrac.own 1) (sp.KitVal.beTheLeaderReply (W32 (-1)) (W32 (-1)))) Θ
    $$ [$Hc Hpa Hbtl] as %err Hres
  · ihave %Hpan := typedPointsto_not_null _ _ _ $$ Hpa
    ihave %Hbn := typedPointsto_not_null _ _ _ $$ Hbtl
    iframe Hcs Hko
    isplitr
    · ipureintro; exact ⟨by decide, HSS⟩
    isplitl [Hpa]
    · iapply enc_of C
      unfold net.rpc.RpcCodec.enc kitCodec
      simp only
      iexists DFrac.own 1, sp.KitVal.beTheLeaderArgs
      isplitl [Hpa]
      · unfold kitValOwn structOwn
        iexists replica.defs.BeTheLeaderArgs.ty, pa
        isplitr
        · ipureintro; exact ⟨rfl, Hpan⟩
        isplitr
        · ipureintro; rfl
        iexists _; iexact Hpa
      iintro %x' %Hx' -
      simp only [sp.KitVal.equiv] at Hx'
      subst Hx'
      isplitl
      · iapply (sp.replicaRpcSpec_beTheLeader (γc := γc) (γm := γm) _ Φr).2
        isplitr
        · ipureintro; rfl
        iintro %ld %nl Hok
        iexists ld, nl
        isplitr
        · ipureintro; rfl
        iexact Hok
      itrivial
    isplitl [Hbtl]
    · unfold kitValOwn structOwn
      iexists replica.defs.BeTheLeaderReply.ty, btl
      isplitr
      · ipureintro; exact ⟨rfl, Hbn⟩
      isplitr
      · ipureintro; rfl
      iexact Hbtl
    imodintro
    iintro HD %rep
    iapply KitLike.dec_intro
    unfold decT
    iexists _
    iframe HD
    isplitr
    · ipureintro; trivial
    isplit
    · iintro %y %Hy Hown
      iexists _
      iframe Hown
      ipureintro
      intro _; left; exact ⟨y, Hy.1, Hy.2.1, rfl⟩
    · iintro %Hno %ok ⟨%x1, %Htag, Hown⟩
      iexists x1
      iframe Hown
      ipureintro
      intro _; right; exact Hno
  iapply HΦ
  icases Hres with (⟨%He, -, %rep, ⟨%ld, %nl, %Hrep, %N', %fr, %l, #Hcfg, %Hok⟩, ⟨%x1, Hown, %Hx1⟩⟩ |
    ⟨%msg, %Hm, -⟩ | ⟨%Hne, -⟩)
  · ileft
    isplitr
    · ipureintro; exact He
    ihave %HN' := sp.cfg_conf (γc := γc) (γm := γm) N' fr l cc $$ [$Hcfg $Hcc]
    rcases Hx1 rfl with ⟨y, Hy, Hyt, rfl⟩ | Hno
    · have hy := master.btl_decode (Hrep ▸ Hy) Hyt
      subst hy
      have hld : ld ≠ 0 := by
        intro h; subst h; rcases Hok.1 with h | h
        · exact absurd h (by decide)
        · simp at h
      have hnl : nl ≠ 0 := by
        intro h; subst h; rcases Hok.2 with h | h | h
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · simp at h
      try simp only [sp.KitVal.merge, hld, hnl, ↓reduceIte]
      unfold kitValOwn structOwn
      icases Hown with ⟨%ty, %p, %Hp, %Hty, Hp'⟩
      obtain ⟨Hp1, -⟩ := Hp
      simp only [rp, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at Hp1
      have := go.intoVal_inj Hp1.2
      subst this
      iexists ld, nl
      iframe Hp'
      ipureintro; rw [HN'.1]; exact Hok
    · exact absurd Hrep (Hno (sp.KitVal.beTheLeaderReply ld nl) rfl (by simp [sp.KitVal.wf]))
  · iright; ipureintro; rw [Hm.2]; exact net.rpc.serverErr_ne_nil msg
  · iright; ipureintro; exact Hne.1

/-- `c.Call("Replica.Ping", &PingArgs{}, &PingReply{})`: returns (any error). -/
theorem master.wp_call_ping (c : Loc) (W : net.rpc.RpcWorld netDistGF) (a : GoString)
    (γc γm : GName) (pa pr : Loc) :
    {{ isPkgInit (PROP := IProp netDistGF) pkg_id.net.rpc ∗ net.rpc.codecSet net.rpc.RpcCodec.spec ∗ net.rpc.kitCodecOk ∗
        net.rpc.isClient c W a ∗ ⌜W.SS a go!"Replica" = some (sp.replicaRpcSpec γc γm)⌝ ∗
        pa ↦ replica.defs.PingArgs.mk (W8 0) ∗ pr ↦ replica.defs.PingReply.mk }}
      (App (App (App (Val (c @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Call"))
        (Val #(go!"Replica.Ping")))
        (Val #(interface.mkOk (go.GoType.PointerType replica.defs.PingArgs.ty) #pa)))
        (Val #(interface.mkOk (go.GoType.PointerType replica.defs.PingReply.ty) #pr)))
    {{ (err : GoInterface), RET #err; True }} := by
  wp_start_folded as ⟨#Hcs, #Hko, #Hc, %HSS, Hpa, Hpr⟩
  let rp := interface.mkOk (go.GoType.PointerType replica.defs.PingReply.ty) #pr
  wp_apply net.rpc.Client.Call.wp c W a go!"Replica.Ping" go!"Replica" go!"Ping"
    (sp.replicaRpcSpec γc γm) _ rp (fun _ _ => iprop(True)) iprop(True)
    (kitValOwn rp (DFrac.own 1) sp.KitVal.pingReply) (fun _ _ => iprop(True))
    $$ [$Hc Hpa Hpr] as %err -
  · ihave %Hpan := typedPointsto_not_null _ _ _ $$ Hpa
    ihave %Hprn := typedPointsto_not_null _ _ _ $$ Hpr
    iframe Hcs Hko
    isplitr
    · ipureintro; exact ⟨by decide, HSS⟩
    isplitl [Hpa]
    · iapply enc_of C
      unfold net.rpc.RpcCodec.enc kitCodec
      simp only
      iexists DFrac.own 1, sp.KitVal.pingArgs (W8 0)
      isplitl [Hpa]
      · unfold kitValOwn structOwn
        iexists replica.defs.PingArgs.ty, pa
        isplitr
        · ipureintro; exact ⟨rfl, Hpan⟩
        isplitr
        · ipureintro; rfl
        iexact Hpa
      iintro %x' %Hx' -
      simp only [sp.KitVal.equiv] at Hx'
      subst Hx'
      isplitl
      · iapply (sp.replicaRpcSpec_ping (γc := γc) (γm := γm) _ _).2
        iexists W8 0
        isplitr
        · ipureintro; rfl
        itrivial
      itrivial
    isplitl [Hpr]
    · unfold kitValOwn structOwn
      iexists replica.defs.PingReply.ty, pr
      isplitr
      · ipureintro; exact ⟨rfl, Hprn⟩
      isplitr
      · ipureintro; rfl
      iexists _; iexact Hpr
    imodintro
    iintro HD %rep
    iapply KitLike.dec_intro
    unfold decT
    iexists _
    iframe HD
    isplitr
    · ipureintro; trivial
    isplit
    · iintro %y %Hy -; itrivial
    · iintro %Hno %ok -; itrivial
  iapply HΦ; itrivial

/-- The range of a `BeTheLeaderReply` the master holds before `UpdateBeTheLeaderReply`: the
initial one (`-1`) or `btlOk`'s. -/
def master.btlR (N : Nat) (l n : w32) : Prop :=
  (l = W32 (-1) ∨ l = W32 (-2) ∨ (1 ≤ l.toInt ∧ l.toInt < N)) ∧
  (n = W32 (-2) ∨ n = W32 (-1) ∨ (1 ≤ n.toInt ∧ n.toInt < N))

theorem master.btlR_of_btlOk {N : Nat} {l n : w32} (h : sp.btlOk N l n) : master.btlR N l n := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- The registrations, complete and fixed (persistent): what phase 1 establishes. -/
def master.registered (m : Loc) (γm : GName) (N : Nat) : IProp netDistGF :=
  iprop(∃ (nl al pl : GoSlice) (nodes addrs : List GoString) (ports : List w64),
    master.fld m go!"nodeList" ↦□ nl ∗ master.fld m go!"addrList" ↦□ al ∗
    master.fld m go!"portList" ↦□ pl ∗ nl ↦*□ nodes ∗ al ↦*□ addrs ∗ pl ↦*□ ports ∗
    memIs γm nodes ∗ ⌜master.regOk N nodes addrs ports ∧ nodes.length = N⌝)

instance master.registered_persistent (m : Loc) (γm : GName) (N : Nat) :
    Persistent (master.registered m γm N) := by
  unfold master.registered; infer_instance

instance master.rpcAddr_persistent (W : net.rpc.RpcWorld netDistGF) (a : GoString) :
    Persistent (net.rpc.rpcAddr W a) := by
  unfold net.rpc.rpcAddr; infer_instance

set_option maxHeartbeats 4000000 in
theorem master.Master.run.wp_proof
    (wp_Printf : dlog.Logger.Printf.spec (GF := netDistGF) (hG := hG))
    (wp_Fatal : dlog.Logger.Fatal.spec (GF := netDistGF) (hG := hG))
    (wp_NBR : replica.defs.NewBeTheLeaderReply.spec) :
    master.Master.run.spec := fun m γc γm N W nodesS0 nl => by
  wp_start as ⟨#Hm, #HnodesP, Hns, HnlF, Haddrs, %HSS, #Hcs, #Hko⟩
  ihave #HisM := Hm
  unfold master.isMaster
  iNamed Hm
  icombine HnodesP Hnodes gives %Heq
  subst Heq
  wp_auto
  ipersist master
  -- phase 1: wait for the `N` registrations
  wp_join (master.registered m γm N) at next as #Hreg
  · wp_for
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
    iNamed HR
    icases master.lists_read $$ Hlists with ⟨%dq, HnlF', Hnl, Hback⟩
    ihave %Hnllen := ownSlice_len _ _ _ $$ Hnl
    wp_auto
    wp_if_destruct
    · -- complete: the registrations are persistent
      have hfull : nodes.length = N := by have := HN.2; word
      ihave Hlists := Hback $$ HnlF' Hnl
      ihave Hl := Hlists
      unfold master.lists
      rw [if_pos hfull]
      icases Hl with ⟨#H1, #H2, #H3, #H4, #H5, #H6, #H7⟩
      ihave Hlists := master.lists_full m γm N nl al pl nodes addrs ports hfull $$ H1 H2 H3 H4 H5
        H6 H7
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlists Hleaders Halives Hlats Hfi]
      · inext
        unfold master.lockInv
        iexists nl, al, pl, nodes, addrs, ports, leaders, alive, lats, fi
        iframe
        isplitl [Hlists]
        · iexact Hlists
        ipureintro; exact Hwf
      wp_for_post
      unfold master.registered
      iframe
      isplitr
      · ipureintro; rfl
      iexists nl, al, pl, nodes, addrs, ports
      iframe H1 H2 H3 H4 H5 H6 H7
      ipureintro; exact ⟨Hwf.1, hfull⟩
    · ihave Hlists := Hback $$ HnlF' Hnl
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlists Hleaders Halives Hlats Hfi]
      · inext
        unfold master.lockInv
        iexists nl, al, pl, nodes, addrs, ports, leaders, alive, lats, fi
        iframe
        ipureintro; exact Hwf
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
  -- phase 2: dial every replica's rpc port
  unfold master.registered
  icases Hreg with ⟨%nlr, %alr, %plr, %nodes, %addrs, %ports, #HnlR, #HalR, #HplR, #HnodesR,
    #HaddrsR, #HportsR, #Hmem, %Hfull⟩
  ihave #Haddrs := Haddrs
  wp_apply time.wp_Sleep
  have hN := HN.2
  ihave %Hnsl := ownSlice_len _ _ _ $$ Hns
  ihave HI : (∃ (j nlv : w64) (cs : List Loc),
      "i" ∷ i_ptr ↦ j ∗ "Hns" ∷ nodesS0 ↦* cs ∗ "HnlF" ∷ master.fld m go!"nextLeader" ↦ nlv ∗
      "#Hcl" ∷ □ (∀ (t : Nat) (c : Loc), ⌜t < sint.nat j ∧ cs[t]? = some c⌝ -∗
        ∃ a, ⌜a ∈ replicaRpcAddrs⌝ ∗ net.rpc.isClient c W a) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ N ∧ cs.length = N ∧
        (nlv = W64 (-1) ∨ (0 ≤ sint.Z nlv ∧ sint.Z nlv < N))⌝ : IProp netDistGF)
    $$ [i Hns HnlF]
  · iexists (W64 0), nl, List.replicate N null
    iframe
    isplitr
    · simp only [named]
      imodintro; iintro %t %c %Ht; exfalso; simp at Ht; omega
    ipureintro; refine ⟨by word, by word, by simp, Or.inl HSS.2⟩
  ihave %HaL := ownSlice_len _ _ _ $$ HaddrsR
  ihave %HpL := ownSlice_len _ _ _ $$ HportsR
  obtain ⟨hal, hpl, -, -, -, -⟩ := Hfull.1
  wp_for HI
  wp_if_destruct
  · ihave %Hcsl := ownSlice_len _ _ _ $$ Hns
    have hjN : sint.nat j < nodes.length := by rw [Hfull.2]; word
    obtain ⟨k, ip, hip, hport, hra⟩ := master.rpc_of_reg Hfull.1 hjN
    rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z alr.len by word)]
    wp_apply wp_load_slice_index _ (sint.Z j) _ _ ip Hj.1 $$ [HaddrsR] as -
    · iframe HaddrsR; ipureintro; exact hip
    rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z plr.len by word)]
    wp_apply wp_load_slice_index _ (sint.Z j) _ _ (W64 (7002 + k)) Hj.1 $$ [HportsR] as -
    · iframe HportsR; ipureintro; exact hport
    wp_apply wp_slice_literal (V := GoInterface)
      [interface.mkOk go.string #ip, interface.mkOk go.int #(W64 (7002 + k) + W64 1000)]
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_auto
    wp_apply fmt.wp_Sprintf_argsWf _ _ _ _ (ArgsWf.cons_string _ _ (ArgsWf.cons_int _ _ _
      (IntArgValue.int _) ArgsWf.nil)) $$ [$Hasl] as %str ⟨-, %Hstr⟩
    rw [master.sprintf_str_d _ _ _ Hstr]
    rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z nodesS0.len by have := Hj.2.2.1; word)]
    ihave #Hra := BigSepL.bigSepL_lookup (Φ := fun _ a => net.rpc.rpcAddr W a) hra $$ Haddrs
    wp_auto
    wp_apply net.rpc.DialHTTP.wp W _ $$ [$Hra] as %c %derr Hd
    wp_apply wp_store_slice_index $$ [$Hns] as Hns
    · ipureintro; have := Hj.2.2.1; word
    icases Hd with (⟨%Hd, #Hc⟩ | ⟨%Hd, #He⟩)
    · subst Hd
      wp_auto
      wp_apply wp_NBR as %btl Hbtl
      wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
      iNamed HR
      ihave %Hldl := ownSlice_len _ _ _ $$ Hleaders
      have hjl : sint.Z j < sint.Z leaderS.len := by have := Hwf.2.1; word
      list_elem leaders (sint.Z j).toNat as isL
      rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z leaderS.len from ⟨Hj.1, hjl⟩)]
      wp_apply wp_load_slice_index _ (sint.Z j) _ _ isL Hj.1 $$ [Hleaders] as Hleaders
      · iframe; ipureintro; exact HisL_lookup
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlists Hleaders Halives Hlats Hfi]
      · inext
        unfold master.lockInv
        iexists nl, al, pl, nodes, addrs, ports, leaders, alive, lats, fi
        iframe
        ipureintro; exact Hwf
      have ha : ip ++ [W8 58] ++ decimal (sint.Z (W64 (7002 + k) + W64 1000)) ∈ replicaRpcAddrs :=
        List.mem_of_getElem? hra
      have Hjl0 : sint.Z j < N := by have := Hwf.2.1; word
      wp_join iprop(∃ (j' nlv' : w64), i_ptr ↦ j' ∗ master.fld m go!"nextLeader" ↦ nlv' ∗
          nodesS0 ↦* cs.set (sint.Z j).toNat c ∗
          ⌜-1 ≤ sint.Z j' ∧ sint.Z j' ≤ sint.Z j ∧
            (nlv' = W64 (-1) ∨ (0 ≤ sint.Z nlv' ∧ sint.Z nlv' < N))⌝)
        with [i HnlF Hbtl btlReply err Hns] as ⟨%j', %nlv', i, HnlF, Hns, %Hj'⟩
      · iexists j, nlv
        iframe
        ipureintro; exact ⟨by word, Int.le_refl _, Hj.2.2.2⟩
      · -- the leader: BeTheLeader
        wp_alloc pa as Hpa
        wp_auto
        ihave %Hcsl' := ownSlice_len _ _ _ $$ Hns
        rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z nodesS0.len by
          simp only [List.length_set] at Hcsl'; have := Hj.2.2.1; word)]
        wp_apply wp_load_slice_index _ (sint.Z j) _ _ c Hj.1 $$ [Hns] as Hns
        · iframe; ipureintro; rw [List.getElem?_set_self (by have := Hj.2.2.1; word)]
        wp_apply master.wp_call_btl c W _ γc γm _ pa btl $$ [$Hc $Hconf $Hpa $Hbtl] as %berr Hbr
        · iframe Hcs Hko; ipureintro; exact HSS.1 _ ha
        wp_join iprop(∃ (p : Loc) (l n : w32), btlReply_ptr ↦ p ∗
            p ↦ replica.defs.BeTheLeaderReply.mk l n ∗ ⌜master.btlR N l n⌝)
          at next with [btlReply Hbr] as ⟨%p, %l, %n, btlReply, Hb, %Hln⟩
        · icases Hbr with (⟨%He, %l, %n, Hb, %Hok⟩ | %He)
          · subst He
            wp_auto
            isplitr
            · ipureintro; rfl
            iexists btl, l, n
            iframe
            ipureintro
            rw [HN.1] at Hok
            exact master.btlR_of_btlOk Hok
          · rcases berr with ei | _
            · wp_auto
              wp_apply wp_slice_literal (V := GoInterface)
                [interface.mkOk go.string #(go!"Not today Zurg!")]
              isplitr
              · ipureintro; rfl
              iintro %fsl ⟨-, -⟩
              wp_auto
              wp_apply master.wp_Fatal wp_Fatal $$ [$Hlg $Hquiet]
              wp_apply wp_NBR as %btl2 Hbtl2
              isplitr
              · ipureintro; rfl
              iexists btl2, W32 (-1), W32 (-1)
              iframe
              ipureintro
              exact ⟨Or.inl rfl, Or.inr (Or.inl rfl)⟩
            · exact absurd rfl He
        wp_apply master.wp_UpdateBTL $$ [$Hb] as Hb
        have hN := HN.2
        generalize hl' : (if l = W32 (-2) then W32 0 else l) = l' at *
        generalize hn' : (if n = W32 (-2) then W32 0 else n) = n' at *
        have hNpos : 0 < N := by have := Hjl0; omega
        have Hl' : l' = W32 (-1) ∨ (0 ≤ l'.toInt ∧ l'.toInt < N) := by
          subst hl'
          by_cases h2 : l = W32 (-2)
          · right; rw [if_pos h2]; simp; omega
          · rw [if_neg h2]
            rcases Hln.1 with h | h | h
            · left; exact h
            · exact absurd h h2
            · right; omega
        have Hn' : n' = W32 (-1) ∨ (0 ≤ n'.toInt ∧ n'.toInt < N) := by
          subst hn'
          by_cases h2 : n = W32 (-2)
          · right; rw [if_pos h2]; simp; omega
          · rw [if_neg h2]
            rcases Hln.2 with h | h | h
            · exact absurd h h2
            · left; exact h
            · right; omega
        wp_join iprop(∃ li : w64, leaderI_ptr ↦ li ∗ btlReply_ptr ↦ p ∗ i_ptr ↦ j ∗
            p ↦ replica.defs.BeTheLeaderReply.mk l' n' ∗ ⌜0 ≤ sint.Z li ∧ sint.Z li < N⌝)
          with [leaderI Hb btlReply i] as ⟨%li, leaderI, btlReply, i, Hb, %Hli⟩
        · iexists j
          iframe
          ipureintro; exact ⟨Hj.1, Hjl0⟩
        · have Hl'' : 0 ≤ l'.toInt ∧ l'.toInt < N := by
            rcases Hl' with h | h
            · exact absurd h Hif
            · exact h
          wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
          iNamed HR
          ihave %Hldl' := ownSlice_len _ _ _ $$ Hleaders
          have hl1 : sint.Z j < sint.Z leaderS.len := by have := Hwf.2.1; word
          have hl2 : sint.Z (W64 (sint.Z l')) < sint.Z leaderS.len := by have := Hwf.2.1; word
          have hl3 : 0 ≤ sint.Z (W64 (sint.Z l')) := by word
          rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z leaderS.len from ⟨Hj.1, hl1⟩)]
          wp_apply wp_store_slice_index $$ [$Hleaders] as Hleaders
          · ipureintro; word
          rw [if_pos (show 0 ≤ sint.Z (W64 (sint.Z l')) ∧ sint.Z (W64 (sint.Z l')) < sint.Z leaderS.len
            from ⟨hl3, hl2⟩)]
          wp_apply wp_store_slice_index $$ [$Hleaders] as Hleaders
          · ipureintro; simp only [List.length_set]; word
          wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlists Hleaders Halives Hlats Hfi]
          · inext
            unfold master.lockInv
            iexists _, _, _, _, _, _, _, alive, lats, fi
            iframe
            ipureintro
            exact ⟨Hwf.1, by simp only [List.length_set]; exact Hwf.2.1, Hwf.2.2⟩
          isplitr
          · ipureintro; rfl
          iexists W64 (sint.Z l')
          iframe
          ipureintro; constructor <;> word
        have Hnl' : W64 (sint.Z n') = W64 (-1) ∨
            (0 ≤ sint.Z (W64 (sint.Z n')) ∧ sint.Z (W64 (sint.Z n')) < N) := by
          rcases Hn' with h | h
          · left; subst h; rfl
          · right; constructor <;> word
        wp_if_destruct
        · wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.int #li]
          isplitr
          · ipureintro; rfl
          iintro %psl ⟨-, -⟩
          wp_auto
          wp_apply master.wp_Printf wp_Printf $$ [$Hlg $Hquiet]
          isplitr
          · ipureintro; rfl
          iexists j, W64 (sint.Z n')
          iframe
          ipureintro; exact ⟨by word, Int.le_refl _, Hnl'⟩
        · wp_if_destruct
          · isplitr
            · ipureintro; first | rfl | trivial
            iexists li - W64 1, W64 (sint.Z n')
            iframe
            ipureintro; exact ⟨by word, by word, Hnl'⟩
          · isplitr
            · ipureintro; first | rfl | trivial
            iexists j, W64 (sint.Z n')
            iframe
            ipureintro; exact ⟨by word, Int.le_refl _, Hnl'⟩
      wp_for_post
      iframe
      iexists (j' + W64 1), nlv', cs.set (sint.Z j).toNat c
      iframe
      try simp only [named]
      isplitr
      · try simp only [named]
        imodintro
        iintro %t %c' %Ht
        by_cases htj : t = (sint.Z j).toNat
        · subst htj
          rw [List.getElem?_set_self (by word)] at Ht
          cases Ht.2
          iexists _
          iframe Hc
          ipureintro; exact ha
        · iapply Hcl
          ipureintro
          rw [List.getElem?_set_ne (by omega)] at Ht
          exact ⟨by have := Ht.1; word, Ht.2⟩
      ipureintro
      refine ⟨by word, by word, by simp only [List.length_set]; exact Hj.2.2.1, Hj'.2.2⟩
    · rcases derr with ei | _
      · wp_auto
        wp_apply wp_slice_literal (V := GoInterface)
          [interface.mkOk go.int #j,
            interface.mkOk go.string #(ip ++ [W8 58] ++ decimal (sint.Z (W64 (7002 + k) + W64 1000)))]
        isplitr
        · ipureintro; rfl
        iintro %psl ⟨-, -⟩
        wp_auto
        wp_apply master.wp_Printf wp_Printf $$ [$Hlg $Hquiet]
        wp_apply time.wp_Sleep
        wp_for_post
        iframe
        iexists j, nlv, cs.set (sint.Z j).toNat c
        iframe
        isplitr
        · simp only [named]
          imodintro
          iintro %t %c' %Ht
          iapply Hcl
          ipureintro
          refine ⟨Ht.1, ?_⟩
          rw [List.getElem?_set_ne (by word)] at Ht; exact Ht.2
        ipureintro; simp only [List.length_set]; exact Hj
      · exact absurd rfl Hd
  · -- phase 3: ping every replica, then `finishInit`
    have hjN : sint.Z j = N := by
      have := Hj.2.1; have : ¬ sint.Z j < sint.Z (W64 N) := Hif; word
    ihave %Hcsl := ownSlice_len _ _ _ $$ Hns
    ipersist pingNode
    rename_i key_ptr
    irename : (key_ptr ↦ Perennial.zero_val w64 : IProp netDistGF) => ikey
    ihave HP : (∃ (t kv : w64) (nv : Loc) (b : Bool),
        "i" ∷ i_ptr ↦ t ∗ "ikey" ∷ key_ptr ↦ kv ∗ "node" ∷ node_ptr ↦ nv ∗
        "new_leader" ∷ new_leader_ptr ↦ b ∗ "Hns" ∷ nodesS0 ↦* cs ∗
        "%Ht" ∷ ⌜0 ≤ sint.Z t ∧ sint.Z t ≤ N⌝ : IProp netDistGF) $$ [i ikey node new_leader Hns]
    · iexists _, _, _, _
      iframe
      ipureintro; word
    wp_for HP
    wp_if_destruct
    · have htN : (sint.Z t).toNat < cs.length := by rw [Hj.2.2.1]; word
      list_elem cs (sint.Z t).toNat as cn
      have htj : (sint.Z t).toNat < sint.nat j ∧ cs[(sint.Z t).toNat]? = some cn :=
        ⟨by word, Hcn_lookup⟩
      ihave #Hcn := Hcl $$ %((sint.Z t).toNat) %cn %htj
      icases Hcn with ⟨%acn, %Hacn, #Hcn⟩
      rw [if_pos (show 0 ≤ sint.Z t ∧ sint.Z t < sint.Z nodesS0.len by word)]
      wp_apply wp_load_slice_index _ (sint.Z t) _ _ cn Ht.1 $$ [Hns] as Hns
      · iframe; ipureintro; exact Hcn_lookup
      wp_apply wp_with_defer as %defer Hdefer
      wp_alloc pa as Hpa
      try wp_auto
      wp_alloc pr as Hpr
      try wp_auto
      wp_apply master.wp_call_ping cn W acn γc γm pa pr $$ [$Hcn Hpa Hpr] as %perr _
      · iframe Hcs Hko
        isplitr
        · ipureintro; exact HSS.1 _ Hacn
        iframe
      wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
      iNamed HR
      ihave %Hldl := ownSlice_len _ _ _ $$ Hleaders
      ihave %Hall := ownSlice_len _ _ _ $$ Halives
      have htl : sint.Z t < sint.Z leaderS.len := by have := Hwf.2.1; word
      have hta : sint.Z t < sint.Z aliveS.len := by have := Hwf.2.2.1; word
      try wp_auto
      wp_join iprop(∃ (alive' leaders' : List Bool) (b' : Bool), aliveS ↦* alive' ∗
          leaderS ↦* leaders' ∗ new_leader_ptr ↦ b' ∗ i_ptr ↦ t ∗
          ⌜alive'.length = N ∧ leaders'.length = N⌝)
        at (if: _ then _ else _) with [Halives Hleaders new_leader i] as ⟨%alive', %leaders', %b',
          Halives, Hleaders, new_leader, i, %Hlen'⟩
      · rcases perr with pe | _
        · wp_auto
          rw [if_pos (show 0 ≤ sint.Z t ∧ sint.Z t < sint.Z aliveS.len from ⟨Ht.1, hta⟩)]
          wp_apply wp_store_slice_index $$ [$Halives] as Halives
          · ipureintro; word
          rw [if_pos (show 0 ≤ sint.Z t ∧ sint.Z t < sint.Z leaderS.len from ⟨Ht.1, htl⟩)]
          list_elem leaders (sint.Z t).toNat as lt
          wp_apply wp_load_slice_index _ (sint.Z t) _ _ lt Ht.1 $$ [Hleaders] as Hleaders
          · iframe; ipureintro; exact Hlt_lookup
          cases lt
          · wp_auto
            isplitr
            · ipureintro; first | rfl | trivial
            iexists _, _, _
            iframe
            ipureintro; simp only [List.length_set]; exact ⟨Hwf.2.2.1, Hwf.2.1⟩
          · wp_auto
            rw [if_pos (show 0 ≤ sint.Z t ∧ sint.Z t < sint.Z leaderS.len from ⟨Ht.1, htl⟩)]
            wp_apply wp_store_slice_index $$ [$Hleaders] as Hleaders
            · ipureintro; word
            isplitr
            · ipureintro; first | rfl | trivial
            iexists _, _, _
            iframe
            ipureintro; simp only [List.length_set]; exact ⟨Hwf.2.2.1, Hwf.2.1⟩
        · wp_auto
          rw [if_pos (show 0 ≤ sint.Z t ∧ sint.Z t < sint.Z aliveS.len from ⟨Ht.1, hta⟩)]
          wp_apply wp_store_slice_index $$ [$Halives] as Halives
          · ipureintro; word
          isplitr
          · ipureintro; first | rfl | trivial
          iexists _, _, _
          iframe
          ipureintro; simp only [List.length_set]; exact ⟨Hwf.2.2.1, Hwf.2.1⟩
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlists Hleaders Halives Hlats Hfi]
      · inext
        unfold master.lockInv
        iexists nl, al, pl, nodes, addrs, ports, leaders', alive', lats, fi
        iframe
        ipureintro; exact ⟨Hwf.1, Hlen'.2, Hlen'.1, Hwf.2.2.2⟩
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      ipureintro; word
    · -- `finishInit`
      wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
      iNamed HR
      icases master.lists_full_of m γm N _ _ _ _ _ _ _ $$ [$Hmem $Hlists] with ⟨Hlists, %Hfl⟩
      wp_auto
      wp_apply sync.Cond.wp_Broadcast $$ [$HisCond]
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlists Hleaders Halives Hlats Hfi]
      · inext
        unfold master.lockInv
        iexists _, _, _, _, _, _, leaders, alive, lats, true
        iframe
        ipureintro; exact ⟨Hwf.1, Hwf.2.1, Hwf.2.2.1, Hwf.2.2.2.1, fun _ => Hfl⟩
      -- phase 4: the leader changes
      ipersist beTheLeader
      have Hcs' : cs.length = N := Hj.2.2.1
      ihave #Hbtl : (□ ∀ (t nlv0 : w64) (Φ' : val → IProp netDistGF),
          ⌜0 ≤ sint.Z t ∧ sint.Z t < N ∧ (nlv0 = W64 (-1) ∨ (0 ≤ sint.Z nlv0 ∧ sint.Z nlv0 < N))⌝ -∗
          master.fld m go!"nextLeader" ↦ nlv0 -∗ nodesS0 ↦* cs -∗
          ▷ (∀ (e : GoInterface) (nlv1 : w64), master.fld m go!"nextLeader" ↦ nlv1 -∗
            nodesS0 ↦* cs -∗ ⌜nlv1 = W64 (-1) ∨ (0 ≤ sint.Z nlv1 ∧ sint.Z nlv1 < N)⌝ -∗ Φ' #e) -∗
          WP (App (App (Val (GoInstruction (GoLoad (go.GoType.FunctionType
            (go.signature.Signature [go.int] false [go.error]))))) (Val #beTheLeader_ptr)) (Val #t))
            {{ Φ' }} : IProp netDistGF) $$ []
      · imodintro
        iintro %t %nlv0 %Φ' %Htn HnlF Hns HΦ'
        wp_auto
        wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
        iNamed HR
        ihave %Hall := ownSlice_len _ _ _ $$ Halives
        have hta : sint.Z t < sint.Z aliveS.len := by have := Hwf.2.2.1; word
        have htN : (sint.Z t).toNat < alive.length := by have := Hwf.2.2.1; word
        list_elem alive (sint.Z t).toNat as alv
        rw [if_pos (show 0 ≤ sint.Z t ∧ sint.Z t < sint.Z aliveS.len from ⟨Htn.1, hta⟩)]
        wp_apply wp_load_slice_index _ (sint.Z t) _ _ alv Htn.1 $$ [Halives] as Halives
        · iframe; ipureintro; exact Halv_lookup
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlists Hleaders Halives Hlats Hfi]
        · inext
          unfold master.lockInv
          iexists _, _, _, _, _, _, leaders, alive, lats, fi
          iframe
          ipureintro; exact Hwf
        cases alv
        · wp_auto
          wp_apply errors.wp_New_errorString as %x _
          iapply HΦ' $$ HnlF Hns
          ipureintro; exact Htn.2.2
        · wp_auto
          wp_apply wp_NBR as %btl Hbtl
          wp_alloc pa as Hpa
          wp_auto
          ihave %Hcsl2 := ownSlice_len _ _ _ $$ Hns
          have htc : (sint.Z t).toNat < cs.length := by rw [Hcs']; word
          list_elem cs (sint.Z t).toNat as cn
          have htj : (sint.Z t).toNat < sint.nat j ∧ cs[(sint.Z t).toNat]? = some cn :=
            ⟨by word, Hcn_lookup⟩
          ihave #Hcn := Hcl $$ %((sint.Z t).toNat) %cn %htj
          icases Hcn with ⟨%acn, %Hacn, #Hcn⟩
          rw [if_pos (show 0 ≤ sint.Z t ∧ sint.Z t < sint.Z nodesS0.len by rw [Hcs'] at htc; word)]
          wp_apply wp_load_slice_index _ (sint.Z t) _ _ cn Htn.1 $$ [Hns] as Hns
          · iframe; ipureintro; exact Hcn_lookup
          wp_apply master.wp_call_btl cn W acn γc γm _ pa btl $$ [$Hcn $Hconf $Hpa $Hbtl] as %berr Hbr
          · iframe Hcs Hko; ipureintro; exact HSS.1 _ Hacn
          icases Hbr with (⟨%He, %l, %n, Hb, %Hok⟩ | %He)
          · subst He
            wp_auto
            wp_apply master.wp_UpdateBTL $$ [$Hb] as Hb
            rw [HN.1] at Hok
            have hNpos : 0 < N := by have := Htn.2.1; have := Htn.1; omega
            generalize hl' : (if l = W32 (-2) then W32 0 else l) = l' at *
            generalize hn' : (if n = W32 (-2) then W32 0 else n) = n' at *
            have Hl' : 0 ≤ l'.toInt ∧ l'.toInt < N := by
              subst hl'
              by_cases h2 : l = W32 (-2)
              · rw [if_pos h2]; simp; omega
              · rw [if_neg h2]
                rcases Hok.1 with h | h
                · exact absurd h h2
                · omega
            have Hn' : n' = W32 (-1) ∨ (0 ≤ n'.toInt ∧ n'.toInt < N) := by
              subst hn'
              by_cases h2 : n = W32 (-2)
              · right; rw [if_pos h2]; simp; omega
              · rw [if_neg h2]
                rcases Hok.2 with h | h | h
                · exact absurd h h2
                · left; exact h
                · right; omega
            have hl1 : l' ≠ W32 (-1) := by intro h; subst h; simp at Hl'
            wp_if_destruct
            · exact absurd rfl hl1
            wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
            iNamed HR
            ihave %Hldl := ownSlice_len _ _ _ $$ Hleaders
            have hl2 : sint.Z (W64 (sint.Z l')) < sint.Z leaderS.len := by have := Hwf.2.1; word
            have hl3 : 0 ≤ sint.Z (W64 (sint.Z l')) := by word
            rw [if_pos (show 0 ≤ sint.Z (W64 (sint.Z l')) ∧ sint.Z (W64 (sint.Z l')) < sint.Z leaderS.len
              from ⟨hl3, hl2⟩)]
            wp_apply wp_store_slice_index $$ [$Hleaders] as Hleaders
            · ipureintro; word
            wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlists Hleaders Halives Hlats Hfi]
            · inext
              unfold master.lockInv
              iexists _, _, _, _, _, _, _, alive, lats, fi
              iframe
              ipureintro
              exact ⟨Hwf.1, by simp only [List.length_set]; exact Hwf.2.1, Hwf.2.2⟩
            wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.int #(W64 (sint.Z l'))]
            isplitr
            · ipureintro; rfl
            iintro %psl ⟨-, -⟩
            wp_auto
            wp_apply master.wp_Printf wp_Printf $$ [$Hlg $Hquiet]
            iapply HΦ' $$ HnlF Hns
            ipureintro
            rcases Hn' with h | h
            · left; subst h; rfl
            · right; constructor <;> word
          · rcases berr with ei | _
            · wp_auto
              iapply HΦ' $$ HnlF Hns
              ipureintro; exact Htn.2.2
            · exact absurd rfl He
      iclear beTheLeader
      ihave HF : (∃ (nlv' : w64) (b' : Bool), "HnlF" ∷ master.fld m go!"nextLeader" ↦ nlv' ∗
          "new_leader" ∷ new_leader_ptr ↦ b' ∗ "Hns" ∷ nodesS0 ↦* cs ∗
          "%Hnl" ∷ ⌜nlv' = W64 (-1) ∨ (0 ≤ sint.Z nlv' ∧ sint.Z nlv' < N)⌝ : IProp netDistGF)
        $$ [HnlF new_leader Hns]
      · iexists nlv, b
        iframe
        ipureintro; exact Hj.2.2.2
      wp_for HF
      wp_apply time.wp_Sleep
      rename_i key_ptr
      irename : (key_ptr ↦ Perennial.zero_val w64 : IProp netDistGF) => ikey
      ihave HP : (∃ (t kv : w64) (nv : Loc) (b : Bool),
          "i" ∷ i_ptr ↦ t ∗ "ikey" ∷ key_ptr ↦ kv ∗ "node" ∷ node_ptr ↦ nv ∗
          "new_leader" ∷ new_leader_ptr ↦ b ∗ "Hns" ∷ nodesS0 ↦* cs ∗
          "%Ht" ∷ ⌜0 ≤ sint.Z t ∧ sint.Z t ≤ N⌝ : IProp netDistGF) $$ [i ikey node new_leader Hns]
      · iexists _, _, _, _
        iframe
        ipureintro; word
      wp_for HP
      wp_if_destruct
      · have htN : (sint.Z t).toNat < cs.length := by rw [Hj.2.2.1]; word
        list_elem cs (sint.Z t).toNat as cn
        have htj : (sint.Z t).toNat < sint.nat j ∧ cs[(sint.Z t).toNat]? = some cn :=
          ⟨by word, Hcn_lookup⟩
        ihave #Hcn := Hcl $$ %((sint.Z t).toNat) %cn %htj
        icases Hcn with ⟨%acn, %Hacn, #Hcn⟩
        rw [if_pos (show 0 ≤ sint.Z t ∧ sint.Z t < sint.Z nodesS0.len by word)]
        wp_apply wp_load_slice_index _ (sint.Z t) _ _ cn Ht.1 $$ [Hns] as Hns
        · iframe; ipureintro; exact Hcn_lookup
        wp_apply wp_with_defer as %defer Hdefer
        wp_alloc pa as Hpa
        try wp_auto
        wp_alloc pr as Hpr
        try wp_auto
        wp_apply master.wp_call_ping cn W acn γc γm pa pr $$ [$Hcn Hpa Hpr] as %perr _
        · iframe Hcs Hko
          isplitr
          · ipureintro; exact HSS.1 _ Hacn
          iframe
        wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
        iNamed HR
        ihave %Hldl := ownSlice_len _ _ _ $$ Hleaders
        ihave %Hall := ownSlice_len _ _ _ $$ Halives
        have htl : sint.Z t < sint.Z leaderS.len := by have := Hwf.2.1; word
        have hta : sint.Z t < sint.Z aliveS.len := by have := Hwf.2.2.1; word
        try wp_auto
        wp_join iprop(∃ (alive' leaders' : List Bool) (b' : Bool), aliveS ↦* alive' ∗
            leaderS ↦* leaders' ∗ new_leader_ptr ↦ b' ∗ i_ptr ↦ t ∗
            ⌜alive'.length = N ∧ leaders'.length = N⌝)
          at (if: _ then _ else _) with [Halives Hleaders new_leader i] as ⟨%alive', %leaders', %b',
            Halives, Hleaders, new_leader, i, %Hlen'⟩
        · rcases perr with pe | _
          · wp_auto
            rw [if_pos (show 0 ≤ sint.Z t ∧ sint.Z t < sint.Z aliveS.len from ⟨Ht.1, hta⟩)]
            wp_apply wp_store_slice_index $$ [$Halives] as Halives
            · ipureintro; word
            rw [if_pos (show 0 ≤ sint.Z t ∧ sint.Z t < sint.Z leaderS.len from ⟨Ht.1, htl⟩)]
            list_elem leaders (sint.Z t).toNat as lt
            wp_apply wp_load_slice_index _ (sint.Z t) _ _ lt Ht.1 $$ [Hleaders] as Hleaders
            · iframe; ipureintro; exact Hlt_lookup
            cases lt
            · wp_auto
              isplitr
              · ipureintro; first | rfl | trivial
              iexists _, _, _
              iframe
              ipureintro; simp only [List.length_set]; exact ⟨Hwf.2.2.1, Hwf.2.1⟩
            · wp_auto
              rw [if_pos (show 0 ≤ sint.Z t ∧ sint.Z t < sint.Z leaderS.len from ⟨Ht.1, htl⟩)]
              wp_apply wp_store_slice_index $$ [$Hleaders] as Hleaders
              · ipureintro; word
              isplitr
              · ipureintro; first | rfl | trivial
              iexists _, _, _
              iframe
              ipureintro; simp only [List.length_set]; exact ⟨Hwf.2.2.1, Hwf.2.1⟩
          · wp_auto
            rw [if_pos (show 0 ≤ sint.Z t ∧ sint.Z t < sint.Z aliveS.len from ⟨Ht.1, hta⟩)]
            wp_apply wp_store_slice_index $$ [$Halives] as Halives
            · ipureintro; word
            isplitr
            · ipureintro; first | rfl | trivial
            iexists _, _, _
            iframe
            ipureintro; simp only [List.length_set]; exact ⟨Hwf.2.2.1, Hwf.2.1⟩
        wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlists Hleaders Halives Hlats Hfi]
        · inext
          unfold master.lockInv
          iexists nl, al, pl, nodes, addrs, ports, leaders', alive', lats, fi
          iframe
          ipureintro; exact ⟨Hwf.1, Hlen'.2, Hlen'.1, Hwf.2.2.2⟩
        wp_for_post
        iframe
        iexists _, _, _, _
        iframe
        ipureintro; word
      · cases b
        · wp_auto
          wp_for_post
          iframe
          iexists _, _
          iframe
          ipureintro; exact Hnl
        · wp_auto
          wp_if_destruct
          · -- no planned next leader: try every replica
            rename_i key_ptr
            irename : (key_ptr ↦ Perennial.zero_val w64 : IProp netDistGF) => ikey
            ihave %Hcsl3 := ownSlice_len _ _ _ $$ Hns
            ihave HR2 : (∃ (u ku nlv2 : w64), "i" ∷ i_ptr ↦ u ∗ "ikey" ∷ key_ptr ↦ ku ∗
                "HnlF" ∷ master.fld m go!"nextLeader" ↦ nlv2 ∗ "Hns" ∷ nodesS0 ↦* cs ∗
                "%Hu" ∷ ⌜0 ≤ sint.Z u ∧ sint.Z u ≤ N ∧
                  (nlv2 = W64 (-1) ∨ (0 ≤ sint.Z nlv2 ∧ sint.Z nlv2 < N))⌝ : IProp netDistGF)
              $$ [i ikey HnlF Hns]
            · iexists _, _, _
              iframe
              ipureintro; refine ⟨by word, by word, Or.inl rfl⟩
            wp_for HR2
            wp_if_destruct
            · have huN : (sint.Z u).toNat < cs.length := by rw [Hcs']; word
              list_elem cs (sint.Z u).toNat as cu
              rw [if_pos (show 0 ≤ sint.Z u ∧ sint.Z u < sint.Z nodesS0.len by word)]
              wp_apply wp_load_slice_index _ (sint.Z u) _ _ cu Hu.1 $$ [Hns] as Hns
              · iframe; ipureintro; exact Hcu_lookup
              try wp_auto
              have Hpre : 0 ≤ sint.Z u ∧ sint.Z u < N ∧
                  (nlv2 = W64 (-1) ∨ (0 ≤ sint.Z nlv2 ∧ sint.Z nlv2 < N)) := ⟨Hu.1, by word, Hu.2.2⟩
              wp_apply Hbtl $$ %u %nlv2 %_ %Hpre HnlF Hns as %e %nlv3 HnlF Hns %Hnl3
              rcases e with ei | _
              · wp_auto
                wp_for_post
                iframe
                iexists _, _, _
                iframe
                ipureintro; exact ⟨by word, by word, Hnl3⟩
              · wp_auto
                wp_for_post
                wp_for_post
                iframe
                iexists _, _
                iframe
                ipureintro; exact Hnl3
            · wp_for_post
              iframe
              iexists _, _
              iframe
              ipureintro; exact Hu.2.2
          · -- the planned next leader
            have Hnlr : 0 ≤ sint.Z nlv' ∧ sint.Z nlv' < N := by
              rcases Hnl with h | h
              · exact absurd h Hif
              · exact h
            have Hpre : 0 ≤ sint.Z nlv' ∧ sint.Z nlv' < N ∧
                (nlv' = W64 (-1) ∨ (0 ≤ sint.Z nlv' ∧ sint.Z nlv' < N)) := ⟨Hnlr.1, Hnlr.2, Hnl⟩
            wp_apply Hbtl $$ %nlv' %nlv' %_ %Hpre HnlF Hns as %e %nlv3 HnlF Hns %Hnl3
            rcases e with ei | _
            · wp_auto
              rename_i key_ptr
              irename : (key_ptr ↦ Perennial.zero_val w64 : IProp netDistGF) => ikey
              ihave %Hcsl3 := ownSlice_len _ _ _ $$ Hns
              ihave HR2 : (∃ (u ku nlv2 : w64), "i" ∷ i_ptr ↦ u ∗ "ikey" ∷ key_ptr ↦ ku ∗
                  "HnlF" ∷ master.fld m go!"nextLeader" ↦ nlv2 ∗ "Hns" ∷ nodesS0 ↦* cs ∗
                  "%Hu" ∷ ⌜0 ≤ sint.Z u ∧ sint.Z u ≤ N ∧
                    (nlv2 = W64 (-1) ∨ (0 ≤ sint.Z nlv2 ∧ sint.Z nlv2 < N))⌝ : IProp netDistGF)
                $$ [i ikey HnlF Hns]
              · iexists _, _, _
                iframe
                ipureintro; refine ⟨by word, by word, Hnl3⟩
              wp_for HR2
              wp_if_destruct
              · have huN : (sint.Z u).toNat < cs.length := by rw [Hcs']; word
                list_elem cs (sint.Z u).toNat as cu
                rw [if_pos (show 0 ≤ sint.Z u ∧ sint.Z u < sint.Z nodesS0.len by word)]
                wp_apply wp_load_slice_index _ (sint.Z u) _ _ cu Hu.1 $$ [Hns] as Hns
                · iframe; ipureintro; exact Hcu_lookup
                try wp_auto
                have Hpre : 0 ≤ sint.Z u ∧ sint.Z u < N ∧
                    (nlv2 = W64 (-1) ∨ (0 ≤ sint.Z nlv2 ∧ sint.Z nlv2 < N)) := ⟨Hu.1, by word, Hu.2.2⟩
                wp_apply Hbtl $$ %u %nlv2 %_ %Hpre HnlF Hns as %e %nlv3 HnlF Hns %Hnl3
                rcases e with ei | _
                · wp_auto
                  wp_for_post
                  iframe
                  iexists _, _, _
                  iframe
                  ipureintro; exact ⟨by word, by word, Hnl3⟩
                · wp_auto
                  wp_for_post
                  wp_for_post
                  iframe
                  iexists _, _
                  iframe
                  ipureintro; exact Hnl3
              · wp_for_post
                iframe
                iexists _, _
                iframe
                ipureintro; exact Hu.2.2
            · wp_auto
              wp_for_post
              iframe
              iexists _, _
              iframe
              ipureintro; exact Hnl3

end proof

end Perennial.github_com.imdea_software.swiftpaxos
