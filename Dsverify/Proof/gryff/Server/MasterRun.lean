/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Server/MasterRun.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The master's `Run` goroutine (U2): it waits until the three replicas registered (then the
registration lists are persistent, `masterLockInv`), dials each replica's rpc address
(`addr:port+1000`, retried), then pings the replicas forever, asking one to lead when the leader
does not answer; every error of `DialHTTP` and `Call` is retried or ignored.

Port (`Net/`): the replicas' rpc addresses are the kit's (`replicaRpcAddr k`, `127.0.0.1:850(2+k)`),
dialed with `Net/`'s `rpc.DialHTTP.spec` (behind the HTTP handshake: `replicaRpcOk`, `dialEnv`) and
called with `Client.Call.spec` (the generated codec's laws `CodecLaws`); both specs are premises
(`wp_DialHTTP`, `wp_Call`), discharged at linking by `Net/`'s proofs.
-/
module

public import Dsverify.Proof.gryff.Server.MasterRegister
public import Dsverify.Proof.gryff.Server.LogErr
public import Net.Spec.net.rpc.Client__Call
public import Net.Spec.net.rpc.DialHTTP
public import GooseLang.Ext.Net.Decide

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net fmt

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- Replica node `k`'s rpc address. -/
abbrev rpcAddrOf (k : Nat) : GoString := replicaRpcAddr k

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]

/-- `Run`'s `Sprintf("%s:%d", addrList[i], portList[i]+1000)` of replica node `k`. -/
theorem sprintf_rpcAddr (k : Nat) (hk : k < 3) (pv : w64) (hz : sint.Z pv = 8502 + k)
    (s : GoString)
    (h : SprintfOut go!"%s:%d"
      [interface.mkOk go.string #(ipOf k), interface.mkOk go.int #pv] s) :
    s = rpcAddrOf k := by
  have hf : go!"%s:%d" = W8 37 :: W8 115 :: go!":%d" := rfl
  rw [hf] at h
  obtain ⟨o1, rfl, h1⟩ := SprintfOut.str_inv h
  obtain ⟨o2, rfl, h2⟩ := SprintfOut.byte_inv (by decide) h1
  have hp : parseIntVerb go!"d" = some (0, []) := by decide
  obtain ⟨o3, rfl, h3⟩ := SprintfOut.int_inv hp (IntArgValue.int pv)
    (fun z' hz' => intArg_int_uniq _ _ hz') h2
  rw [SprintfOut.done_inv h3]
  rw [hz]
  rcases k with _|_|_|k
  · simp [decimalPad, padZeros, decimalNat_eq, digitByte, ipOf, rpcAddrOf, replicaRpcAddr]
  · simp [decimalPad, padZeros, decimalNat_eq, digitByte, ipOf, rpcAddrOf, replicaRpcAddr]
  · simp [decimalPad, padZeros, decimalNat_eq, digitByte, ipOf, rpcAddrOf, replicaRpcAddr]
  · omega

theorem take_set_succ {A : Type} (cs : List A) (j : Nat) (c : A) (h : j < cs.length) :
    (cs.set j c).take (j+1) = cs.take j ++ [c] := by
  rw [List.take_add_one]
  simp [List.take_set, h]
  apply List.set_eq_of_length_le
  simp; omega

theorem rpcAddrOf_mem (k : Nat) (hk : k < 3) : [0, 1, 2][k]? = some k := by
  rcases k with _|_|_|k
  · rfl
  · rfl
  · rfl
  · omega

/-- Replica node `k`'s rpc address is taken by its own rpc listener, not by the master's. -/
theorem replicaRpcAddr_lis (k : Nat) (hk : k < 3) :
    lisAccepts (replicaRpcLis k) (replicaRpcAddr k) ∧ ¬ lisAccepts masterRpcLis (replicaRpcAddr k) := by
  rcases k with _|_|_|k
  · exact ⟨lisAcceptsB_iff.1 (by decide), fun h => by
      have := lisAcceptsB_iff.2 h; revert this; decide⟩
  · exact ⟨lisAcceptsB_iff.1 (by decide), fun h => by
      have := lisAcceptsB_iff.2 h; revert this; decide⟩
  · exact ⟨lisAcceptsB_iff.1 (by decide), fun h => by
      have := lisAcceptsB_iff.2 h; revert this; decide⟩
  · omega


theorem rpcAddrArgs_argsWf (k : Nat) (pv : w64) :
    ArgsWf [interface.mkOk go.string #(ipOf k), interface.mkOk go.int #pv] :=
  .cons_string _ _ (.cons_int _ _ _ (.int _) .nil)

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [mA : gryff.src.masterlib.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions]
variable (L : CodecLaws (GF := GF))
variable (wp_Call : net.rpc.Client.Call.spec (GF := GF) (hG := hG))
variable (wp_DialHTTP : net.rpc.DialHTTP.spec (GF := GF) (hG := hG))

/-- A client of one of the replicas' rpc addresses (persistent). -/
def clientOk (γ : GryffNames GF) (c : Loc) : IProp GF :=
  iprop(∃ k : Nat, ⌜k < 3⌝ ∗ net.rpc.isClient c γ.rpc (replicaRpcAddr k))

instance clientOk_persistent (γ : GryffNames GF) (c : Loc) :
    Persistent (clientOk γ c) := by
  unfold clientOk; infer_instance

omit [net.rpc.Assumptions] [net.FieldAssumptions] in
theorem worldOk_replica (γ : GryffNames GF) (hw : worldOk γ) (k : Nat) (hk : k < 3) :
    γ.rpc.SS (replicaRpcAddr k) go!"Replica" = some replicaSvc := by
  rw [hw.1]
  unfold rpcServicesDef
  have hm : ¬ (lisAccepts masterRpcLis (replicaRpcAddr k) ∧ go!"Replica" = go!"Master") := by
    intro h; exact absurd h.2 (by decide)
  rw [if_neg hm, if_pos ⟨⟨k, hk, (replicaRpcAddr_lis k hk).1⟩, rfl⟩]

set_option goose.wp.extras true

include L wp_Call in
/-- `c.Call("Replica.Ping", pa, pr)` on a client of a replica: some error or none, ignored. -/
theorem wp_Call_Ping (γ : GryffNames GF) (c pa pr : Loc) (a : w8) :
    {{ net.rpc.codecSet gryffCodec ∗ clientOk γ c ∗ ⌜worldOk γ⌝ ∗
        pa ↦ gryff.src.genericsmrproto.PingArgs.mk a ∗ pr ↦ gryff.src.genericsmrproto.PingReply.mk }}
      (App (App (App (Val (c @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Call"))
        (Val #(go!"Replica.Ping")))
        (Val #(interface.mkOk (go.GoType.PointerType gryff.src.genericsmrproto.PingArgs.ty) #pa)))
        (Val #(interface.mkOk (go.GoType.PointerType gryff.src.genericsmrproto.PingReply.ty) #pr)))
    {{ (err : GoInterface), RET #err; True }} := by
  iintro %Φ ⟨#Hcs, #Hc, %Hw, Hpa, Hpr⟩ HΦ
  unfold clientOk
  icases Hc with ⟨%k, %hk, #Hc⟩
  iapply (wp_Call c γ.rpc (replicaRpcAddr k) go!"Replica.Ping" go!"Replica" go!"Ping" replicaSvc
    (ptrIface gryff.src.genericsmrproto.PingArgs.ty pa)
    (ptrIface gryff.src.genericsmrproto.PingReply.ty pr)
    (fun rep msg => iprop(⌜msg ≠ [] ∨ rep = encPingReply⌝))
    iprop(True) (pr ↦ gryff.src.genericsmrproto.PingReply.mk)
    (fun _ _ => iprop(True)) gryffCodec) $$ [Hpa Hpr]
  · iframe Hc Hcs Hpr
    isplitr
    · ipureintro; exact ⟨by decide, worldOk_replica γ Hw k hk, by simp [ptrIface]⟩
    isplitl [Hpa]
    · iapply L.enc_PingArgs pa (DFrac.own 1) a
      iframe Hpa
      iintro -
      isplitl
      · unfold replicaSvc withErr replicaSvc0
        isplit
        · ileft
          isplitr
          · ipureintro; rfl
          isplitr
          · iexists a; ipureintro; rfl
          ipureintro; right; rfl
        · iintro %msg %hmsg
          ipureintro; left; exact hmsg
      · itrivial
    iintro !> Hpr %rep %Hrep
    rcases Hrep with Hrep | rfl
    · exact absurd rfl Hrep
    iapply L.dec_PingReply pr
    iframe Hpr
    iintro -; itrivial
  iintro !> %err -
  iapply HΦ; itrivial

include L wp_Call in
/-- `c.Call("Replica.BeTheLeader", pa, pr)` on a client of a replica: some error or none. -/
theorem wp_Call_BTL (γ : GryffNames GF) (c pa pr : Loc) :
    {{ net.rpc.codecSet gryffCodec ∗ clientOk γ c ∗ ⌜worldOk γ⌝ ∗
        pa ↦ gryff.src.genericsmrproto.BeTheLeaderArgs.mk ∗
        pr ↦ gryff.src.genericsmrproto.BeTheLeaderReply.mk }}
      (App (App (App (Val (c @!! go.GoType.PointerType net.rpc.Client.ty @!! go!"Call"))
        (Val #(go!"Replica.BeTheLeader")))
        (Val #(interface.mkOk (go.GoType.PointerType gryff.src.genericsmrproto.BeTheLeaderArgs.ty)
          #pa)))
        (Val #(interface.mkOk (go.GoType.PointerType gryff.src.genericsmrproto.BeTheLeaderReply.ty)
          #pr)))
    {{ (err : GoInterface), RET #err; True }} := by
  iintro %Φ ⟨#Hcs, #Hc, %Hw, Hpa, Hpr⟩ HΦ
  unfold clientOk
  icases Hc with ⟨%k, %hk, #Hc⟩
  iapply (wp_Call c γ.rpc (replicaRpcAddr k) go!"Replica.BeTheLeader" go!"Replica"
    go!"BeTheLeader" replicaSvc
    (ptrIface gryff.src.genericsmrproto.BeTheLeaderArgs.ty pa)
    (ptrIface gryff.src.genericsmrproto.BeTheLeaderReply.ty pr)
    (fun rep msg => iprop(⌜msg ≠ [] ∨ rep = encBTLReply⌝))
    iprop(True) (pr ↦ gryff.src.genericsmrproto.BeTheLeaderReply.mk)
    (fun _ _ => iprop(True)) gryffCodec) $$ [Hpa Hpr]
  · iframe Hc Hcs Hpr
    isplitr
    · ipureintro; exact ⟨by decide, worldOk_replica γ Hw k hk, by simp [ptrIface]⟩
    isplitl [Hpa]
    · iapply L.enc_BTLArgs pa (DFrac.own 1)
      iframe Hpa
      iintro -
      isplitl
      · unfold replicaSvc withErr replicaSvc0
        isplit
        · iright
          isplitr
          · ipureintro; exact ⟨rfl, rfl⟩
          ipureintro; right; rfl
        · iintro %msg %hmsg
          ipureintro; left; exact hmsg
      · itrivial
    iintro !> Hpr %rep %Hrep
    rcases Hrep with Hrep | rfl
    · exact absurd rfl Hrep
    iapply L.dec_BTLReply pr
    iframe Hpr
    iintro -; itrivial
  iintro !> %err -
  iapply HΦ; itrivial

include L wp_Call wp_DialHTTP in
theorem wp_Master_Run' (γ : GryffNames GF) (m : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.masterlib ∗ runPre γ m }}
      (App (Val (m @!! go.GoType.PointerType gryff.src.masterlib.Master.ty @!! go!"Run"))
        (Val #()))
    {{ RET #(); True }} := by
  wp_start as Hpre
  unfold runPre
  iNamed Hpre
  unfold masterReg
  iNamed Hreg
  wp_auto
  wp_for
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  unfold masterLockInv
  iNamed Hinv
  ihave %Hnllen := ownSlice_len $$ Hnl
  wp_auto
  wp_if_destruct
  · -- all three replicas registered: the registration lists are persistent
    have hfull : ks.length = 3 := by
      have h := Hnllen.1; simp only [List.length_map] at h; rw [Hif] at h; word
    rw [dqOf_full ks hfull]
    icases Hnlf with #Hnlf
    icases Half with #Half
    icases Hplf with #Hplf
    icases Hnl with #Hnl
    icases Hal with #Hal
    icases Hpl with #Hpl
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hcap Hreg]
    · iexists ks, nl, al, pl
      rw [dqOf_full ks hfull]
      iframe
      iframe #
      ipureintro; exact Hks
    wp_for_post
    wp_apply time.wp_Sleep
    ihave %Hallen := ownSlice_len $$ Hal
    ihave %Hpllen := ownSlice_len $$ Hpl
    ihave %Hnsllen := ownSlice_len $$ Hnsl
    ihave IH : iprop(∃ (j : w64) (cs : List Loc),
        "i" ∷ i_ptr ↦ j ∗ "Hnsl" ∷ nsl ↦* cs ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 3 ∧ cs.length = 3⌝ ∗
        "#Hcl" ∷ □ ([∗list] c ∈ cs.take (sint.nat j), clientOk γ c)) $$ [i Hnsl]
    · iexists _, _
      iframe
      isplitr
      · ipureintro; refine ⟨by word, by word, by simp⟩
      iintro !>
      rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
      iapply BigSepL.bigSepL_nil.2
      iempintro
    wp_for IH
    wp_if_destruct
    · have hjn : sint.nat j < 3 := by word
      obtain ⟨k, hk⟩ : ∃ k, ks[sint.nat j]? = some k :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hk3 : k < 3 := Hks.2.1 k (List.mem_of_getElem? hk)
      have hal : sint.Z al.len = 3 := by have h := Hallen.1; simp at h; word
      have hpl : sint.Z pl.len = 3 := by have h := Hpllen.1; simp at h; word
      have hnsl : sint.Z nsl.len = 3 := by have h := Hnsllen.1; simp at h; word
      simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z al.len from ⟨Hj.1, by word⟩]
      wp_apply wp_load_slice_index al (sint.Z j) (ks.map ipOf) DFrac.discard (ipOf k) Hj.1 $$ [] as -
      · iframe #; ipureintro; simp [show (sint.Z j).toNat = sint.nat j from rfl, hk]
      simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z pl.len from ⟨Hj.1, by word⟩]
      wp_apply wp_load_slice_index pl (sint.Z j) (ks.map portNum) DFrac.discard (portNum k) Hj.1 $$ []
        as -
      · iframe #; ipureintro; simp [show (sint.Z j).toNat = sint.nat j from rfl, hk]
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoInterface) (t := go.any)
        [interface.mkOk go.string #(ipOf k), interface.mkOk go.int #(portNum k + W64 1000)]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %ssl ⟨Hssl, -⟩
      wp_apply fmt.wp_Sprintf_argsWf _ _ _ _ (rpcAddrArgs_argsWf k _) $$ [Hssl] as %s ⟨-, %Hs⟩
      · iframe
      rw [sprintf_rpcAddr k hk3 _ (by unfold portNum; word) s Hs]
      rw [if_pos ⟨Hj.1, by word⟩]
      ihave #Hra := BigSepL.bigSepL_lookup (Φ := fun _ k => replicaRpcOk (GF := GF) γ k)
        (rpcAddrOf_mem k hk3) $$ Hras
      iunfold replicaRpcOk at Hra
      wp_auto
      wp_apply (wp_DialHTTP go!"tcp" net.tcpNet_tcp γ.rpc (rpcAddrOf k)) $$ [] as %c %e Hd
      · iunfold dialEnv at Hde
        icases Hde with ⟨%Hrb, #Hce, #Hhe, #Hcon⟩
        iframe Hce Hhe Hcon
        isplitr
        · ipureintro; exact Hrb
        iexact Hra
      wp_apply wp_store_slice_index nsl (sint.Z j) cs c $$ [Hnsl] as Hnsl
      · iframe; ipureintro; exact ⟨Hj.1, by word⟩
      ihave IH2 : iprop(∃ (c' : Loc) (e' : GoInterface),
          "err" ∷ err_ptr ↦ e' ∗ "Hnsl" ∷ nsl ↦* cs.set (sint.nat j) c' ∗
          "He" ∷ ((⌜e' = interface.nil⌝ ∗ clientOk γ c') ∨
            (⌜e' ≠ interface.nil⌝ ∗ models_lab.errAny e'))) $$ [err Hnsl Hd]
      · iexists c, e
        iframe
        icases Hd with (⟨%He0, #Hc⟩ | ⟨%Hne, #Hea⟩)
        · ileft
          isplitr
          · ipureintro; exact He0
          unfold clientOk
          iexists k
          isplitr
          · ipureintro; exact hk3
          iexact Hc
        · iright
          isplitr
          · ipureintro; exact Hne
          iexact Hea
      wp_for IH2
      icases He with (⟨%He0, #Hc⟩ | ⟨%Hne, #Hea⟩)
      · subst He0
        wp_auto
        rw [if_neg (by simpa using (show (#false : val) ≠ #true from fun h => absurd (go.intoVal_inj h) (by decide))), if_pos (by simp)]
        wp_auto
        ihave %Hlsllen := ownSlice_len $$ Hlsl
        rw [if_pos ⟨Hj.1, by have h := Hlsllen.1; simp at h; word⟩]
        wp_apply wp_store_slice_index lsl (sint.Z j) _ false $$ [Hlsl] as Hlsl
        · iframe; ipureintro; simp; word
        simp only [List.set_replicate_self]
        wp_for_post
        iframe
        iexists _, (cs.set (sint.nat j) c')
        iframe
        isplitr
        · ipureintro; refine ⟨by word, by word, by simp [Hj.2.2]⟩
        iintro !>
        rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word,
          take_set_succ _ _ _ (by rw [Hj.2.2]; exact hjn)]
        iapply BigSepL.bigSepL_snoc.2
        iframe #
      · cases e' with
        | nil => exact absurd rfl Hne
        | ok ei =>
        wp_auto
        rw [if_pos (by simp)]
        wp_auto
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := GoInterface) (t := go.any) [interface.mkOk go.int #j]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iintro %lsl' ⟨Hlsl', -⟩
        wp_apply log.wp_Printf _ _ _ _ (.cons_int _ _ _ (.int j) .nil) $$ [Hlsl'] as -
        · iframe
        wp_apply time.wp_Sleep
        rw [if_pos ⟨Hj.1, by word⟩]
        wp_auto
        wp_apply (wp_DialHTTP go!"tcp" net.tcpNet_tcp γ.rpc (rpcAddrOf k)) $$ [] as %c2 %e2 Hd
        · iunfold dialEnv at Hde
          icases Hde with ⟨%Hrb, #Hce, #Hhe, #Hcon⟩
          iframe Hce Hhe Hcon
          isplitr
          · ipureintro; exact Hrb
          iexact Hra
        wp_apply wp_store_slice_index nsl (sint.Z j) _ c2 $$ [Hnsl] as Hnsl
        · iframe; ipureintro; simp; exact ⟨Hj.1, by word⟩
        wp_for_post
        iframe
        iexists c2, e2
        rw [show (sint.Z j).toNat = sint.nat j from rfl, List.set_set]
        iframe
        icases Hd with (⟨%He0, #Hc⟩ | ⟨%Hne', #Hea'⟩)
        · ileft
          isplitr
          · ipureintro; exact He0
          unfold clientOk
          iexists k
          isplitr
          · ipureintro; exact hk3
          iexact Hc
        · iright
          isplitr
          · ipureintro; exact Hne'
          iexact Hea'
    · -- every replica dialed: the ping loop
      have hj3 : sint.nat j = 3 := by word
      rw [hj3, List.take_of_length_le (by rw [Hj.2.2]; omega)]
      ihave %Hlsllen := ownSlice_len $$ Hlsl
      ihave %Hasllen := ownSlice_len $$ Hasl
      rw [if_pos ⟨by decide, by have h := Hlsllen.1; simp at h; word⟩]
      wp_apply wp_store_slice_index lsl (sint.Z (W64 0)) _ true $$ [Hlsl] as Hlsl
      · iframe; ipureintro; simp
      ihave IH3 : iprop(∃ (lv av : List Bool), "Hlsl" ∷ lsl ↦* lv ∗ "Hasl" ∷ asl ↦* av ∗
          "%Hlv" ∷ ⌜lv.length = 3 ∧ av.length = 3⌝) $$ [Hlsl Hasl]
      · iexists _, _; iframe; ipureintro; simp
      wp_for IH3
      wp_apply time.wp_Sleep
      rename_i ig_ptr
      irename : (ig_ptr ↦ zero_val w64 : IProp GF) => ig
      ihave %Hcslen := ownSlice_len $$ Hnsl
      ihave IH4 : iprop(∃ (n iv : w64) (nv : Loc) (nlb : Bool) (lv' av' : List Bool),
          "i" ∷ i_ptr ↦ n ∗ "ig" ∷ ig_ptr ↦ iv ∗ "node" ∷ node_ptr ↦ nv ∗
          "new_leader" ∷ new_leader_ptr ↦ nlb ∗
          "Hlsl" ∷ lsl ↦* lv' ∗ "Hasl" ∷ asl ↦* av' ∗
          "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ 3 ∧ lv'.length = 3 ∧ av'.length = 3⌝)
        $$ [i ig node new_leader Hlsl Hasl]
      · iexists _, _, _, _, lv, av
        iframe
        ipureintro; exact ⟨by word, by word, Hlv.1, Hlv.2⟩
      wp_for IH4
      by_cases Hif : sint.Z n < sint.Z nsl.len
      · simp only [decide_eq_true Hif, ↓reduceIte, _root_.decide_true, _root_.true_and, if_true, Bool.false_eq_true]
        have hn3 : (sint.Z n).toNat < cs.length := by rw [Hj.2.2]; word
        obtain ⟨c, Hc⟩ : ∃ c, cs[(sint.Z n).toNat]? = some c :=
          ⟨_, List.getElem?_eq_getElem hn3⟩
        try simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z nsl.len from ⟨Hn.1, Hif⟩]
        try wp_auto
        rw [if_pos (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z nsl.len from ⟨Hn.1, Hif⟩)]
        wp_apply wp_load_slice_index nsl (sint.Z n) cs _ c Hn.1 $$ [Hnsl] as Hnsl
        · iframe; ipureintro; exact Hc
        ihave #Hcok := BigSepL.bigSepL_lookup (Φ := fun _ c => clientOk γ c) Hc
          $$ Hcl
        wp_alloc pa as Hpa
        wp_auto
        wp_alloc pr as Hpr
        wp_auto
        wp_apply (wp_Call_Ping L wp_Call γ c pa pr (W8 0)) $$ [Hpa Hpr] as %err -
        · iframe #
          isplitr
          · ipureintro; exact Hw
          iframe
        ihave %Hlvl := ownSlice_len $$ Hlsl
        ihave %Havl := ownSlice_len $$ Hasl
        have hb : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z asl.len := ⟨Hn.1, by have h := Havl.1; word⟩
        have hbl : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z lsl.len := ⟨Hn.1, by have h := Hlvl.1; word⟩
        cases err with
        | nil =>
          wp_auto
          rw [if_pos hb]
          wp_apply wp_store_slice_index asl (sint.Z n) av' true $$ [Hasl] as Hasl
          · iframe; ipureintro; exact ⟨Hn.1, by word⟩
          wp_for_post
          iframe
          iexists _, _, _, _, lv', av'.set (sint.Z n).toNat true
          iframe
          ipureintro; exact ⟨by word, by word, Hn.2.2.1, by simp [Hn.2.2.2]⟩
        | ok ei =>
          wp_auto
          rw [if_pos hb]
          wp_apply wp_store_slice_index asl (sint.Z n) av' false $$ [Hasl] as Hasl
          · iframe; ipureintro; exact ⟨Hn.1, by word⟩
          rw [if_pos hbl]
          obtain ⟨b, Hb⟩ : ∃ b, lv'[(sint.Z n).toNat]? = some b :=
            ⟨_, List.getElem?_eq_getElem (by rw [Hn.2.2.1]; word)⟩
          wp_apply wp_load_slice_index lsl (sint.Z n) lv' _ b Hn.1 $$ [Hlsl] as Hlsl
          · iframe; ipureintro; exact Hb
          wp_if_destruct
          · wp_for_post
            iframe
            iexists _, _, _, _, lv', av'.set (sint.Z n).toNat false
            iframe
            ipureintro; exact ⟨by word, by word, Hn.2.2.1, by simp [Hn.2.2.2]⟩
          · rw [if_pos hbl]
            wp_apply wp_store_slice_index lsl (sint.Z n) lv' false $$ [Hlsl] as Hlsl
            · iframe; ipureintro; exact ⟨Hn.1, by word⟩
            wp_for_post
            iframe
            iexists _, _, _, _, lv'.set (sint.Z n).toNat false, av'.set (sint.Z n).toNat false
            iframe
            ipureintro; exact ⟨by word, by word, by simp [Hn.2.2.1], by simp [Hn.2.2.2]⟩
      · -- after the pings: ask a live replica to lead if the leader did not answer
        simp only [decide_eq_false Hif, ↓reduceIte, _root_.decide_true, _root_.true_and, if_true, Bool.false_eq_true]
        cases nlb with
        | false =>
          wp_auto
          wp_for_post
          iframe
          iexists lv', av'
          iframe
          ipureintro; exact ⟨Hn.2.2.1, Hn.2.2.2⟩
        | true =>
          wp_auto
          rename_i ig2_ptr
          irename : (ig2_ptr ↦ zero_val w64 : IProp GF) => ig2
          ihave IH5 : iprop(∃ (n2 iv2 : w64) (nv2 : Loc) (lv2 av2 : List Bool),
              "i" ∷ i_ptr ↦ n2 ∗ "ig2" ∷ ig2_ptr ↦ iv2 ∗ "new_master" ∷ new_master_ptr ↦ nv2 ∗
              "Hlsl" ∷ lsl ↦* lv2 ∗ "Hasl" ∷ asl ↦* av2 ∗
              "%Hn2" ∷ ⌜0 ≤ sint.Z n2 ∧ sint.Z n2 ≤ 3 ∧ lv2.length = 3 ∧ av2.length = 3⌝)
            $$ [i ig2 new_master Hlsl Hasl]
          · iexists _, _, _, lv', av'
            iframe
            ipureintro; exact ⟨by word, by word, Hn.2.2.1, Hn.2.2.2⟩
          wp_for IH5
          by_cases Hif : sint.Z n2 < sint.Z nsl.len
          · simp only [decide_eq_true Hif, ↓reduceIte, _root_.decide_true, _root_.true_and, if_true, Bool.false_eq_true]
            have hn3 : (sint.Z n2).toNat < cs.length := by rw [Hj.2.2]; word
            obtain ⟨c, Hc⟩ : ∃ c, cs[(sint.Z n2).toNat]? = some c :=
              ⟨_, List.getElem?_eq_getElem hn3⟩
            try simp only [show 0 ≤ sint.Z n2 ∧ sint.Z n2 < sint.Z nsl.len from ⟨Hn2.1, Hif⟩]
            try wp_auto
            rw [if_pos (show 0 ≤ sint.Z n2 ∧ sint.Z n2 < sint.Z nsl.len from ⟨Hn2.1, Hif⟩)]
            wp_apply wp_load_slice_index nsl (sint.Z n2) cs _ c Hn2.1 $$ [Hnsl] as Hnsl
            · iframe; ipureintro; exact Hc
            ihave #Hcok := BigSepL.bigSepL_lookup (Φ := fun _ c => clientOk γ c) Hc $$ Hcl
            ihave %Hlvl := ownSlice_len $$ Hlsl
            ihave %Havl := ownSlice_len $$ Hasl
            have hb : 0 ≤ sint.Z n2 ∧ sint.Z n2 < sint.Z asl.len :=
              ⟨Hn2.1, by have h := Havl.1; word⟩
            have hbl : 0 ≤ sint.Z n2 ∧ sint.Z n2 < sint.Z lsl.len :=
              ⟨Hn2.1, by have h := Hlvl.1; word⟩
            rw [if_pos hb]
            obtain ⟨b, Hb⟩ : ∃ b, av2[(sint.Z n2).toNat]? = some b :=
              ⟨_, List.getElem?_eq_getElem (by rw [Hn2.2.2.2]; word)⟩
            wp_apply wp_load_slice_index asl (sint.Z n2) av2 _ b Hn2.1 $$ [Hasl] as Hasl
            · iframe; ipureintro; exact Hb
            wp_if_destruct
            · wp_for_post
              iframe
              iexists _, _, _, lv2, av2
              iframe
              ipureintro; exact ⟨by word, by word, Hn2.2.2.1, Hn2.2.2.2⟩
            · wp_alloc pa as Hpa
              wp_auto
              wp_alloc pr as Hpr
              wp_auto
              wp_apply (wp_Call_BTL L wp_Call γ c pa pr) $$ [Hpa Hpr] as %err -
              · iframe #
                isplitr
                · ipureintro; exact Hw
                iframe
              cases err with
              | nil =>
                wp_auto
                rw [if_pos hbl]
                wp_apply wp_store_slice_index lsl (sint.Z n2) lv2 true $$ [Hlsl] as Hlsl
                · iframe; ipureintro; exact ⟨Hn2.1, by word⟩
                wp_bind (App (Val (GoInstruction (CompositeLiteral
                  (go.SliceType (go.InterfaceType []))))) (Val (LiteralValueV _)))
                iapply wp_slice_literal (V := GoInterface) (t := go.any) [interface.mkOk go.int #n2]
                wp_auto
                isplitl []
                · ipureintro; rfl
                iintro %lsl2 ⟨Hlsl2, -⟩
                wp_apply log.wp_Printf _ _ _ _ (.cons_int _ _ _ (.int n2) .nil) $$ [Hlsl2] as -
                · iframe
                wp_for_post
                wp_for_post
                iframe
                iexists lv2.set (sint.Z n2).toNat true, av2
                iframe
                ipureintro; exact ⟨by simp [Hn2.2.2.1], Hn2.2.2.2⟩
              | ok ei =>
                wp_auto
                wp_for_post
                iframe
                iexists _, _, _, lv2, av2
                iframe
                ipureintro; exact ⟨by word, by word, Hn2.2.2.1, Hn2.2.2.2⟩
          · simp only [decide_eq_false Hif, ↓reduceIte, _root_.decide_true, _root_.true_and, if_true, Bool.false_eq_true]
            wp_for_post
            iframe
            iexists lv2, av2
            iframe
            ipureintro; exact ⟨Hn2.2.2.1, Hn2.2.2.2⟩
  · wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hnlf Half Hplf Hnl Hal Hpl Hcap Hreg]
    · iexists ks, nl, al, pl
      iframe
      ipureintro; exact Hks
    wp_apply time.wp_Sleep
    wp_for_post
    iframe

end proof

end Perennial.gryff
