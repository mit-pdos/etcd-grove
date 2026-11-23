/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ClientLeaders.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`s.changeLeaders(cs)` (`kit.go`), client node `c`'s leader changes' goroutine: for each of the
node's planned changes, it waits (under `s.mu`) for its number of returned operations, then asks
the replica at its rpc port (`at(addrs, NC+Node, RPCOff)`) to become the leader
(`Replica.BeTheLeader` over the rpc model, the frozen `replicaRpcSpec`'s law): any answer, error
or none is fine (safety only).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNodeDefs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.replica.defs.NewBeTheLeaderReply
public import Perennial.Proof.fmt
public import Perennial.Proof.time

-- PORT: lab imports dropped: Harness.Proof.log, Harness.Proof.net.rpc.Results

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has netShaExts_hasSha256

namespace cnode

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [C : net.rpc.RpcCodec netDistGF]

local notation "swiftnetPkg" => pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet

/-- `at(addrs, NC+node, RPCOff)`: server node `node`'s rpc port (an instance of the adapter's
`at` spec; `node` a replica's server node, 2..6). -/
abbrev atRpc.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (node : w64), 2 ≤ uint.nat node → uint.nat node ≤ 6 →
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ sl ↦*{dq} addrs }}
    (App (App (App (Val (@! examples.swiftnet.«at»)) (Val #sl)) (Val #(W64 6 + node)))
      (Val #(W64 1000)))
  {{ RET #(replicaRpcAddrs.getD (uint.nat node - 2) go!""); sl ↦*{dq} addrs }}

/-- `s.changeLeaders(cs)` (the leader changes' goroutine), each change at a replica's server
node: never panics. -/
abbrev Sys.changeLeaders.spec (γ : SwiftNames netDistGF) (c : Nat) : Prop :=
  ∀ (s : Loc) (sl : GoSlice) (cs : List examples.swiftnet.change),
  (∀ ch ∈ cs, 2 ≤ uint.nat ch.Node' ∧ uint.nat ch.Node' ≤ 6) →
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ isSysL γ c s ∗ sl ↦*□ cs }}
    (App (Val (s @!! go.GoType.PointerType examples.swiftnet.Sys.ty @!! go!"changeLeaders"))
      (Val #sl))
  {{ RET #(); True }}

end specs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [examples.swiftnet.Assumptions] [net.model.Assumptions]
variable [C : net.rpc.RpcCodec netDistGF] [KitLike C]

set_option goose.wp.extras true

theorem Sys.changeLeaders.wp_proof (γ : SwiftNames netDistGF) (c : Nat) (wp_at : atRpc.spec)
    (wp_NewBTLReply : replica.defs.NewBeTheLeaderReply.spec) :
    Sys.changeLeaders.spec γ c := by
  intro s sl cs hcs
  wp_start as ⟨#Hs, #Hsl⟩
  iunfold isSysL at Hs
  icases Hs with ⟨%conf, %asl, #Haddrs, #Hasl, #Hconf, #Hconfis, #Hmu, #Henv, -⟩
  iunfold nodeEnv at Henv
  icases Henv with ⟨-, #Hrpc, %HSS, #HcodecSet, #HcodecOk, -, -⟩
  wp_auto
  ihave %Hsllen := ownSlice_len $$ Hsl
  ihave HI : (∃ (i : w64) (chv : examples.swiftnet.change), "i" ∷ i_ptr ↦ i ∗
      "ch" ∷ ch_ptr ↦ chv ∗ "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len⌝ : IProp netDistGF)
    $$ [i ch]
  · iexists W64 0, _
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have hi : sint.nat i < cs.length := by rw [Hsllen.1]; word
    list_elem cs (sint.nat i) as chx
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨Hi.1, Hif⟩
    simp only [hb, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z i) cs _ chx hb.1 $$ [] as -
    · iframe Hsl; ipureintro; exact Hchx_lookup
    wp_for
    wp_apply sync.Mutex.wp_Lock _
        (iprop(∃ d : w64, s.[examples.swiftnet.Sys, go!"done"] ↦ d)) $$ [] as ⟨Hlocked, HR⟩
    · iexact Hmu
    icases HR with ⟨%d, Hd⟩
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hd]
    · iframe Hmu Hlocked
      iexists _
      iexact Hd
    wp_if_destruct
    · wp_for_post
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.GoType.InterfaceType [])))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoInterface) (t := go.GoType.InterfaceType [])
        [interface.mkOk go.uint64 #chx.Node', interface.mkOk go.uint64 #chx.After']
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %lit ⟨Hlit, -⟩
      wp_auto
      wp_apply log.wp_Printf _ _ _ _
        (fmt.ArgsWf.cons_int _ _ _ (fmt.IntArgValue.uint64 _)
          (fmt.ArgsWf.cons_int _ _ _ (fmt.IntArgValue.uint64 _) fmt.ArgsWf.nil)) $$ [Hlit] as -
      · iexact Hlit
      have hok := hcs chx (List.mem_of_getElem? Hchx_lookup)
      wp_apply wp_at asl DFrac.discard chx.Node' hok.1 hok.2 $$ [] as -
      · iexact Hasl
      obtain ⟨ra, hidx⟩ : ∃ ra, replicaRpcAddrs[uint.nat chx.Node' - 2]? = some ra :=
        ⟨_, List.getElem?_eq_getElem (by simp [replicaRpcAddrs]; omega)⟩
      have hra : replicaRpcAddrs.getD (uint.nat chx.Node' - 2) go!"" = ra := by
        simp [List.getD_eq_getElem?_getD, hidx]
      rw [hra]
      ihave #Hra := BigSepL.bigSepL_lookup (Φ := fun _ a => net.rpc.rpcAddr (GF := netDistGF) γ.W a)
        hidx $$ Hrpc
      wp_apply net.rpc.DialHTTP.wp γ.W _ $$ [] as %cli %err Hd
      · iexact Hra
      icases Hd with (⟨%Herr, #Hcl⟩ | ⟨%Herr, -⟩)
      rotate_left
      · cases err with
        | nil => exact absurd rfl Herr
        | ok ei =>
          wp_auto
          wp_for_post
          iframe
          iexists i + W64 1, chx
          iframe
          ipureintro; constructor <;> word
      subst Herr
      wp_auto
      wp_alloc ap as Hap
      wp_auto
      wp_apply wp_NewBTLReply as %rp Hrp
      have hS : γ.W.SS (ra) go!"Replica" =
          some (sp.replicaRpcSpec γ.conf γ.mem) := by
        rw [HSS]; unfold services
        have hm : ra ∈ replicaRpcAddrs :=
          List.mem_of_getElem? hidx
        have hne : ¬ (ra = masterAddr ∧ go!"Replica" = go!"Master") :=
          fun h => by have := h.2; simp at this
        rw [if_neg hne, if_pos ⟨hm, rfl⟩]
      ihave %Hapnn := typedPointsto_not_null $$ Hap
      ihave %Hrpnn := typedPointsto_not_null $$ Hrp
      ihave HD : kitValOwn (interface.mkOk (go.GoType.PointerType replica.defs.BeTheLeaderReply.ty)
          #rp) (DFrac.own 1) (sp.KitVal.beTheLeaderReply (W32 (-1)) (W32 (-1))) $$ [Hrp]
      · unfold kitValOwn structOwn
        iexists replica.defs.BeTheLeaderReply.ty, rp
        isplitr
        · ipureintro; exact ⟨rfl, Hrpnn⟩
        isplitr
        · ipureintro; rfl
        iexact Hrp
      wp_apply net.rpc.Client.Call.wp cli γ.W _ go!"Replica.BeTheLeader" go!"Replica"
        go!"BeTheLeader" (sp.replicaRpcSpec γ.conf γ.mem) _ _ (fun _ _ => iprop(True)) iprop(True)
        (kitValOwn (interface.mkOk (go.GoType.PointerType replica.defs.BeTheLeaderReply.ty) #rp)
          (DFrac.own 1) (sp.KitVal.beTheLeaderReply (W32 (-1)) (W32 (-1))))
        (fun _ _ => iprop(True)) $$ [$HcodecSet $HcodecOk $Hcl HD Hap] as %err Hres
      · isplitr
        · ipureintro; exact ⟨by decide, hS⟩
        isplitl [Hap]
        · iapply enc_of C
          simp only [net.rpc.RpcCodec.enc]
          iexists DFrac.own 1, sp.KitVal.beTheLeaderArgs
          isplitl [Hap]
          · unfold kitValOwn structOwn
            iexists replica.defs.BeTheLeaderArgs.ty, ap
            isplitr
            · ipureintro; exact ⟨rfl, Hapnn⟩
            isplitr
            · ipureintro; rfl
            iexists _
            iexact Hap
          iintro %x' %Heq -
          simp only [sp.KitVal.equiv] at Heq
          subst Heq
          isplitl
          rotate_left
          · itrivial
          iapply (sp.replicaRpcSpec_beTheLeader (γc := γ.conf) (γm := γ.mem) _ _).2
          isplitr
          · ipureintro; rfl
          iintro %ld %nl -
          itrivial
        iframe HD
        iintro !> HD %rep
        iapply KitLike.dec_intro
        unfold decT
        iexists _
        iframe HD
        isplitr
        · ipureintro; trivial
        isplit
        · iintro %y %Hy -; itrivial
        · iintro %Hn %ok -; itrivial
      wp_apply net.rpc.Client.Close.wp cli γ.W _ $$ [$Hcl] as %e2 -
      wp_for_post
      iframe
      iexists i + W64 1, chx
      iframe
      ipureintro; constructor <;> word
    · wp_apply time.wp_Sleep
      wp_for_post
      iframe
  · iapply HΦ $$ %trivial

end proof

end cnode

end Perennial.github_com.imdea_software.swiftpaxos
