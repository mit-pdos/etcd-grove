/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ClientLeaders.lean (lab master
915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md), onto `RpcHttpHyp`'s `DialHTTP` and the
generated codec (`callBtl.spec`, the master's `wp_call_btl`).

`s.changeLeaders(cs)` (`kit.go`): for each planned change, wait (under `mu`) until enough of the
client's operations returned, log it, dial the replica's rpc port over HTTP and call
`Replica.BeTheLeader`, then close; a failed dial or call is not retried. It never panics.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNodeDefs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.replica.defs.NewBeTheLeaderReply
public import Net.Spec.net.rpc.Client__Close
public import Perennial.Proof.fmt
public import Perennial.Proof.time
public import Perennial.Proof.log

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has netShaExts_hasSha256

namespace cnode

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [net.Assumptions] [net.rpc.Assumptions] [net.FieldAssumptions] [log.Assumptions]
  [net.http.Assumptions] [client.Assumptions] [examples.swiftnet.Assumptions]
variable [RpcHttpAddr netDistGF] [H : RpcHttpHyp netDistGF]

set_option goose.wp.extras true

theorem Sys.changeLeaders.wp_proof (γ : SwiftNames netDistGF) (c : Nat) (wp_at : atRpc.spec)
    (wp_NewBTLReply : replica.defs.NewBeTheLeaderReply.spec)
    (wp_callBtl : callBtl.spec (hG := hG))
    (wp_Close : net.rpc.Client.Close.spec (GF := netDistGF) (hG := hG)) :
    Sys.changeLeaders.spec γ c := by
  intro s sl cs hcs
  wp_start as ⟨#Hs, #Hsl⟩
  iunfold isSysL at Hs
  icases Hs with ⟨%conf, %asl, #Haddrs, #Hasl, #Hconf, #Hconfis, #Hmu, -, #Henv, -, -⟩
  iunfold nodeEnv at Henv
  icases Henv with ⟨-, #Hrpc, %HSS, #HcodecSet, #HcodecOk, -, -⟩
  ihave #Hrpcp : isPkgInit (PROP := IProp netDistGF) pkg_id.net.rpc $$ []
  · iPkgInit
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
      ihave #Hra := BigSepL.bigSepL_lookup (Φ := fun _ a => rpcHttp (GF := netDistGF) γ.W a)
        hidx $$ Hrpc
      wp_apply DialHTTP_tcp γ.W _ $$ [$Hra] as %cli %err Hd
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
      have hS : γ.W.SS ra go!"Replica" = some (withErr (sp.replicaRpcSpec γ.conf γ.mem)) := by
        rw [HSS]; unfold services
        have hm : ra ∈ replicaRpcAddrs := List.mem_of_getElem? hidx
        have hne : ¬ (lisAcceptsB go!":7001" ra = true ∧ go!"Replica" = go!"Master") :=
          fun h => by have := h.2; simp at this
        rw [if_neg hne, if_pos ⟨hm, rfl⟩]
      wp_apply wp_callBtl cli γ.W ra γ.conf γ.mem conf ap rp $$ [Hap Hrp] as %err2 -
      · iframe HcodecSet HcodecOk Hcl Hap Hrp
        isplitr
        · ipureintro; exact hS
        iunfold swiftpaxos.conf.is at Hconfis
        iexact Hconfis
      wp_apply wp_Close cli γ.W ra $$ [$Hcl] as %e2 -
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
