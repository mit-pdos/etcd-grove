/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvwitness/KV__answer.lean`.
Lean-first (no Rocq counterpart).

A read state whose index is at most `applied` (so at most `|ap|`) and whose context decodes
to this replica's read at `seq`, with a waiter in `reads`: the context is the one minted at
`(id, seq)` (`kv_read_minted`, from the fresh token raft's read registry keeps), and the waiter
gets the read state's read index with the value after `ap` (`readAns`, 2026-10-14, stage R:
the reader, which knows the log its deposit was made at, turns it into `readP`). raft v3.7
(2026-10-16, stage R6b): a read state's context is its bytes (`rsOk`, D6).
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.KV__answer
public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.decode
public import RaftWitness.Proof.github_com.mit_pdos.etcd_grove.examples.kvwitness.Lemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]
variable [KVStor GF]

theorem KV.answer.wp_proof (wp_decode : kvwitness.decode.spec (GF := GF) (hG := hG)) :
    KV.answer.spec (GF := GF) (hG := hG) := by
  intro γr γp r id n st ap psl ps dq applied Happ
  wp_start as ⟨#Hrep, Hrun, Hpsl, #Hps⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  wp_auto
  ihave %Hpslen := ownSlice_len $$ Hpsl
  ihave IH : iprop(∃ (k : w64) (rsv : ReadState) (restv : GoSlice) (ps' : List ReadState),
      "i" ∷ i_ptr ↦ k ∗ "rs" ∷ rs_ptr ↦ rsv ∗ "rest" ∷ rest_ptr ↦ restv ∗
      "Hrest" ∷ restv ↦* ps' ∗ "Hcap" ∷ ownSliceCap ReadState restv (DFrac.own 1) ∗
      "Hps'" ∷ ([∗list] v ∈ ps', rsOk γr.raft v) ∗
      "Hrun" ∷ runOwn γr r ap ∗ "Hpsl" ∷ psl ↦*{dq} ps ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (ps.length : Int)⌝) $$ [i rs rest Hrun Hpsl]
  · iexists W64 0, _, _, []
    iframe i rs rest Hrun Hpsl
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply (BigSepL.bigSepL_nil).2; iempintro
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat k < ps.length := by word
    obtain ⟨sv, Hsv⟩ : ∃ sv, ps[sint.nat k]? = some sv := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd' : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z psl.len := ⟨Hk.1, by word⟩
    simp only [Hbnd', and_self]
    wp_apply wp_load_slice_index psl (sint.Z k) _ dq sv Hk.1 $$ [Hpsl] as Hpsl
    · iframe Hpsl; ipureintro; exact Hsv
    ihave #Hsv := BigSepL.bigSepL_lookup (Φ := fun _ v => rsOk (GF := GF) γr.raft v) Hsv $$ Hps
    wp_if_destruct
    · -- a later index: kept
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %sl1 ⟨Hsl1, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [$Hrest $Hcap $Hsl1] as %rest' ⟨Hrest, Hcap, -⟩
      wp_for_post
      iframe
      iexists k + W64 1, sv, rest', ps' ++ [sv]
      iframe
      isplitl
      · iapply (BigSepL.bigSepL_singleton (Φ := fun _ v => rsOk (GF := GF) γr.raft v)).2
        iexact Hsv
      ipureintro; constructor <;> word
    · -- answered, if it is this replica's waiting read
      have Hle : uint.Z sv.Index' ≤ (ap.length : Int) := by word
      iunfold rsOk at Hsv
      icases Hsv with ⟨%cx, #Hcx, #Hok⟩
      imod node_readState_data γp.node id n ⟨sv.Index', cx⟩ ⊤ $$ HisNode [] with #Hok0
      · rw [Hraft]; iexact Hok
      ihave #Hok' : readOk γr.raft cx sv.Index' $$ []
      · rw [← Hraft]; iexact Hok0
      wp_apply wp_decode sv.RequestCtx' cx DFrac.discard $$ [$Hcx]
      iintro -
      cases Hdec : decodeOp cx with
      | none =>
        simp only [decodeRet, Hdec]
        wp_auto
        wp_for_post
        iframe
        iexists k + W64 1, sv, restv, ps'
        iframe
        ipureintro; constructor <;> word
      | some x =>
        obtain ⟨rep, sq, kd, key, vl⟩ := x
        simp only [decodeRet, Hdec]
        wp_auto
        have Hkey : opKey cx = some (rep, sq) := by simp [opKey, Hdec]
        wp_if_destruct
        · wp_if_destruct
          · -- this replica's read
            wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
            iNamed HR
            iunfold readsOwn at Hrds
            iNamed Hrds
            iunfold runOwn at Hrun
            iNamed Hrun
            wp_auto
            wp_apply wp_map_lookup2 go.uint64 (go.GoType.ChannelType go.ChanDir.sendrecv go.string)
              mR Rd sq (DFrac.own 1) $$ [$HRd] as HRd
            ihave Hrun : iprop(r.[RKV, go!"kv"] ↦ mK -∗ mK ↦$ K -∗ r.[RKV, go!"applied"] ↦ mA -∗
                mA ↦$ A -∗ runOwn γr r ap) $$ []
            · iintro HmK HK HmA HA
              unfold runOwn
              iexists mK, K, mA, A, ods
              iframe HmK HK HmA HA Hap Hods
              ipureintro; exact ⟨Hval, HA⟩
            cases HRs : Rd !! sq with
            | none =>
              simp only [Option.getD_none, Option.isSome_none, decide_false, Bool.false_eq_true]
              wp_auto
              wp_apply wp_map_lookup1 go.string go.string mK K key (DFrac.own 1) $$ [$HK] as HK
              wp_apply sync.Mutex.wp_Unlock _ _
                $$ [$Hmu $Hlocked Hns HmW HW Hseq Hwaiters HmR HRd Hreads]
              · inext
                unfold lockInv
                iexists ns, mW, W
                iframe
                isplitr
                · ipureintro; exact HWdom
                unfold readsOwn
                iexists mR, Rd
                iframe
                ipureintro; exact HRdom
              ihave Hrun := Hrun $$ HmK HK HmA HA
              wp_for_post
              iframe
              iexists k + W64 1, sv, restv, ps'
              iframe
              ipureintro; constructor <;> word
            | some ch =>
              simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
              wp_auto
              wp_apply wp_mapDelete mR Rd sq go.uint64
                (go.GoType.ChannelType go.ChanDir.sendrecv go.string) $$ [$HRd] as HRd
              icases (BigSepM.bigSepM_delete (Φ := fun s ch => readWaiterOk (GF := GF) γr id s ch)
                HRs).1 $$ Hreads with ⟨Hw, Hreads⟩
              iunfold readWaiterOk at Hw
              icases Hw with ⟨%c0, %γh, #Hmint, #Hho, Hprod⟩
              -- the waiter's context is the read state's: both are minted at `(id, sq)`
              ihave #Hok'' := Hok'
              iunfold readOk at Hok''
              icases Hok'' with ⟨%Lc', #Hrq', -⟩
              rw [Hif] at Hkey
              ihave #Hcinv : raftCommitInv γr.raft $$ []
              · rw [← Hraft]; open_node HisNode; iexact Hcinv
              imod kv_read_minted γr cx c0 Lc' (id, sq) ⊤ CoPset.subseteq_top raftN_regN Hkey
                $$ Hinv Hcinv Hrq' Hmint with %Hc0
              subst Hc0
              wp_apply wp_map_lookup1 go.string go.string mK K key (DFrac.own 1) $$ [$HK] as HK
              wp_apply sync.Mutex.wp_Unlock _ _
                $$ [$Hmu $Hlocked Hns HmW HW Hseq Hwaiters HmR HRd Hreads]
              · inext
                unfold lockInv
                iexists ns, mW, W
                iframe
                isplitr
                · ipureintro; exact HWdom
                unfold readsOwn
                iexists mR, GMap.delete sq Rd
                iframe
                ipureintro
                intro s ch' Hs
                by_cases Hss : s = sq
                · subst Hss; rw [GMap.lookup_delete_eq] at Hs; cases Hs
                · rw [GMap.lookup_delete_ne _ (Ne.symm Hss)] at Hs; exact HRdom s ch' Hs
              wp_apply wp_handoff_send (t := go.string) γh ch (readAns γr c0) iprop(True)
                iprop(False) ((K !! key).getD (zero_val GoString)) $$ [$Hho $Hprod]
              · isplitl
                · unfold readAns
                  iexists sv.Index', ap, ods
                  iframe Hok' Hap Hods
                  ipureintro
                  refine ⟨Hle, ?_⟩
                  have Hdk : dkey c0 = key := by simp [dkey, Hdec]
                  rw [Hdk]; exact Hval key
                · itrivial
              iintro -
              wp_auto
              ihave Hrun := Hrun $$ HmK HK HmA HA
              wp_for_post
              iframe
              iexists k + W64 1, sv, restv, ps'
              iframe
              ipureintro; constructor <;> word
          · -- not a read
            wp_for_post
            iframe
            iexists k + W64 1, sv, restv, ps'
            iframe
            ipureintro; constructor <;> word
        · -- another replica's
          wp_for_post
          iframe
          iexists k + W64 1, sv, restv, ps'
          iframe
          ipureintro; constructor <;> word
  · iapply HΦ
    iframe

end proof

end kvwitness
end EtcdGrove
end Perennial
