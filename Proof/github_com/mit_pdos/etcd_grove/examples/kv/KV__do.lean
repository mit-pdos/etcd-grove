/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/KV__do.lean`. Lean-first (no
Rocq counterpart). raft v3.7 (2026-10-16, stage R6b): `Node.Propose` wants the data frozen and
non-empty (D6); an encoding is at least 25 bytes.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__do
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.encode
public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Lemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

theorem KV.do.wp_proof
    (wp_encode : kv.encode.spec (GF := GF) (hG := hG))
    (wp_node_Propose : node.Propose.spec (GF := GF) (hG := hG)) :
    KV.do.spec (GF := GF) (hG := hG) := by
  intro γr γp r kind key val Ψ Hkey Hval
  wp_start as ⟨#Hreg, Hau⟩
  iunfold isKV at Hreg
  icases Hreg with ⟨%id, %n, %st, #Hrep⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
  iNamed HR
  wp_auto_lc 1
  wp_if_destruct
  · -- out of sequence numbers: the replica stops
    ihave Hspin : iprop(True) $$ []
    · itrivial
    wp_for Hspin
    wp_for_post
    iframe
  have Hns : uint.Z ns + 1 < 2 ^ 64 := by
    have : ns ≠ W64 18446744073709551615 := by assumption
    word
  -- the operation's datum, minted, with its slot holding the client's update (2026-10-14,
  -- stage R)
  ihave Hau : opAu γr (kvNext kind key val) key Ψ $$ [Hau]
  · unfold opAu; iexact Hau
  imod kv_mint γr id ns kind key val Ψ ⊤ CoPset.subseteq_top Hns (by omega) $$ Hinv Hseq Hlc1 Hau
    with ⟨Hseq, #Hmint, Hfresh, %γo, #Hop, #Hsp, Htok⟩
  have Hdne : encodeOp id (ns + W64 1) kind key val ≠ [] := by
    intro h; have := encodeOp_length id (ns + W64 1) kind key val; rw [h] at this
    simp at this; omega
  generalize Hd : encodeOp id (ns + W64 1) kind key val = d at Hdne
  wp_apply chan.wp_make2 (V := GoString) (W64 1) as %ch %γc ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; decide
  ihave Hoc : ownChan γc GoString (.Buffered []) $$ Hoc
  imod start_handoff ch (waitP γr d) iprop(True) iprop(False) γc $$ Hch Hoc
    with ⟨%γh, %Hγh, #Hho, Hprod, Hcons⟩
  have HWfresh : W !! (ns + W64 1) = none := by
    cases h : W !! (ns + W64 1) with
    | none => rfl
    | some ch' => have := HWdom _ _ h; word
  wp_apply wp_mapInsert go.uint64 mW W (ns + W64 1) ch $$ [$HW] as HW
  ihave Hrds := readsOwn_mono γr id r ns (ns + W64 1) (by word) $$ Hrds
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hns HmW HW Hseq Hwaiters Hprod Hrds]
  · inext
    unfold lockInv
    iexists ns + W64 1, mW, W.insert (ns + W64 1) ch
    iframe Hns HmW HW Hseq Hrds
    isplitr
    · ipureintro
      intro s ch' Hs
      by_cases Hss : s = ns + W64 1
      · subst Hss; exact Int.le_refl _
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hss)] at Hs
        have := HWdom _ _ Hs; word
    iapply (BigSepM.bigSepM_insert (Φ := fun s ch => waiterOk (GF := GF) γr id s ch) HWfresh).2
    iframe Hwaiters
    unfold waiterOk
    iexists d, γh
    iframe Hmint Hho Hprod
  -- (2026-10-21) the datum registered with raft, once; then every proposal of it, a retry of a
  -- dropped one included, takes the registration and a new update over raft's log (2026-10-14,
  -- stage R), which the store's invariant makes (`kv_propAu`) and raft fires at most once
  rw [← Hraft]
  imod node_prop_register γp.node id n d (fun _ => iprop(True)) ⊤ CoPset.subseteq_top
    $$ HisNode Hfresh with #Hpi
  ihave HI : iprop(True) $$ []
  · itrivial
  wp_for HI
  wp_apply context.wp_Background
  wp_apply wp_encode id (ns + W64 1) kind key val Hkey Hval as %b ⟨Hb, Hbcap⟩
  rw [Hd]
  imod ownSlice_persist b _ _ $$ Hb with #Hb
  ihave Hpau := kv_propAu γr d γo $$ Hinv Hop
  rw [← Hraft]
  ihave Harg : propArg γp.node.raft d (fun _ => iprop(True)) $$ [Hpau]
  · unfold propArg
    iframe Hpi Hpau
  ihave #Hbg := nodeCtx_background (GF := GF) bgCd
  wp_apply wp_node_Propose γp.node id n b d _ context.backgroundCtxVal bgCd
    $$ [$Hraftinit $HisNode $Hbg $Hb $Harg] as %err -
  · ipureintro; exact Hdne
  cases err with
  | ok i =>
    -- dropped: propose again
    wp_auto
    simp only [show decide ((#true : val) = #true) = true from decide_eq_true rfl, ↓reduceIte,
      _root_.decide_true]
    wp_auto
    wp_for_post
    iframe
  | nil =>
    wp_auto
    rw [ite_eq_right (by simp only [decide_eq_true_eq]; intro h; cases go.intoVal_inj (V := Bool) h),
      ite_eq_left (by simp)]
    wp_auto_lc 2
    wp_apply +noauto wp_handoff_receive (t := go.string) γh ch (waitP γr d) iprop(True) iprop(False)
      false $$ [$Hho $Hcons] as %v %ok ⟨Hcons, Hgot⟩
    unfold handoffGot
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hgot with ⟨-, Hf⟩
      iexfalso; iexact Hf
    simp only [↓reduceIte]
    icases Hgot with ⟨Hw, -⟩
    iunfold waitP at Hw
    icases Hw with ⟨%l, %ods, %m, #Hl, #Hods, %Hm⟩
    obtain ⟨Hm1, Hm2, Hv⟩ := Hm
    -- the client's result, from the operation's slot (2026-10-14, stage R)
    ihave #Hcinv : raftCommitInv γr.raft $$ []
    · rw [← Hraft]; open_node HisNode; iexact Hcinv
    imod kv_collect γr d γo Ψ l ods m ⊤ CoPset.subseteq_top raftN_regN Hm1 Hm2
      $$ Hinv Hcinv Hop Hsp Htok Hl Hods with HQ
    imod lc_fupd_elim_later $$ Hlc1 HQ with HQ
    imod lc_fupd_elim_later $$ Hlc2 HQ with HQ
    wp_auto
    rw [← Hv]
    iapply HΦ $$ HQ

end proof

end kv
end EtcdGrove
end Perennial
