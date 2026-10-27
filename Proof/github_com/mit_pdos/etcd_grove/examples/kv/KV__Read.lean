/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/KV__Read.lean`.
Lean-first (no Rocq counterpart).

Under the lock, a new sequence number mints the read's context and its fresh token for raft's
read registry (`kv_mint_read`), and the read waits on a handoff channel in `reads`
(`readsOwn`); `Node.ReadIndex` takes the context's bytes (its slice read-only, D6), the token,
the read's persistent update (trivial: `kv_readAu`), the committed log of the caller's lower
bound and the read credit, and deposits the update at a committed log `Lc` extending it
(2026-10-14, stage R); the applier answers with a read index of the context and the value after
a committed log at least that long (`readAns`, `KV.answer`), which extends `Lc`
(`readOk_prefix`) and so the caller's log.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.KV__Read
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

theorem KV.Read.wp_proof
    (wp_encode : kv.encode.spec (GF := GF) (hG := hG))
    (wp_node_ReadIndex : Draft.node.ReadIndex.spec (GF := GF) (hG := hG)) :
    KV.Read.spec (GF := GF) (hG := hG) := by
  intro γr γp r key L0 Hkey
  wp_start as ⟨#Hreg, Hrdc, #Hlb⟩
  iunfold isKV at Hreg
  icases Hreg with ⟨%id, %n, %st, #Hrep⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  iunfold kvLb at Hlb
  icases Hlb with ⟨%l0, #Hl0, %HL0⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
  iNamed HR
  wp_auto
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
  -- the read's context, minted, and committed to the read seeing what the caller knew committed
  imod kv_mint_read γr id ns key l0 ⊤ CoPset.subseteq_top Hns (by omega) $$ Hinv Hseq Hl0
    with ⟨Hseq, #Hmint, #Hrc⟩
  generalize Hc : encodeOp id (ns + W64 1) opReadB key [] = cx
  wp_apply chan.wp_make2 (V := GoString) (W64 1) as %ch %γc ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; decide
  ihave Hoc : ownChan γc GoString (.Buffered []) $$ Hoc
  imod start_handoff ch (readAns γr cx) iprop(True) iprop(False) γc $$ Hch Hoc
    with ⟨%γh, %Hγh, #Hho, Hprod, Hcons⟩
  iunfold readsOwn at Hrds
  iNamed Hrds
  have HRfresh : Rd !! (ns + W64 1) = none := by
    cases h : Rd !! (ns + W64 1) with
    | none => rfl
    | some ch' => have := HRdom _ _ h; word
  wp_auto
  wp_apply wp_mapInsert go.uint64 mR Rd (ns + W64 1) ch $$ [$HRd] as HRd
  wp_apply sync.Mutex.wp_Unlock _ _
    $$ [$Hmu $Hlocked Hns HmW HW Hseq Hwaiters HmR HRd Hreads Hprod]
  · inext
    unfold lockInv
    iexists ns + W64 1, mW, W
    iframe Hns HmW HW Hseq Hwaiters
    isplitr
    · ipureintro
      intro s ch' Hs
      have := HWdom _ _ Hs; word
    unfold readsOwn
    iexists mR, Rd.insert (ns + W64 1) ch
    iframe HmR HRd
    isplitr
    · ipureintro
      intro s ch' Hs
      by_cases Hss : s = ns + W64 1
      · subst Hss; exact Int.le_refl _
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm Hss)] at Hs
        have := HRdom _ _ Hs; word
    iapply (BigSepM.bigSepM_insert (Φ := fun s ch => readWaiterOk (GF := GF) γr id s ch)
      HRfresh).2
    iframe Hreads
    unfold readWaiterOk
    iexists cx, γh
    iframe Hmint Hho Hprod
  -- `ReadIndex`, with the context's bytes read-only, its fresh token and the read's (trivial)
  -- persistent update, at the committed log of the caller's lower bound
  wp_apply context.wp_Background
  wp_apply wp_encode id (ns + W64 1) (W8 3) key [] Hkey (by simp) as %b ⟨Hb, -⟩
  rw [show (W8 3 : w8) = opReadB from rfl, Hc]
  imod ownSlice_persist b _ _ $$ Hb with #Hb
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hbg := nodeCtx_background (GF := GF) bgCd
  wp_apply wp_node_ReadIndex n γr.cluster kvRaftN id b cx
    (fun ops => iprop(⌜Draft.opsOf l0 <+: ops⌝)) context.backgroundCtxVal
    bgCd $$ [$Hraftinit $HisNode $Hbg $Hb $Hrc $Hrdc] as %err -
  -- the answer: a read state of the context, and the value after a committed log at least that
  -- long; the read took effect at a committed log that long (`Draft.readStateOk_ctx`), whose
  -- requested entries extend `l0`'s
  wp_apply +noauto wp_handoff_receive (t := go.string) γh ch (readAns γr cx)
    iprop(True) iprop(False) false $$ [$Hho $Hcons] as %v %ok ⟨Hcons, Hgot⟩
  unfold handoffGot
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hgot with ⟨-, Hf⟩
    iexfalso; iexact Hf
  simp only [↓reduceIte]
  icases Hgot with ⟨Hw, -⟩
  iunfold readAns at Hw
  icases Hw with ⟨%i, %ap, #Hok, #Hap, %Hi⟩
  icases Draft.readStateOk_ctx γr.cluster kvRaftN cx i (fun ops => iprop(⌜Draft.opsOf l0 <+: ops⌝))
    $$ [Hok Hrc] with ⟨%l, %Hlen, #Hl, HQ⟩
  · iframe Hok Hrc
  ihave HQ : iprop(▷ ⌜Draft.opsOf l0 <+: Draft.opsOf l⌝) $$ [HQ]
  · inext; icases HQ with #%HQ; ipureintro; exact HQ
  imod HQ with %HQ
  wp_auto
  ihave %Hag := Draft.isCommittedLogLb_agree γr.cluster l ap $$ [Hl Hap]
  · iframe Hl Hap
  have Hlap : l <+: ap := by
    rcases Hag with h | h
    · exact h
    · have : ap.length ≤ l.length := h.length_le
      have : l.length = ap.length := by have := Hi.1; rw [Hlen] at *; word
      exact (h.eq_of_length this.symm) ▸ List.prefix_refl _
  iapply HΦ
  iexists logHist ap
  isplitl
  · unfold kvLb
    iexists ap
    iframe Hap
    ipureintro; rfl
  ipureintro
  rw [HL0]
  have Hdk : dkey cx = key := by rw [← Hc]; exact dkey_encodeOp _ _ _ _ _ (by omega)
  refine ⟨?_, Hdk ▸ Hi.2⟩
  rw [← logHist_opsOf l0]
  exact (logHist_prefix _ _ HQ).trans (by rw [logHist_opsOf]; exact logHist_prefix _ _ Hlap)

end proof

end kv
end EtcdGrove
end Perennial
