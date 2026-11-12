/-
`Cursor.prev` of a writer's cursor (U6aa, `notes/bbolt-proof-plan.md`, "Writer reads at a
fraction"): the stack's persistent part kept by the up-loop's truncation and move
(`wStkOwn_trunc`), and the leaf count's bound (`leafCnt_lt`: a page's count, or a live node's
entries, below `2 ^ 63`), with no code run.
-/
module

public import Proof.go_etcd_io.bbolt.Read.WFirstTop
public import Proof.go_etcd_io.bbolt.Read.WPrevPure

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace WPrev

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

omit hos in
/-- **The up-loop's stack** (truncated above level `E.length`, moved there) keeps the persistent
part. -/
theorem wStkOwn_trunc (r : TxReg) (nl : Loc → Option (Loc × Nat)) (v : View) (rt : Nat)
    (ipg : List w8) (E T : List elemRef) (e e' : elemRef) (hn : e'.node' = e.node')
    (hpg : e'.page' = e.page') :
    wStkOwn (GF := GF) r nl v rt ipg (E ++ e :: T) ⊢ wStkOwn r nl v rt ipg (E ++ [e']) := by
  have hnl : nodeLoc (GF := GF) r nl e' = nodeLoc r nl e := by unfold nodeLoc; rw [hn]
  have hinl : wInlOwn (GF := GF) v rt ipg (E ++ [e']) = wInlOwn v rt ipg (E ++ e :: T) := by
    cases E with
    | nil => simp only [List.nil_append, wInlOwn]; rw [hn, hpg]
    | cons a t => rfl
  unfold wStkOwn
  rw [hinl]
  iintro ⟨Hn, Hi⟩
  isplitl [Hn]
  · iapply (BigSepL.bigSepL_snoc (Φ := fun _ e => nodeLoc (GF := GF) r nl e)).2
    icases (BigSepL.bigSepL_append (Φ := fun _ e => nodeLoc (GF := GF) r nl e)).1 $$ Hn
      with ⟨HE, Het⟩
    icases (BigSepL.bigSepL_cons (Φ := fun k e => nodeLoc (GF := GF) r nl e)).1 $$ Het
      with ⟨He, -⟩
    rw [hnl]
    isplitl [HE]
    · iexact HE
    · iexact He
  · iexact Hi

/-- **A writer path's leaf count is below `2 ^ 63`**: a page's count (`sLeafOK`), or the live
leaf node's entries (`WBridge.wStk_top`). -/
theorem leafCnt_lt (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (n : GoString)
    (bl : Loc) (rt : Nat) (ipg : List w8) (nl : Loc → Option (Loc × Nat)) (els : List elemRef)
    (pids : List Nat) (hc : wCurCtx X n bl rt)
    (hp : sPathR nl X.v bl rt els pids) (hlo : sLeafOK X.v ipg (wEs X n) pids els) :
    wtxWQ (GF := GF) K tx r m q X ∗ wStkOwn r nl X.v rt ipg els ⊢
      wtxWQ K tx r m q X ∗ ⌜leafCnt X.v (wEs X n) pids els < 2 ^ 63⌝ := by
  have hok := hc.1
  obtain ⟨B, hB⟩ := PubW.bktLoc_rec X hok n bl hc.2.1
  obtain ⟨els0, e, rfl⟩ : ∃ els0 e, els = els0 ++ [e] := by
    rcases List.eq_nil_or_concat els with h | ⟨L, b, h⟩
    · exact absurd h hp.1
    · exact ⟨L, b, by simpa using h⟩
  have hpl : pids.length = els0.length + 1 := by have := hp.2.1; simpa using this
  obtain ⟨pid, hpid⟩ : ∃ pid, pids.getLast? = some pid := by
    cases h : pids.getLast? with
    | none => rw [List.getLast?_eq_none_iff] at h; subst h; simp at hpl
    | some p => exact ⟨p, rfl⟩
  have he : (els0 ++ [e]).getLast? = some e := by simp
  iintro ⟨Hw, #Hown⟩
  unfold wStkOwn
  icases Hown with ⟨#Hnls, #Hinl⟩
  icases WBridge.wtxWQ_nodeLoc_agree K tx r m q X nl (els0 ++ [e]) $$ [Hw] with ⟨Hw, %Hag⟩
  · iframe; iframe #
  icases wtxWQ_cells_acc K tx r m q X $$ Hw with ⟨%Hbase0, Hcells0, Hwb0⟩
  ihave Hw := Hwb0 $$ Hcells0
  obtain ⟨ws, hL, hents, hcnt, hplain, hnode⟩ :=
    WBridge.wStk_top X n bl rt B hc hB Hbase0 nl _ pids hp Hag e pid he hpid
  by_cases hnn : e.node' = null
  · obtain ⟨pg, hpg, -, hpe, -⟩ := hlo e pid he hpid hnn
    have hcnt' : leafCnt X.v (wEs X n) pids (els0 ++ [e]) = pageCount pg := by
      unfold leafCnt; rw [← hpe]; simp [pgEnts, pageWs]
    iframe
    ipureintro
    have : pageCount pg < 2 ^ 16 := by unfold pageCount; exact BitVec.isLt _
    omega
  · obtain ⟨-, rn, hrn, hrws, -⟩ := hnode hnn
    obtain ⟨-, B0, hB0, -, -, -, hnsl, -⟩ := PubW.bktLocalOK_of_wOK X hok bl B hB
    rw [hB] at hB0; cases hB0
    have hlv := hnsl _ rn hrn
    icases wtxWQ_node_len K tx r m q X bl B _ rn hB hrn hlv $$ Hw with ⟨Hw, %H63⟩
    iframe
    ipureintro
    rw [← hcnt, ← hrws]; exact H63

end proof

end WPrev

end bbolt
end EtcdGrove
end Perennial
