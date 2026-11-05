/-
`elemRef.count` of a writer cursor stack's top (U6aa, `notes/bbolt-proof-plan.md`, "Writer reads at
a fraction"; for `Cursor.first_w`): on a path whose leaf page holds its bounds' entries, the count is
the leaf's (`leafCnt`): a node reference is the bucket's current leaf node there
(`WBridge.wStk_top`), a page reference reads `sLeafOK`'s page (a view page, or the inline root's
bytes, `wInlOwn`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.WFirstCount
public import Proof.go_etcd_io.bbolt.Read.PubWGet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace WFirst

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **The count of a writer stack's top**: its leaf's entries. -/
theorem wp_top_count
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (n : GoString) (bl : Loc)
    (rt : Nat) (ipg : List w8) (nl : Loc → Option (Loc × Nat)) (els0 : List elemRef)
    (e : elemRef) (pids : List Nat) (ptr : Loc) (hc : wCurCtx X n bl rt)
    (hp : sPathR nl X.v bl rt (els0 ++ [e]) pids)
    (hlo : sLeafOK X.v ipg (wEs X n) pids (els0 ++ [e])) :
  {{ wtxWQ (GF := GF) K tx r m q X ∗ ptr ↦ e ∗ wStkOwn r nl X.v rt ipg (els0 ++ [e]) }}
    (App (Val (ptr @!! go.GoType.PointerType elemRef.ty @!! go!"count")) (Val #()))
  {{ RET #(W64 (leafCnt X.v (wEs X n) pids (els0 ++ [e]) : Int)); wtxWQ K tx r m q X ∗ ptr ↦ e ∗
      ⌜leafCnt X.v (wEs X n) pids (els0 ++ [e]) < 2 ^ 63⌝ }} := by
  have hok := hc.1
  have hvw : viewWF X.v := hok.2.2.2.2.2.2.2
  obtain ⟨B, hB⟩ := PubW.bktLoc_rec X hok n bl hc.2.1
  have hpl : pids.length = els0.length + 1 := by have := hp.2.1; simpa using this
  obtain ⟨pid, hpid⟩ : ∃ pid, pids.getLast? = some pid := by
    cases h : pids.getLast? with
    | none => rw [List.getLast?_eq_none_iff] at h; subst h; simp at hpl
    | some p => exact ⟨p, rfl⟩
  have he : (els0 ++ [e]).getLast? = some e := by simp
  iintro %Φ ⟨Hw, He, #Hown⟩ HΦ
  unfold wStkOwn
  icases Hown with ⟨#Hnls, #Hinl⟩
  icases WBridge.wtxWQ_nodeLoc_agree K tx r m q X nl (els0 ++ [e]) $$ [Hw] with ⟨Hw, %Hag⟩
  · iframe; iframe #
  icases wtxWQ_cells_acc K tx r m q X $$ Hw with ⟨%Hbase0, Hcells0, Hwb0⟩
  ihave Hw := Hwb0 $$ Hcells0
  obtain ⟨ws, hL, hents, hcnt, hplain, hnode⟩ :=
    WBridge.wStk_top X n bl rt B hc hB Hbase0 nl _ pids hp Hag e pid he hpid
  by_cases hnn : e.node' = null
  · obtain ⟨pg, hpg, hplainp, hpe, hinlg⟩ := hlo e pid he hpid hnn
    have hcnt' : leafCnt X.v (wEs X n) pids (els0 ++ [e]) = pageCount pg := by
      unfold leafCnt; rw [← hpe]; simp [pgEnts, pageWs]
    have h16 : 16 ≤ pg.length := by
      by_cases hp0 : pid = 0
      · obtain ⟨-, -, -, g4, -⟩ := hinlg hp0
        exact g4
      · unfold leafPgAt at hpg; rw [if_neg hp0] at hpg
        have := (Read.viewWF_page X.v hvw pid pg hpg).2.2.1
        omega
    ihave #Hsrc0 : ∃ src, ⌜src ≠ Src.stale⌝ ∗ srcLoc X.v e.page' src pg $$ []
    · by_cases hp0 : pid = 0
      · subst hp0
        obtain ⟨rfl, -, rfl⟩ := WKVs.sPathR_pid0 nl X.v hvw bl rt els0 e pids hp hpid
        unfold leafPgAt at hpg; simp only [↓reduceIte, Option.some.injEq] at hpg
        subst hpg
        isimp only [List.nil_append] at Hinl
        iapply WKVs.wInlOwn_src X.v ipg e hnn
        iexact Hinl
      · unfold leafPgAt at hpg; rw [if_neg hp0] at hpg
        have hj := hp.2.2.2 els0.length e pid (by simp)
          (by rw [show els0.length = pids.length - 1 by omega, ← List.getLast?_eq_getElem?]; exact hpid)
        rw [(hj.2.1 hnn).2 hp0]
        iexists Src.view
        isplitr
        · ipureintro; intro h; cases h
        · iapply srcLoc_view_page X.v pid pg hpg
    icases Hsrc0 with ⟨%src, -, #Hsrc⟩
    wp_apply wp_count_page hCnt K tx r m q X ptr e src pg hnn h16 $$ [Hw He] as ⟨Hw, He⟩
    · iframe; iframe #
    rw [hcnt']
    iapply HΦ
    iframe
    ipureintro
    have : pageCount pg < 2 ^ 16 := by unfold pageCount; exact BitVec.isLt _
    omega
  · obtain ⟨-, rn, hrn, hrws, -⟩ := hnode hnn
    obtain ⟨-, B0, hB0, -, -, -, hnsl, -⟩ := PubW.bktLocalOK_of_wOK X hok bl B hB
    rw [hB] at hB0; cases hB0
    have hlv := hnsl _ rn hrn
    icases wtxWQ_node_len K tx r m q X bl B _ rn hB hrn hlv $$ Hw with ⟨Hw, %H63⟩
    wp_apply wp_count_node K tx r m q X bl B ptr e rn hB hnn hrn hlv $$ [Hw He] as ⟨Hw, He⟩
    · iframe
    rw [hrws, hcnt]
    iapply HΦ
    iframe
    ipureintro
    rw [← hcnt, ← hrws]; exact H63

end proof

end WFirst

end bbolt
end EtcdGrove
end Perennial
