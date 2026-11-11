/-
`elemRef.count` of the reference `pageNode` returns for a branch's child (U6aa, `notes/bbolt-proof-plan.md`,
"Writer reads at a fraction"; for `Cursor.last_w`'s `nextRef.count()`): its logical entries' number,
from a live node's entries or the view page's header (`WLast.child_ref`'s facts).
-/
module

public import Proof.go_etcd_io.bbolt.Read.WFirstCount

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace WLast

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A child reference's count**: its entries `ws`, fewer than `2 ^ 63`. -/
theorem wp_count_ref
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (bl : Loc) (B : BRec)
    (ptr : Loc) (e : elemRef) (ws : List WEntry) (c : Nat) (pgc : List w8)
    (hB : X.t.bs !! bl = some B)
    (hnode : e.node' ≠ null → ∃ rn, B.ns !! e.node' = some rn ∧ e.node' ∈ X.live ∧ rn.ws = ws)
    (hpage : e.node' = null → e.page' = pageLoc X.v c ∧ X.v.pages !! c = some pgc ∧
      ws = pageWs pgc ∧ 16 ≤ pgc.length) :
  {{ wtxWQ (GF := GF) K tx r m q X ∗ ptr ↦ e }}
    (App (Val (ptr @!! go.GoType.PointerType elemRef.ty @!! go!"count")) (Val #()))
  {{ RET #(W64 (ws.length : Int)); wtxWQ K tx r m q X ∗ ptr ↦ e ∗ ⌜ws.length < 2 ^ 63⌝ }} := by
  iintro %Φ ⟨Hw, He⟩ HΦ
  by_cases hnn : e.node' = null
  · obtain ⟨hloc, hpg, hws, h16⟩ := hpage hnn
    ihave #Hsrc : srcLoc X.v e.page' Src.view pgc $$ []
    · rw [hloc]; iapply srcLoc_view_page X.v c pgc hpg
    wp_apply WFirst.wp_count_page hCnt K tx r m q X ptr e Src.view pgc hnn h16 $$ [Hw He]
      as ⟨Hw, He⟩
    · iframe; iframe #
    have hl : ws.length = pageCount pgc := by rw [hws, pageWs_length]
    rw [hl]
    iapply HΦ
    iframe
    ipureintro
    have : pageCount pgc < 2 ^ 16 := by unfold pageCount; exact BitVec.isLt _
    omega
  · obtain ⟨rn, hrn, hlv, hrws⟩ := hnode hnn
    icases wtxWQ_node_len K tx r m q X bl B _ rn hB hrn hlv $$ Hw with ⟨Hw, %H63⟩
    wp_apply WFirst.wp_count_node K tx r m q X bl B ptr e rn hB hnn hrn hlv $$ [Hw He] as ⟨Hw, He⟩
    · iframe
    rw [hrws]
    iapply HΦ
    iframe
    ipureintro
    rw [← hrws]; exact H63

end proof

end WLast

end bbolt
end EtcdGrove
end Perennial
