/-
The persistent part of a writer's search stack (U6aa, `notes/bbolt-proof-plan.md`, "Writer reads at
a fraction"; for the public `Seek`'s writer case): a logical stack `lPath` (what `seek_w` leaves)
has its node references' registry fragments (`nlFrags`, the bridge's registry entries) and, at the
inline root, the bucket's inline page's bytes at its page reference (`WFirst.root_own`): its
`wStkOwn` over the writer's registry (`nlX`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.WFirstRoot
public import Proof.go_etcd_io.bbolt.Read.WBridge

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace WSeek

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common Write WBridge
  WGoFirst

section iprop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The node references' registry fragments of a stack whose nodes are registered. -/
theorem wtxWQ_nodeLocs (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) :
    ∀ els : List elemRef, (∀ e ∈ els, e.node' ≠ null → ∃ y, X.nloc !! e.node' = some y) →
    wtxWQ (GF := GF) K tx r m q X ⊢ wtxWQ K tx r m q X ∗ [∗list] e ∈ els, nodeLoc r (nlX X) e
  | [], _ => by
    iintro Hw; iframe Hw; iapply BigSepL.bigSepL_nil.2; iempintro
  | a :: t, h => by
    iintro Hw
    icases wtxWQ_nodeLocs K tx r m q X t (fun e he => h e (List.mem_cons_of_mem _ he)) $$ Hw
      with ⟨Hw, Ht⟩
    by_cases hn : a.node' = null
    · iframe Hw
      iapply (BigSepL.bigSepL_cons (Φ := fun _ e => nodeLoc (GF := GF) r (nlX X) e)).2
      iframe Ht
      unfold nodeLoc; rw [if_pos hn]; iempintro
    · obtain ⟨y, hy⟩ := h a (List.mem_cons_self ..) hn
      icases wtxWQ_nlFrag K tx r m q X a.node' y hy $$ Hw with ⟨Hw, #Hf⟩
      iframe Hw
      iapply (BigSepL.bigSepL_cons (Φ := fun _ e => nodeLoc (GF := GF) r (nlX X) e)).2
      iframe Ht
      unfold nodeLoc; rw [if_neg hn]
      iexists y; iframe #; ipureintro; exact hy

/-- **A search stack's persistent part** (`wStkOwn`): its node references' registry fragments, and
at the inline root its page reference's bytes (the bucket's inline page). -/
theorem wtxWQ_lPath_own (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX)
    (n : GoString) (bl : Loc) (rt : Nat) (B : BRec) (hc : wCurCtx X n bl rt)
    (hB : X.t.bs !! bl = some B)
    (hmax : ∀ id pg, X.v.pages !! id = some pg → id * 4096 < 0xFFFFFFFFFFFF)
    (hbase : 0 < X.v.base.addr) (els : List elemRef) (ps : List w64) (hp : lPath X bl els ps) :
    wtxWQ (GF := GF) K tx r m q X ⊢ wtxWQ K tx r m q X ∗ wStkOwn r (nlX X) X.v rt B.ipg els := by
  obtain ⟨hpath, -, -, -⟩ :=
    lPath_wStk X n bl B hc.1 hc.2.1 hc.2.2.2.2 hc.2.2.1 hB hbase els ps hp
  have hreg : ∀ e ∈ els, e.node' ≠ null → ∃ y, X.nloc !! e.node' = some y := by
    intro e he hn
    obtain ⟨j, hj, hej⟩ := List.getElem_of_mem he
    have hjp : j < (ps.map (·.toNat)).length := by rw [hpath.2.1]; exact hj
    exact ⟨_, (hpath.2.2.2 j e _ (by rw [List.getElem?_eq_getElem hj, hej])
      (List.getElem?_eq_getElem hjp)).1 hn⟩
  unfold wStkOwn
  iintro Hw
  icases wtxWQ_nodeLocs K tx r m q X els hreg $$ Hw with ⟨Hw, Hn⟩
  iframe Hn
  cases els with
  | nil => iframe Hw; unfold wInlOwn; iempintro
  | cons e0 t =>
    have hI : wInlOwn (GF := GF) X.v rt B.ipg (e0 :: t) = wInlOwn X.v rt B.ipg [e0] := rfl
    rw [hI]
    by_cases hnn : e0.node' = null
    · -- the root page reference: `refAt`'s page case
      obtain ⟨-, -, hhd, hstep⟩ := hp
      obtain ⟨p0, hp0⟩ : ∃ p0, ps.head? = some p0 := ⟨_, hhd⟩
      have hpe : p0 = B.ib.root' := by
        rw [hhd] at hp0; cases hp0; simp [WX.rootPid, hB]
      have hps0 : ps[0]? = some p0 := by
        cases ps with
        | nil => cases hp0
        | cons a _ => simpa using hp0
      obtain ⟨⟨B', hB', hra⟩, -⟩ := hstep 0 e0 p0 (by simp) hps0
      rw [hB] at hB'; cases hB'
      rw [hpe] at hra
      have hcl := wOK_bktClean X hc.1 bl B hB
      have hres : resolve B B.ib.root' = none := by
        cases hr : resolve B B.ib.root' with
        | none => rfl
        | some l =>
          rw [hr] at hra
          exfalso; apply (show l ≠ null from ?_); rw [← hra]; exact hnn
          by_cases h0 : B.ib.root' = W64 0
          · unfold resolve at hr; rw [if_pos h0] at hr
            by_cases hrn : B.bv.rootNode' = null
            · rw [if_pos hrn] at hr; cases hr
            · rw [if_neg hrn] at hr; cases hr; exact hrn
          · rw [resolve_tree B _ h0] at hr; exact (hcl.2.2.2.2.1 _ l hr).1
      rw [hres] at hra
      icases WFirst.root_own K tx r m q X n bl rt B hc hB hmax e0 (fun h => absurd hnn h)
        (by rw [hres]; exact hra) $$ Hw with ⟨Hw, Ho⟩
      unfold wStkOwn
      icases Ho with ⟨-, #Hi⟩
      iframe Hw; iframe #
    · iframe Hw
      rw [show wInlOwn (GF := GF) X.v rt B.ipg [e0] = iprop(emp) by
        simp only [wInlOwn, hnn, and_false, ↓reduceIte]]
      iempintro

end iprop

end WSeek

end bbolt
end EtcdGrove
end Perennial
