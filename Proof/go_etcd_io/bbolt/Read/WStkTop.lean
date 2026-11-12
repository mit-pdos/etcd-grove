/-
A writer cursor's stack top (U6aa, `notes/bbolt-proof-plan.md`, "Writer reads at a fraction"):
what `keyValue`, `next` and `prev` read at the top of a `boltCurDef` writer stack. Its leaf
position's logical entries are plain, are the bucket's within the path's bounds (`leafCnt` of them),
and a node reference at the top is the bucket's current leaf node there (`wStk_top`, over
`Read/WStkLeaf`'s current references and `Read/WBridge`); the registry fragments of the stack's
node references agree with the writer's registry (`wtxWQ_nodeLoc_agree`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.WStkLeaf
public import Proof.go_etcd_io.bbolt.Read.WQ

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace WBridge

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common Write Ents LeafT

section stkTop
variable [GooseExts]

/-- **The top of a writer cursor's stack** (pure): its leaf position holds the plain entries
`entsIn (wEs X n) (pathBnd …)` of the logical tree, and a node reference there is the bucket's
current leaf node. -/
theorem wStk_top (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (B : BRec)
    (hc : wCurCtx X n bl rt) (hB : X.t.bs !! bl = some B) (hbase : 0 < X.v.base.addr)
    (nl : Loc → Option (Loc × Nat)) (els : List elemRef) (pids : List Nat)
    (hp : sPathR nl X.v bl rt els pids)
    (hnl : ∀ e ∈ els, e.node' ≠ null → nl e.node' = X.nloc !! e.node')
    (e : elemRef) (pid : Nat) (he : els.getLast? = some e) (hpid : pids.getLast? = some pid) :
    ∃ ws, ltree X bl (W64 (pid : Int)) = some (true, ws) ∧
      ws.map (fun w => (w.key, w.value)) = entsIn (wEs X n) (pathBnd X.v pids els) ∧
      ws.length = leafCnt X.v (wEs X n) pids els ∧ (∀ w ∈ ws, ¬ isBktFlag w.flags) ∧
      (e.node' ≠ null → resolve B (W64 (pid : Int)) = some e.node' ∧
        ∃ rn, B.ns !! e.node' = some rn ∧ rn.ws = ws ∧ rn.nv.isLeaf' = true) := by
  obtain ⟨hok, hb, hnlc, hroot, hbr⟩ := hc
  obtain ⟨hlp, hlt⟩ := sPathR_lPath X n bl rt B ⟨hok, hb, hnlc, hroot, hbr⟩ hB nl els pids hp
  have hlen : pids.length = els.length := hp.2.1
  obtain ⟨-, -, hbnd, -⟩ := curRefs_index X B pids els hlen
  have hrt : (pids.map fun (p : Nat) => W64 (p : Int)).map (·.toNat) = pids := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id pids]
    apply List.map_congr_left
    intro p hp'
    have := hlt p hp'
    simp only [Function.comp, id]
    simp; omega
  obtain ⟨-, -, hents, hplain⟩ := lPath_wStk X n bl B hok hb hbr hnlc hB hbase _ _ hlp
  rw [hrt, hbnd] at hents
  have hpos : 0 < els.length := by
    cases els with
    | nil => exact absurd rfl hp.1
    | cons _ _ => simp
  have hcl : (curRefs X B pids els).length = els.length := (curRefs_index X B pids els hlen).2.1
  have hlast : (pids.map fun (p : Nat) => W64 (p : Int)).getLast? = some (W64 (pid : Int)) := by
    rw [List.getLast?_map, hpid]; rfl
  have hlj : (pids.map fun (p : Nat) => W64 (p : Int))[els.length - 1]? = some (W64 (pid : Int)) := by
    rw [show els.length - 1 = (pids.map fun (p : Nat) => W64 (p : Int)).length - 1 by simp [hlen],
      ← List.getLast?_eq_getElem?]
    exact hlast
  obtain ⟨-, lf, ws, hL, -, hleaf⟩ := hlp.2.2.2 (els.length - 1) _ _
    (List.getElem?_eq_getElem (by omega)) hlj
  have := hleaf (by omega)
  subst this
  have hll : lLeaf X bl (pids.map fun (p : Nat) => W64 (p : Int)) = ws := by
    unfold lLeaf; rw [hlast]; simp only [hL]
  rw [hll] at hents hplain
  refine ⟨ws, hL, hents, ?_, hplain, ?_⟩
  · unfold leafCnt; rw [← hents, List.length_map]
  · intro hnn
    have he' : els[els.length - 1]? = some e := by rw [← List.getLast?_eq_getElem?]; exact he
    have hpj : pids[els.length - 1]? = some pid := by
      rw [show els.length - 1 = pids.length - 1 by omega, ← List.getLast?_eq_getElem?]; exact hpid
    obtain ⟨h1, -⟩ := hp.2.2.2 _ e pid he' hpj
    have hx := h1 hnn
    rw [hnl e (List.mem_of_getElem? he') hnn] at hx
    have hres := nodeRef_current X n bl rt B ⟨hok, hb, hnlc, hroot, hbr⟩ hB _ pid hnn hx
    refine ⟨hres, ?_⟩
    unfold ltree at hL
    rw [hB] at hL
    simp only [hres] at hL
    cases hrn : B.ns !! e.node' with
    | none => rw [hrn] at hL; cases hL
    | some rn =>
      rw [hrn] at hL
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hL
      exact ⟨rn, rfl, hL.2, hL.1⟩

end stkTop

section stkTopI
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The registry fragments of a list of stack elements agree with the registry's auth. -/
theorem nodeLocs_agree (r : TxReg) (q : Qp) (M : GMap Loc (Loc × Nat))
    (nl : Loc → Option (Loc × Nat)) :
    ∀ els : List elemRef, ghostMapAuth (GF := GF) r.n.nl q M ∗ ([∗list] e ∈ els, nodeLoc r nl e) ⊢
      ghostMapAuth r.n.nl q M ∗ ⌜∀ e ∈ els, e.node' ≠ null → nl e.node' = M !! e.node'⌝
  | [] => by
    iintro ⟨Ha, -⟩
    iframe
    ipureintro; intro e he; cases he
  | a :: t => by
    iintro ⟨Ha, Ht⟩
    icases (BigSepL.bigSepL_cons (Φ := fun _ e => nodeLoc (GF := GF) r nl e)).1 $$ Ht with ⟨Ha1, Ht⟩
    icases nodeLocs_agree r q M nl t $$ [Ha Ht] with ⟨Ha, %Ht⟩
    · iframe
    unfold nodeLoc
    by_cases hn : a.node' = null
    · rw [if_pos hn]
      iframe
      ipureintro
      intro e he hne
      rcases List.mem_cons.1 he with rfl | he'
      · exact absurd hn hne
      · exact Ht e he' hne
    · rw [if_neg hn]
      icases Ha1 with ⟨%y, %hy, #Hf⟩
      ihave %Hl := ghost_map_lookup $$ Ha Hf
      iframe
      ipureintro
      intro e he hne
      rcases List.mem_cons.1 he with rfl | he'
      · rw [hy, Hl]
      · exact Ht e he' hne

/-- **A writer stack's node references agree with the writer's registry** (out of `wtxWQ`). -/
theorem wtxWQ_nodeLoc_agree (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX)
    (nl : Loc → Option (Loc × Nat)) (els : List elemRef) :
    wtxWQ (GF := GF) K tx r m q X ∗ ([∗list] e ∈ els, nodeLoc r nl e) ⊢
      wtxWQ K tx r m q X ∗ ⌜∀ e ∈ els, e.node' ≠ null → nl e.node' = X.nloc !! e.node'⌝ := by
  unfold wtxWQ wtxCoreQ nlAuth
  iintro ⟨⟨⟨#Hpkg, #Hcore, %Hr, #Hreg, Hh, Hfills, Hbk, ⟨Hnl, #Hf⟩, Hdb, Hview, Hst⟩, Hcells,
    Hmap⟩, Hels⟩
  icases nodeLocs_agree r q X.nloc nl els $$ [Hnl Hels] with ⟨Hnl, %Hag⟩
  · iframe
  iframe; iframe #
  isplitr
  · ipureintro; exact Hr
  ipureintro; exact Hag

end stkTopI

end WBridge

end bbolt
end EtcdGrove
end Perennial
