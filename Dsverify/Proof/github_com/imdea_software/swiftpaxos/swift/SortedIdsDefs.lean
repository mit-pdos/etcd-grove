/-
The definitions, specs and lemmas of `SortedIds.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLogKey
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLeafDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Steps
public import Perennial.Spec.slices.SortFunc

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## Pure: `cmdIdLess`, `sortIds` -/

/-- `cmdIdLess` on Go command ids. -/
def swift.cmdIdLt (a b : swift.CommandId) : Bool :=
  decide (sint.Z a.ClientId' < sint.Z b.ClientId') ||
    (decide (a.ClientId' = b.ClientId') && decide (sint.Z a.SeqNum' < sint.Z b.SeqNum'))

theorem swift.cmdIdLt_toCmdId (a b : swift.CommandId) :
    swift.cmdIdLt a b = sp.CmdId.lt (swift.toCmdId a) (swift.toCmdId b) := by
  unfold swift.cmdIdLt sp.CmdId.lt swift.toCmdId
  simp

namespace sp

theorem CmdId.lt_iff' (a b : CmdId) : CmdId.lt a b = true ↔
    a.cl.toInt < b.cl.toInt ∨ (a.cl.toInt = b.cl.toInt ∧ a.seq.toInt < b.seq.toInt) := by
  simp [CmdId.lt, BitVec.toInt_inj]

theorem CmdId.nlt (a b : CmdId) : (!(CmdId.lt b a)) = true ↔
    ¬ (b.cl.toInt < a.cl.toInt ∨ (b.cl.toInt = a.cl.toInt ∧ b.seq.toInt < a.seq.toInt)) := by
  rw [← CmdId.lt_iff']; cases CmdId.lt b a <;> simp

theorem CmdId.lt_le_trans (a b c : CmdId) :
    (!(CmdId.lt b a)) = true → (!(CmdId.lt c b)) = true → (!(CmdId.lt c a)) = true := by
  rw [CmdId.nlt, CmdId.nlt, CmdId.nlt]; omega

theorem CmdId.le_total (a b : CmdId) : Bool.or (!(CmdId.lt b a)) (!(CmdId.lt a b)) = true := by
  cases hb : CmdId.lt b a <;> cases ha : CmdId.lt a b <;> simp
  have := (CmdId.lt_iff' b a).1 hb; have := (CmdId.lt_iff' a b).1 ha; omega

theorem CmdId.le_antisymm (a b : CmdId) :
    (!(CmdId.lt b a)) = true → (!(CmdId.lt a b)) = true → a = b := by
  rw [CmdId.nlt, CmdId.nlt]
  intro h1 h2
  have hc : a.cl = b.cl := BitVec.eq_of_toInt_eq (by omega)
  have hs : a.seq = b.seq := BitVec.eq_of_toInt_eq (by omega)
  cases a; cases b; simp_all

/-- `sortIds` of any enumeration is the one list sorted by `cmdIdLess` with its elements. -/
theorem sortIds_eq (L l' : List CmdId) (hp : List.Perm l' L)
    (hs : l'.Pairwise (fun a b => (!(CmdId.lt b a)) = true)) : sortIds L = l' := by
  unfold sortIds
  apply List.Perm.eq_of_pairwise (le := fun a b => (!(CmdId.lt b a)) = true)
  · intro a b _ _ h1 h2; exact CmdId.le_antisymm a b h1 h2
  · exact List.pairwise_mergeSort (fun a b c h1 h2 => CmdId.lt_le_trans a b c h1 h2)
      (fun a b => CmdId.le_total a b) L
  · exact hs
  · exact (List.mergeSort_perm L _).trans hp.symm

end sp

theorem swift.cmdIdLt_swo : slices.StrictWeakOrder (fun a b => swift.cmdIdLt a b = true) where
  strict_weak_order_irrefl x := by
    rw [swift.cmdIdLt_toCmdId, sp.CmdId.lt_iff']; omega
  strict_weak_order_trans x y z := by
    rw [swift.cmdIdLt_toCmdId, swift.cmdIdLt_toCmdId, swift.cmdIdLt_toCmdId, sp.CmdId.lt_iff',
      sp.CmdId.lt_iff', sp.CmdId.lt_iff']; omega
  strict_weak_order_equiv := by
    refine ⟨fun x => ?_, fun h => ⟨h.2, h.1⟩, fun {x y z} h1 h2 => ?_⟩
    · rw [swift.cmdIdLt_toCmdId, sp.CmdId.lt_iff']; omega
    · revert h1 h2
      simp only [swift.cmdIdLt_toCmdId, sp.CmdId.lt_iff']
      omega

/-! ## The Go functions -/

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]

abbrev swift.cmdIdLess.specI : Prop :=
  ∀ (a b : swift.CommandId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift }}
    (App (App (Val (@! swift.cmdIdLess)) (Val #a)) (Val #b))
  {{ RET #(swift.cmdIdLt a b); True }}

variable [swift.Assumptions] [slices.Assumptions]

abbrev swift.cmdIdCmp.specI : Prop :=
  ∀ (a b : swift.CommandId),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift }}
    (App (App (Val (@! swift.cmdIdCmp)) (Val #a)) (Val #b))
  {{ (r : w64), RET #r; ⌜sint.Z r < 0 ↔ swift.cmdIdLt a b = true⌝ }}

/-- `cmdIdCmp` implements `cmdIdLess` as `slices.SortFunc`'s comparator. -/
theorem swift.cmdIdCmp_implements (wp_cmdIdCmp : swift.cmdIdCmp.specI (hG := hG)) :
    isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ⊢
      slices.cmpImplements (E := swift.CommandId) (fun a b => swift.cmdIdLt a b = true)
        (functions swift.cmdIdCmp []) := by
  iintro #Hi
  unfold slices.cmpImplements
  iintro %x %y
  imodintro
  iintro %Φ - HΦ
  wp_apply wp_cmdIdCmp
  iapply HΦ

/-- `sortedIds(m)`: the keys of the map `m` (of `kept`), sorted by `cmdIdLess`: as the model's
`sortIds` of any enumeration of them. The map's size is at most `2^62` (`slices.SortFunc`'s
bound; the caller's `kept` is bounded by its reports). -/
abbrev swift.sortedIds.specI : Prop :=
  ∀ (m : Loc) (mk : GMap swift.CommandId Loc) (dq : DFrac),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      m ↦${dq} mk ∗ ⌜GMap.size mk ≤ 2 ^ 62⌝ }}
    (App (Val (@! swift.sortedIds)) (Val #m))
  {{ (sl : GoSlice) (ids : List swift.CommandId), RET #sl; m ↦${dq} mk ∗ sl ↦* ids ∗
      ⌜ids.Nodup ∧ (∀ k, k ∈ ids ↔ (mk !! k).isSome) ∧
        ∀ L : List sp.CmdId, List.Perm L (ids.map swift.toCmdId) →
          sp.sortIds L = ids.map swift.toCmdId⌝ }}

end specs

end Perennial.github_com.imdea_software.swiftpaxos
