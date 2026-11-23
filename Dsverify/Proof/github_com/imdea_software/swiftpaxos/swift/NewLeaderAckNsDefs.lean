/-
The definitions, specs and lemmas of `NewLeaderAckNs.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecSync
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RepsOkInv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.WriterSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncFits
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.MsgRep
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SyncSeq
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.GhostSteps2

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## Pure -/

theorem swift.LView.computed_locAt (w : swift.LView) (b' : Nat) (o : List sp.CmdId) (b : Nat) :
    (w.computed b' o).locAt b = if b = b' then o else w.locAt b := by
  unfold swift.LView.computed swift.LView.locAt
  by_cases h : b = b'
  · subst h; simp
  · simp [h, Ne.symm h]

theorem swift.localOkS_computed {N r : Nat} {ld : Bool} {v : swift.RunV} {M : Option sp.SyncMsg}
    {w : swift.LView} {b' : Nat} (o : List sp.CmdId) (h : swift.localOkS N r ld v M w b')
    (hb : w.2.1 < b') : swift.localOkS N r ld v M (w.computed b' o) b' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have e : ∀ b, b ≠ b' → (w.computed b' o).locAt b = w.locAt b := fun b hb' => by
    rw [swift.LView.computed_locAt, if_neg hb']
  have hc : (w.computed b' o).2.1 = w.2.1 := rfl
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, ?_, ?_, h11⟩
  · rw [hc, e _ (by omega)]; exact h8
  · rw [hc, e _ (by omega)]; exact h9
  · intro b o' hb1 hb2 hmem
    change (b, o') ∈ (b', o) :: w.2.2.2 at hmem
    rcases List.mem_cons.mp hmem with e' | e'
    · exact hb2 (congrArg Prod.fst e')
    · exact h10 b o' hb1 hb2 e'

/-- An `MSync` lists at most the reports' entries (its ids are distinct reported ids). -/
theorem sp.recoverSync_len (N : Nat) (reps : List (Nat × sp.Report))
    (hnd : ((sp.recoverSync N reps).map Prod.fst).Nodup) :
    (sp.recoverSync N reps).length ≤ (reps.flatMap (·.2.entries)).length := by
  have hsub : (sp.recoverSync N reps).map Prod.fst ⊆ (reps.flatMap (·.2.entries)).map (·.id) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    obtain ⟨a, ha, re, hre, h1, -⟩ := sp.recoverSync_cmd N reps p hp
    exact List.mem_map.mpr ⟨re, List.mem_flatMap.mpr ⟨a, ha, hre⟩, h1⟩
  have := (List.subperm_of_subset hnd hsub).length_le
  simpa using this

section ghost
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

instance swift.syncSent_persistent (ls : Loc) (me bl : w32) (M : sp.SyncMsg) :
    Persistent (swift.syncSent ls me bl M) := by
  unfold swift.syncSent; infer_instance

/-- The run loop's state with its view taken out (to step the node state). -/
theorem swift.runStS_view (γ : sp.Names) (γv : GName) (rp : Loc) (N r : Nat) (ld : Bool)
    (v : swift.RunV) (M : Option sp.SyncMsg) (bs hd : sp.Seq) (w : swift.LView) (b' : Nat)
    (o : List sp.CmdId) (hb : w.2.1 < b') :
    swift.runStS γ γv rp N r ld v M bs hd w b' ⊢
      ghostVar γv (1 : Qp).half w ∗ ⌜swift.localOkS N r ld v M w b'⌝ ∗
      (ghostVar γv (1 : Qp).half (w.computed b' o) -∗
        swift.runStS γ γv rp N r ld v M bs hd (w.computed b' o) b') := by
  unfold swift.runStS
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, Hw, #Hlb, %Hok⟩
  iframe Hw
  isplitr
  · ipureintro; exact Hok.1
  iintro Hw
  rw [show (w.computed b' o).2.1 = w.2.1 from rfl]
  iframe
  iframe #
  ipureintro
  exact ⟨swift.localOkS_computed o Hok.1 hb, Hok.2⟩

/-- The run loop's state with its ballot field taken out (`recoveredSync` reads it). -/
theorem swift.runStS_ballot (γ : sp.Names) (γv : GName) (rp : Loc) (N r : Nat) (ld : Bool)
    (v : swift.RunV) (M : Option sp.SyncMsg) (bs hd : sp.Seq) (w : swift.LView) (b' : Nat) :
    swift.runStS γ γv rp N r ld v M bs hd w b' ⊢
      typedPointsto (swift.fld rp go!"ballot") v.ballot (DFrac.own (1 : Qp).half.half) ∗
      ⌜swift.localOkS N r ld v M w b'⌝ ∗
      (typedPointsto (swift.fld rp go!"ballot") v.ballot (DFrac.own (1 : Qp).half.half) -∗
        swift.runStS γ γv rp N r ld v M bs hd w b') := by
  unfold swift.runStS
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15, H16, Hw, #Hlb, %Hok⟩
  iframe H1
  isplitr
  · ipureintro; exact Hok.1
  iintro H1
  iframe
  iframe #
  ipureintro; exact Hok

end ghost

/-! ## Specs -/

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

/-- **`r.handleNewLeaderAckNs(lm, msgs)`** (the handler of `newLeaderAckNs`'s quorum): the new
leader `r` of `b'` (recovering in `b'`, without a row of `b'`), with the reports `reps` of a
majority (`reported` for `b'`), ends as `handleSync` of `recoverSync N reps` leaves it. Round 47
(sv-swb, 45-b, D61 (1)): `handleSync.specIR`'s persistent `PC`, passed through. -/
abbrev swift.Replica.handleNewLeaderAckNs.specI (EpR : GMap swift.CommandId Loc → IProp netDistGF)
    (EpS : sp.SyncMsg → List sp.CmdId → IProp netDistGF) (DF : Nat → Loc → IProp netDistGF)
    (PS : Nat → GMap GoString GoInterface → IProp netDistGF)
    (γ : sp.Names) (γc γm γl γw γv γd γe γo : GName) (n : swift.SyncN) (rp rr : Loc)
    (PC : IProp netDistGF) : Prop :=
  ∀ (qs : Loc) (N r k : Nat) (me : w32)
    (ld : Bool) (v : swift.RunV) (M0 : Option sp.SyncMsg) (bs hd : sp.Seq) (w : swift.LView)
    (lm : GoInterface) (msl : GoSlice) (ms : List GoInterface) (reps : List (Nat × sp.Report))
    (b' : Nat),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.slices ∗
      swift.runCtxD γ γc γm γl γw γv γe γo (n.sn N r) n.γdl rp N r k ∗
      inv swift.nodeN (swift.nodeInvD γ γv γe γo (n.sn N r) k) ∗
      swift.sendCtxN γ γc γm rp N me ∗
      swift.fld rp go!"Replica" ↦□ rr ∗ replica.fld rr go!"N" ↦□ (W64 N) ∗
      replica.fld rr go!"Id" ↦□ me ∗ swift.fld rp go!"qs" ↦□ qs ∗ replica.quorum.isQS qs N ∗
      swift.syncCtx γ N r n rp ∗ □ PC ∗ swift.runReader rp n.γdl ∗
      swift.runStS γ γv rp N r ld v M0 bs hd w b' ∗
      (if w.2.2.1 then EpR v.propsM else swift.epStopped n γe γd DF PS rp rr) ∗
      swift.syncFieldsOwn rp ∗ swift.syncSendCtx γ γc γm rp N ∗
      encoding.gob.codecSet (GF := netDistGF) ∗
      msl ↦*□ ms ∗ swift.acksIs ms reps ∗ ([∗list] p ∈ reps, sp.reported γ p.1 b' p.2) ∗
      ⌜sp.isMajority N (reps.map Prod.fst) ∧ sp.rid me = r ∧ sp.leaderOf N b' = r ∧
        w.1 = b' ∧ 0 < b' ∧ b' < 2 ^ 31 ∧ w.2.2.1 = false ∧ (∀ o, (b', o) ∉ w.2.2.2) ∧
        w.2.1 < b' ∧ 0 ≤ sint.Z me⌝ }}
    (App (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"handleNewLeaderAckNs"))
      (Val #lm)) (Val #msl))
  {{ RET #(); swift.runReader rp n.γdl ∗
      ∃ (v' : swift.RunV) (w' : swift.LView),
        swift.runSt γ γv rp N r true v' (some (sp.recoverSync N reps))
          (sp.syncSeq (sp.recoverSync N reps)) [] w' ∗
        EpS (sp.recoverSync N reps) (sp.syncOrder (sp.recoverSync N reps)) ∗
        swift.syncFieldsOwnE rp ∗
        ⌜w'.1 = b' ∧ w'.2.1 = b' ∧ w'.2.2.1 = true⌝ }}

end specs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

end proof

end Perennial.github_com.imdea_software.swiftpaxos
