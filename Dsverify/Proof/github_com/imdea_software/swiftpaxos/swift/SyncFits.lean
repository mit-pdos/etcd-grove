/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/SyncFits.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The new leader's `MSync` fits a gob frame, and what `MSync.Marshal` gives with its codec facts
discharged (round 18, sv-swc; notes/prove-swift.md §22):

* `swift.syncWireOf`, `swift.syncFits`, `swift.syncCands` (moved here from MarshalSync.lean).
* `swift.syncFits_of`: an `MSync` of at most `6 · 2^25` entries, whose values are shorter than
  `2^16` and whose dependency lists are at most one longer than it, fits (`Msg.wf`).
* `sp.lkAlong_length`, `sp.lkAlong_deps_len`, `sp.recoverSync_deps_len`: `recoverSync`'s
  dependency lists (`lkDeps` along its order) are at most one longer than it.
* `swift.MSync.marshalHG`: `MSync.Marshal` at gob's package and `codecSet` (the kit codec's
  `kitCodecOk` discharged at the link; proved from `swift.MSync.marshalHP`, MarshalSync.lean).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RecDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.WriterSpecs
public import Dsverify.Spec.encoding.gob.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace sp

theorem lkDeps_len (s : Seq) (c : Cmd) : (lkDeps s c).length ≤ s.length + 1 := by
  unfold lkDeps
  simp only []
  have h1 : (((s.filter (fun p => p.2.key == c.key)).reverse.find? (fun p => p.2.isPut)).toList.map
      Prod.fst).length ≤ 1 := by
    cases ((s.filter (fun p => p.2.key == c.key)).reverse.find? (fun p => p.2.isPut)) <;> simp
  have h2 : ((((s.filter (fun p => p.2.key == c.key)).reverse.takeWhile
      (fun p => !p.2.isPut)).map Prod.fst).reverse).length ≤ s.length := by
    simp only [List.length_reverse, List.length_map]
    have h3 := (List.takeWhile_sublist (fun p : CmdId × Cmd => !p.2.isPut)
      (l := (s.filter (fun p => p.2.key == c.key)).reverse)).length_le
    have h4 := (List.filter_sublist (p := fun p : CmdId × Cmd => p.2.key == c.key) (l := s)).length_le
    try rw [List.length_reverse] at h3
    omega
  split <;> (try simp only [List.length_append]) <;> omega

theorem lkAlong_fold (cs : List (CmdId × Cmd)) (s : Seq) (out : List (CmdId × Cmd × List CmdId))
    (K : Nat) (hK : s.length + cs.length ≤ K) (hout : ∀ p ∈ out, p.2.2.length ≤ K + 1) :
    (∀ p ∈ (cs.foldl (fun (acc : Seq × List (CmdId × Cmd × List CmdId)) p =>
        (acc.1 ++ [p], acc.2 ++ [(p.1, p.2, lkDeps acc.1 p.2)])) (s, out)).2,
        p.2.2.length ≤ K + 1) ∧
      (cs.foldl (fun (acc : Seq × List (CmdId × Cmd × List CmdId)) p =>
        (acc.1 ++ [p], acc.2 ++ [(p.1, p.2, lkDeps acc.1 p.2)])) (s, out)).2.length =
        out.length + cs.length := by
  induction cs generalizing s out with
  | nil => exact ⟨hout, by simp⟩
  | cons q cs ih =>
    simp only [List.foldl_cons]
    have := ih (s ++ [q]) (out ++ [(q.1, q.2, lkDeps s q.2)])
      (by simp only [List.length_append, List.length_cons, List.length_nil] at hK ⊢; omega)
      (by
        intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact hout p hp
        · simp only [List.mem_singleton] at hp
          subst hp
          have := lkDeps_len s q.2
          simp only [List.length_cons] at hK
          simp only []
          omega)
    refine ⟨this.1, ?_⟩
    rw [this.2]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem lkAlong_length (cs : List (CmdId × Cmd)) : (lkAlong cs).length = cs.length := by
  unfold lkAlong
  have := (lkAlong_fold cs [] [] cs.length (by simp) (by simp)).2
  simpa using this

theorem lkAlong_deps_len (cs : List (CmdId × Cmd)) :
    ∀ p ∈ lkAlong cs, p.2.2.length ≤ (lkAlong cs).length + 1 := by
  rw [lkAlong_length]
  unfold lkAlong
  exact (lkAlong_fold cs [] [] cs.length (by simp) (by simp)).1

/-- `recoverSync`'s dependency lists are at most one longer than it. -/
theorem recoverSync_deps_len (N : Nat) (reps : List (Nat × Report)) :
    ∀ p ∈ recoverSync N reps, p.2.2.length ≤ (recoverSync N reps).length + 1 := by
  unfold recoverSync
  exact lkAlong_deps_len _

theorem flatten_map_len_le {α β : Type} (l : List α) (f : α → List β) (B : Nat)
    (h : ∀ a ∈ l, (f a).length ≤ B) : ((l.map f).flatten).length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      Nat.succ_mul]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    omega

end sp

section pure
variable [go_gctx : GoGlobalContext]

/-- The wire listing of `M` (in `M`'s order). -/
def swift.syncWireOf (me bl : w32) (M : sp.SyncMsg) : sp.SyncWire :=
  ⟨me, bl, some (M.map (fun p => (p.1, sp.phCOMMIT))), some (M.map (fun p => (p.1, p.2.1))),
    some (M.map (fun p => (p.1, p.2.2)))⟩

end pure

/-- `M`'s encoding fits a gob frame (item 5 of MarshalSync.lean's header: the size bound, a
premise of `marshalHP`; `swift.syncFits_of`). -/
def swift.syncFits (me bl : w32) (M : sp.SyncMsg) : Prop :=
  (sp.Msg.sync (swift.syncWireOf me bl M)).wf

/-- The messages `MSync.Marshal` may write for an `MSync` listing `M` (Go's map order is chosen
at the write): a wire `MSync` with the sender's fields listing `M`, well formed. -/
def swift.syncCands (me bl : w32) (M : sp.SyncMsg) (mm : sp.Msg) : Prop :=
  ∃ m : sp.SyncWire, mm = .sync m ∧ m.rep = me ∧ m.bal = bl ∧ sp.syncWireOk m M ∧
    (sp.Msg.sync m).wf

/-- **An `MSync` fits a frame** when it has at most `6 · 2^25` entries (the registered
commands' bound, D13), values shorter than `2^16` (`Cmd.wf`, C20) and dependency lists at most
one longer than it. -/
theorem swift.syncFits_of (me bl : w32) (M : sp.SyncMsg) (hn : M.length ≤ 6 * 2 ^ 25)
    (hv : ∀ p ∈ M, p.2.1.val.length < 2 ^ 16) (hd : ∀ p ∈ M, p.2.2.length ≤ M.length + 1) :
    swift.syncFits me bl M := by
  unfold swift.syncFits sp.Msg.wf sp.SyncWire.wf swift.syncWireOf
  have e1 := sp.flatten_map_len_le M
    ((fun p : sp.CmdId × w64 => sp.cCmdId p.1 ++ sp.cU64 p.2) ∘ (fun p => (p.1, sp.phCOMMIT)))
    24 (fun p _ => by simp [sp.cCmdId, sp.cI32, sp.cU64, u64Le_length])
  have e2 := sp.flatten_map_len_le M
    ((fun p : sp.CmdId × sp.Cmd => sp.cCmdId p.1 ++ sp.cCmd p.2) ∘ (fun p => (p.1, p.2.1)))
    (40 + 2 ^ 16) (fun p hp => by
      have := hv p hp
      simp only [Function.comp, sp.cCmdId, sp.cCmd, sp.cBytes, sp.cI32, sp.cU64,
        List.length_append, u64Le_length]
      omega)
  have e3 := sp.flatten_map_len_le M
    ((fun p : sp.CmdId × List sp.CmdId => sp.cCmdId p.1 ++ sp.cList sp.cCmdId p.2) ∘
      (fun p => (p.1, p.2.2)))
    (24 + 16 * (6 * 2 ^ 25 + 1)) (fun p hp => by
      have := hd p hp
      have e := sp.flatten_map_len_le p.2.2 sp.cCmdId 16
        (fun _ _ => by simp [sp.cCmdId, sp.cI32, sp.cU64, u64Le_length])
      simp only [Function.comp, sp.cCmdId, sp.cList, sp.cI32, sp.cU64,
        List.length_append, u64Le_length] at e ⊢
      have : p.2.2.length * 16 ≤ (6 * 2 ^ 25 + 1) * 16 := Nat.mul_le_mul_right _ (by omega)
      omega)
  simp only [sp.KitVal.encode, sp.SyncWire.cEnc, sp.cMapOpt, sp.cList, sp.cI32, sp.cU64,
    List.length_append, List.length_cons, u64Le_length, List.length_map, List.map_map] at e1 e2 e3 ⊢
  have m1 : M.length * 24 ≤ 6 * 2 ^ 25 * 24 := Nat.mul_le_mul_right _ hn
  have m2 : M.length * (40 + 2 ^ 16) ≤ 6 * 2 ^ 25 * (40 + 2 ^ 16) := Nat.mul_le_mul_right _ hn
  have m3 : M.length * (24 + 16 * (6 * 2 ^ 25 + 1)) ≤
      6 * 2 ^ 25 * (24 + 16 * (6 * 2 ^ 25 + 1)) := Nat.mul_le_mul_right _ hn
  omega

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

/-- **`MSync.Marshal`** with gob's package and `codecSet` (change log C18; the kit codec's
`kitCodecOk` discharged at the link: `swift.MSync.marshal_proofG`, MarshalSync.lean): an `MSync`
as `recoveredSync` built it (`syncSent`) whose listing fits a frame marshals as a wire `MSync`
listing `M`, chosen at the write (`marshalOkP`; Go's map order). -/
abbrev swift.MSync.marshalHG : Prop :=
  ∀ (ls : Loc) (me bl : w32) (M : sp.SyncMsg),
    isPkgInit (PROP := IProp netDistGF) pkg_id.encoding.gob ∗
      encoding.gob.codecSet (GF := netDistGF) ∗
      swift.syncSent ls me bl M ∗ ⌜swift.syncFits me bl M⌝ ⊢
    sp.marshalOkP (interface.mkOk (go.GoType.PointerType swift.MSync.ty) #ls)
      (swift.syncCands me bl M) iprop(True)

end specs

end Perennial.github_com.imdea_software.swiftpaxos
