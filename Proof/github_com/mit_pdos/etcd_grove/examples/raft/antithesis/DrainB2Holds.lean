/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E: **raft's durable state at the disk
after a synchronous write** (`StorageHolds`, `loopRestB2`'s, `restartRaft`'s): from the disk at the
loop head's durable state, a `Ready`'s write without a snapshot (`saveW`, from `base0`) leaves the disk
at the `Ready`'s durable state (`readyDurable`); the write's commit at least the disk's (commits only
grow: `AntSim.commit_reachD`) keeps the lowest restart commit (`wcommit`) below the disk's. The
etcdserver WAL's `walSave_holds`, without snapshots.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Phases

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **The disk after a synchronous write holds the `Ready`'s durable state**: from the disk `dk` at the
durable state `D` (`StorageHolds`), the write of the hard state `oh` (none: the disk's) and the entries
`es` (`saveW`, continuing the log: `SaveOk`) at the `Ready`'s hard state `H` (`oh`'s, or the disk's)
leaves the disk at `readyDurable D H none es`, given the write's commit at least the disk's. -/
theorem storageHolds_saveW (D : RaftState) (dk : AntSim.DurW) (H : HardStateM)
    (oh : Option HardStateM) (es : List EntryM)
    (h0 : StorageHolds D (diskContents dk))
    (hoh : oh.getD (HardStateM.mk dk.term dk.vote dk.commit) = H)
    (hok : SaveOk dk es)
    (hc : uint.Z dk.commit ≤ uint.Z H.Commit') :
    StorageHolds (readyDurable D H none es) (diskContents (saveW dk oh es)) := by
  obtain ⟨hb, ht, he, hT, hV, -, hw, -, -, -⟩ := h0
  simp only [diskContents, base0, StorContents.commit] at hb ht he hT hV hw
  have hbz : uint.Z D.base.index' = 0 := by
    have : uint.Z (W64 0) = 0 := rfl
    have : 0 ≤ uint.Z D.base.index' := Int.natCast_nonneg _
    omega
  have hbi : D.base.index' = W64 0 := by
    apply BitVec.eq_of_toNat_eq
    have : uint.Z D.base.index' = ((D.base.index').toNat : Int) := rfl
    have : (D.base.index').toNat = 0 := by omega
    simpa using this
  have hents : dk.log = D.ents := by
    rw [he]; unfold RaftState.entsFrom; rw [hbz]; simp
  have hterm : ∀ l : List EntryM, plogTermAt D.base l (W64 0) = some D.base.term' := by
    intro l; unfold plogTermAt
    have : uint.Z (W64 0) = 0 := rfl
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)), ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
  have hbt : D.base.term' = W64 0 := by
    rw [hterm] at ht; exact Option.some.inj ht
  have hz : uint.Z (W64 0) = 0 := rfl
  have hzn : uint.nat (W64 0) = 0 := rfl
  have hfrom : ∀ S : RaftState, S.entsFrom base0 = S.ents := by
    intro S; unfold RaftState.entsFrom base0; simp only [hz]; simp
  cases es with
  | nil =>
    have hsave : saveW dk oh [] = ⟨H.Term', H.Vote', H.Commit', dk.log⟩ :=
      saveW_ready dk oh [] H _ hoh (fun _ => rfl) (fun _ h => by simp at h)
    rw [hsave]
    unfold StorageHolds readyDurable RaftState.next
    simp only [Option.map_none, diskContents, StorContents.b, StorContents.commit,
      Option.isSome_none, Bool.false_or, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false]
    refine ⟨by unfold base0; omega, by unfold base0; rw [hterm, hbt], ?_, trivial, trivial,
      by show uint.nat (W64 0) ≤ _; omega, ?_, Nat.le_refl _, by simp, ?_⟩
    · rw [hfrom]; simpa [appendEnts] using hents
    · have : uint.nat D.wcommit ≤ uint.nat dk.commit := hw
      have : uint.nat dk.commit ≤ uint.nat H.Commit' := by
        have h1 : uint.Z dk.commit = (uint.nat dk.commit : Int) := rfl
        have h2 : uint.Z H.Commit' = (uint.nat H.Commit' : Int) := rfl
        omega
      omega
    · exact fun h => h hbi
  | cons e0 t =>
    have hsave : saveW dk oh (e0 :: t) =
        ⟨H.Term', H.Vote', H.Commit', dk.log.take (uint.nat e0.Index' - 1) ++ e0 :: t⟩ :=
      saveW_ready dk oh _ H _ hoh (fun h => by simp at h)
        (fun e h => by simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at h; subst h; rfl)
    rw [hsave]
    have h1 := (hok e0 (by simp)).1
    have hi : uint.Z e0.Index' = (uint.nat e0.Index' : Int) := rfl
    unfold StorageHolds readyDurable RaftState.next
    simp only [Option.map_none, diskContents, StorContents.b, StorContents.commit,
      Option.isSome_none, Bool.false_or, List.isEmpty_cons, Bool.not_false, ite_true]
    refine ⟨by unfold base0; omega, by unfold base0; rw [hterm, hbt], ?_, trivial, trivial,
      by show uint.nat (W64 0) ≤ _; omega, Nat.le_refl _, Nat.le_refl _, by simp, fun h => absurd hbi h⟩
    rw [hfrom]
    simp only [appendEnts, plogTruncateAppend, hbz]
    have hd : ((0 : Int) + 1 - uint.Z e0.Index').toNat = 0 := by omega
    rw [hd, List.drop_zero]
    have hk : (uint.Z e0.Index' - 0 - 1).toNat = uint.nat e0.Index' - 1 := by omega
    show _ = List.take (uint.Z e0.Index' - 0 - 1).toNat D.ents ++ e0 :: t
    rw [hk, hents]

/-- **`storageHolds_saveW` at an iteration** (`loopRestB2`'s facts at `rs₂` after the write): from the
loop head's disk at the loop head's durable state, the `Ready`'s write (`oh` the disk's hard state or the
`Ready`'s, as `phsNext`) leaves the disk at the `Ready`'s durable state (`rs₂.dur`), its term within the
ceiling, given the `Ready`'s commit at least the disk's (`AntSim.commit_reachD`) and its term within the
ceiling (`rawNode_term_tc`). -/
theorem DrainIterB1.holds_saveW (γ : AntNames) (j : Fin γ.R.N) (I : DrainIterB1) (oh : Option HardStateM)
    (hok : I.OkB2 γ j) (h0 : StorageHolds I.rs.dur (diskContents I.v.dur))
    (hoh : oh.getD (HardStateM.mk I.v.dur.term I.v.dur.vote I.v.dur.commit) = phsNext I.rs.phs I.h)
    (hsv : SaveOk I.v.dur I.es) (hc : uint.Z I.v.dur.commit ≤ uint.Z I.r.p.commit)
    (htc : uint.Z I.r.p.term ≤ uint.Z I.rs.tc) :
    StorageHolds I.rs₂.dur (diskContents (saveW I.v.dur oh I.es)) ∧
      uint.Z I.rs₂.dur.term ≤ uint.Z I.rs₂.tc := by
  have hph : phsNext I.rs.phs I.h = HardStateM.mk I.r.p.term I.r.p.vote I.r.p.commit :=
    hok.2.2.2.2.1.2.1
  refine ⟨storageHolds_saveW I.rs.dur I.v.dur _ oh I.es h0 hoh hsv (by rw [hph]; exact hc), ?_⟩
  show uint.Z (phsNext I.rs.phs I.h).Term' ≤ uint.Z I.rs.tc
  rw [hph]; exact htc

end pure

end AntHarness
end EtcdGrove
end Perennial
