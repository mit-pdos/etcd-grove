/- Lean-first (no Rocq counterpart).

# The crash condition at a generation's start (`notes/wal-fsext-plan.md`, §2.2; W1 log)

`walAbs_crashOk_start`: a WAL whose names have nothing logged (its directory's `.wal` files kept by
every crash, `hj`) and whose segments are durable, with
nothing appended, meets its crash condition: a crash keeps the names (`RegionCrashed` of claims with
empty histories), every segment there is its bytes as they are (`durable_img`), so the reader reads
the WAL's records and stops (`tailStop`). W1 is not used.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CrashPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section start
variable [GooseExts]

/-- A file whose bytes are all durable (the run of `xs.map durB`, its size bounds the run's
length) comes back after a crash as `xs`. -/
theorem durable_img {om : OsMeta} {dq : DFrac} {xs : List w8} {f' : Fs.OsFile}
    (h : FileCrashedR om [(0, dq, xs.map durB)] (some f')) (hlo : om.lo = xs.length)
    (hhi : om.hi = xs.length) : f'.contents = xs := by
  obtain ⟨-, h1, h2, hrun, -⟩ := h f' rfl
  have hsz : f'.size = xs.length := by omega
  apply List.ext_getElem (by rw [contents_length, hsz])
  intro k hk1 hk2
  obtain ⟨s, hs⟩ | ⟨h0, -⟩ := hrun _ (List.mem_singleton_self _) k (by simpa using hk2) (by omega)
  rotate_left; · omega
  simp only [List.getElem_map, durB, List.mem_singleton, Prod.mk.injEq, Nat.zero_add] at hs
  simp [Fs.OsFile.contents, hs.1]

/-- A directory whose entries are those of `e`, by name, has the entries `e`. -/
theorem entsOf_eq_of_entry {m : Tree} {j : Ino} {e : Ents} (h : ∀ b, m.entry j b = e !! b) :
    entsOf m j = e := by
  apply GMap.map_eq; intro b
  have := h b
  unfold Tree.entry at this
  unfold entsOf
  cases hm : m !! j with
  | none => rw [hm] at this; simp only [Option.bind_none] at this; rw [← this]; rfl
  | some D => rw [hm] at this; simpa using this

/-- A claim whose history is empty: a crash leaves its names as at boot. -/
theorem valAfter_nil {h : NamesH} (hh : h.ents = []) (j : Ino) (K : Nat → Prop) (b : GoString) :
    h.valAfter j K b = h.boot !! b := by
  unfold NamesH.valAfter
  rw [hh]; rfl

/-- **The crash condition at a generation's start**: nothing logged on the WAL's names (each claim's
history empty, `RegionCrashed` then keeps them as they are), every byte of every segment durable and
nothing appended (`wr = so = z0`, the last segment's stream ending at `z0`), so every crash leaves the
files as they are; the static relation then gives the crash condition (the reader reads the WAL's
records, then stops). This is what the next generation's invariant needs (`walInv_crash`). -/
theorem walAbs_crashOk_start (C : WalCodec) (_hC : C.Ok) (Mr : WalMarshal) (d : WalDur)
    (lay : WalLay) (cl : List Claim) (n : Nat) (ents : Ents)
    (habs : WalAbsD C Mr d lay ents)
    (_hfit : RecsFit C (recsOfSegs C Mr d.metadata (segsOf (histM d) lay.cuts)))
    (hlog : ∀ c ∈ cl, c.2.2.ents = [])
    (hj : ∀ m', RegionCrashed cl n m' → walInos (entsOf m' lay.j) = walInos ents)
    (hr : ∃ N h, (lay.jr, N, h) ∈ cl ∧ N.Mem lay.nm ∧ h.boot !! lay.nm = some (.dir lay.j))
    (hdur : lay.wr = lay.so ∧ lay.wr = lay.z0 ∧
      lay.z0 = (segStream C Mr d lay.cuts lay.cuts.length).length)
    (hlast : ∀ g, lay.segs.getLast? = some g → g.bs = lay.old.map durB) :
    CrashOk C Mr d lay cl n := by
  intro m' fo hreg hfc hnamed _
  right
  have hents := hj m' hreg
  obtain ⟨K, -, -, hval⟩ := hreg
  obtain ⟨N, hN, hNm, hNin, hNb⟩ := hr
  have hjr : m'.entry lay.jr lay.nm = some (.dir lay.j) := by
    rw [hval _ hNm lay.nm hNin, valAfter_nil (hlog _ hNm)]
    exact hNb
  have hsorted := habs.cuts.2.1
  have hcutsLen := habs.cuts.2.2
  have hHm := habs.synced.1
  -- each segment's file is there, and holds its bytes
  have hfile : ∀ g ∈ lay.segs, ∀ xs, g.bs = xs.map durB → imgOf (fo g.ino) = xs := by
    intro g hg xs hxs
    have hn : g.ino ∈ walInos (entsOf m' lay.j) := by
      rw [hents, habs.names.1]; exact List.mem_map_of_mem hg
    obtain ⟨f', hf'⟩ := Option.isSome_iff_exists.1 (hnamed g hg hn)
    have hc := hfc g hg
    rw [hf'] at hc ⊢
    rw [hxs] at hc
    obtain ⟨-, -, hlo, hhi⟩ := habs.metas g hg
    rw [hxs, List.length_map] at hlo hhi
    exact durable_img hc hlo hhi
  refine ⟨0, d.H, hjr, List.length_pos_iff.2 habs.nonempty, ?_,
    ⟨d.H.length, hHm, Nat.le_refl _, Or.inl (List.take_length).symm⟩,
    Nat.le_trans habs.lastSynced hHm, ?_, ?_, ?_⟩
  · rw [hents, List.drop_zero]; exact habs.names.1
  · refine Nat.le_min.2 ⟨?_, Nat.le_trans (segStart_le_length hsorted _)
      (Nat.le_trans habs.lastSynced hHm)⟩
    rcases Nat.eq_zero_or_pos lay.first with h0 | h0
    · simp [h0, segStart]
    · rw [Nat.add_zero, ← habs.cut.1]; exact habs.cut.2 h0
  · intro k g hk hlt
    rw [List.drop_zero] at hk
    have hk1 : k + 1 < lay.segs.length := by omega
    exact hfile g (List.mem_of_getElem? hk) _ (by rw [habs.intact k g hk1 hk, Nat.add_zero])
  · intro g hg
    have hl := habs.last g hg
    obtain ⟨-, -, -, -, -, -, htake, -⟩ := hl
    have himg := hfile g (List.mem_of_getLast? hg) lay.old (hlast g hg)
    rw [himg]
    refine ⟨?_, ?_⟩
    · show segStream C Mr d lay.cuts lay.cuts.length <+: lay.old
      have e : segStream C Mr d lay.cuts lay.cuts.length = lay.old.take lay.z0 := by
        rw [← htake, hdur.2.2, List.take_length]
      rw [e]; exact List.take_prefix _ _
    · intro r len c'
      have := habs.tailStop hdur.2.2 r len c'
      rw [hdur.2.2] at this
      exact this

end start

end WalFs
end EtcdGrove
end Perennial

end
