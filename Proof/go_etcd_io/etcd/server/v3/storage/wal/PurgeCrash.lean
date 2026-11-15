/- Lean-first (no Rocq counterpart).

# A purge's crash side, on `CrashTo` (unit `locks`, session 6; `notes/wal-units/locks.md`)

Pure. `purgeRound` removes segment names without a directory fsync, so until the next one (a `cut`'s, or
`Create`'s) a crash may bring back any suffix of the removed-not-durable segments `pg` (the round's removes
are sequential, so a crash keeps a prefix of them: session 4). The design: the crash condition is stated on
the **layout as of the last directory sync**, `unpurge pg lay` (the removed-not-durable segments put back in
front), which a purge does not change (`unpurge_purge`). `CrashTo`'s own `q` (the crash keeps the segments
from the `q`-th on) then covers every suffix of `pg`:

* `unpurge_purge`: a purge of `lay`'s first segment `g0` moves it from `lay` into `pg`: `unpurge (pg ++ [g0])
  (purgeLay lay) = unpurge pg lay`;
* `crashTo_unpurge`: `CrashTo` of `lay` gives `CrashTo` of `unpurge pg lay` (the crash keeps none of `pg`):
  so a step that makes the removals durable can still conclude on `lay` alone;
* `crashTo_purgeD`: `CrashTo` does not read the read position `cut`, and only bounds by `pur` from above, so
  a purge's raise (`walPurgeD`) keeps it;
* `crashTo_dropFirst`: a crash that keeps the removal of the `t`-th segment of the full layout (and so every
  earlier removal) is, with that name back, a crash keeping the segments from `t` on; it keeps them from
  `t + 1` on, given the purge's bound on `pur`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PurgePure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.SegPre

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc

section pure
variable [GooseExts]

/-- **The layout as of the last directory sync**: `lay` with the removed-not-durable segments `pg` put
back in front. -/
def unpurge (pg : List SegG) (lay : WalLay) : WalLay :=
  { lay with first := lay.first - pg.length, segs := pg ++ lay.segs }

@[simp] theorem unpurge_nil (lay : WalLay) : unpurge [] lay = lay := by
  simp [unpurge]

/-- **A purge does not move the layout as of the last directory sync.** -/
theorem unpurge_purge (pg : List SegG) (lay : WalLay) (g0 : SegG) (gs : List SegG)
    (hs : lay.segs = g0 :: gs) (hf : pg.length ≤ lay.first) :
    unpurge (pg ++ [g0]) (purgeLay lay) = unpurge pg lay := by
  cases lay
  simp only [unpurge, purgeLay] at hs hf ⊢
  subst hs
  simp only [List.length_append, List.length_singleton, List.tail_cons, List.append_assoc,
    List.singleton_append, WalLay.mk.injEq, and_true, true_and]
  omega

theorem drop_len_append {α : Type} (pg l : List α) (q : Nat) : (pg ++ l).drop (pg.length + q) = l.drop q := by
  rw [List.drop_append]; simp

/-- **`CrashTo` of the layout gives it of the layout with `pg` put back** (a crash that keeps none of the
removed segments). -/
theorem crashTo_unpurge {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {m' : Tree}
    {fo : Ino → Option Fs.OsFile} (pg : List SegG) (hf : pg.length ≤ lay.first)
    (h : CrashTo C Mr d lay m' fo) : CrashTo C Mr d (unpurge pg lay) m' fo := by
  rcases h with h | ⟨q, I, hent, hq, hinos, hI, hlen, hst, hk, hlast⟩
  · exact Or.inl h
  refine Or.inr ⟨pg.length + q, I, hent, ?_, ?_, hI, hlen, ?_, ?_, ?_⟩
  · simp only [unpurge, List.length_append]; omega
  · simp only [unpurge]; rw [drop_len_append]; exact hinos
  · simp only [unpurge]
    have e : lay.first - pg.length + (pg.length + q) = lay.first + q := by omega
    rw [e]; exact hst
  · intro k g hg hlt
    simp only [unpurge] at hg hlt ⊢
    rw [drop_len_append] at hg
    have e : lay.first - pg.length + (pg.length + q) + k = lay.first + q + k := by omega
    rw [e] at hlt ⊢
    exact hk k g hg hlt
  · intro g hg
    have hne : lay.segs ≠ [] := by intro e; rw [e] at hq; simp at hq
    simp only [unpurge] at hg
    have e : (pg ++ lay.segs).getLast? = lay.segs.getLast? := by
      rw [List.getLast?_append]
      cases h' : lay.segs.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.1 h') hne
      | some _ => simp
    rw [e] at hg
    exact hlast g hg

/-- **A purge's raise keeps `CrashTo`** (it reads `pur` only as an upper bound, never `cut`). -/
theorem crashTo_purgeD {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay F : WalLay} {m' : Tree}
    {fo : Ino → Option Fs.OsFile} (p : Nat) (h : CrashTo C Mr d F m' fo) :
    CrashTo C Mr (walPurgeD d lay p) F m' fo := by
  rcases h with ⟨hn, h⟩ | ⟨q, I, hent, hq, hinos, hI, hlen, hst, hk, hlast⟩
  · exact Or.inl ⟨hn, h⟩
  refine Or.inr ⟨q, I, hent, hq, hinos, hI, hlen, ?_, hk, hlast⟩
  simp only [walPurgeD]
  exact Nat.le_trans hst (by omega)

/-- **`CrashTo` does not read the read position**: the crash condition of the full layout can be stated
for the WAL with `cut` at the full layout's first segment (where `WalAbsD` puts it). -/
theorem crashTo_cut_iff {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {F : WalLay} {m' : Tree}
    {fo : Ino → Option Fs.OsFile} (c : Nat) :
    CrashTo C Mr { d with cut := c } F m' fo ↔ CrashTo C Mr d F m' fo := Iff.rfl

/-! ## The static relation of the full layout

The invariant keeps, besides `WalAbsD d lay ents` (the directory as it is), the static relation of the full
layout `unpurge pg lay` for the WAL with `cut` at its first segment (`walFullD`), over the entries with the
removed-not-durable names back: what the crash proof's `crashTo_start` and the crash step lemmas take, applied
to the full layout instead of `lay`. -/

/-- The WAL with its read position at the full layout's first segment. -/
def walFullD (d : WalDur) (pg : List SegG) (lay : WalLay) : WalDur :=
  { d with cut := segStart lay.cuts (lay.first - pg.length) }

/-- `WalAbsD` reads `pur` only as an upper bound on `cut`. -/
theorem WalAbsD.pur_mono {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (h : WalAbsD C Mr d lay ents) {P : Nat} (hp : d.pur ≤ P) :
    WalAbsD C Mr { d with pur := P } lay ents :=
  { h with cut := ⟨h.cut.1, fun hf => Nat.le_trans (h.cut.2 hf) hp⟩ }

/-- With nothing removed, the full layout is the layout. -/
theorem walAbsD_full_nil {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (h : WalAbsD C Mr d lay ents) : WalAbsD C Mr (walFullD d [] lay) (unpurge [] lay) ents := by
  rw [unpurge_nil]
  show WalAbsD C Mr { d with cut := segStart lay.cuts (lay.first - 0) } lay ents
  rw [Nat.sub_zero, ← h.cut.1]
  exact h

/-- **A purge keeps the full layout's static relation** (the full layout does not move,
`unpurge_purge`; `pur` only rises). -/
theorem walAbsD_full_purge {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents0 : Ents}
    {pg : List SegG} {g0 : SegG} {gs : List SegG} (p : Nat)
    (h : WalAbsD C Mr (walFullD d pg lay) (unpurge pg lay) ents0) (hs : lay.segs = g0 :: gs)
    (hf : pg.length ≤ lay.first) :
    WalAbsD C Mr (walFullD (walPurgeD d lay p) (pg ++ [g0]) (purgeLay lay))
      (unpurge (pg ++ [g0]) (purgeLay lay)) ents0 := by
  rw [unpurge_purge pg lay g0 gs hs hf]
  have e : walFullD (walPurgeD d lay p) (pg ++ [g0]) (purgeLay lay) =
      { walFullD d pg lay with pur := max d.pur p } := by
    simp only [walFullD, walPurgeD, purgeLay, List.length_append, List.length_singleton]
    congr 2; omega
  rw [e]
  exact h.pur_mono (Nat.le_max_left _ _)

/-- **A crash that keeps the removal of the full layout's `t`-th segment**: `CrashTo` of the crash `m''`
with that segment's name back (whose WAL directory lists the segments from `t` on) gives `CrashTo` of `m'`
(listing them from `t + 1` on, the WAL directory at the same place), the segment ending at or before
`pur`. -/
theorem crashTo_dropFirst {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {F : WalLay} {m' m'' : Tree}
    {fo : Ino → Option Fs.OsFile} {t : Nat} (h : CrashTo C Mr d F m'' fo)
    (hc : F.cuts.Pairwise (· < ·)) (hF : F.first + F.segs.length = F.cuts.length + 1)
    (hent : m'.entry F.jr F.nm = some (.dir F.j))
    (hent'' : m''.entry F.jr F.nm = some (.dir F.j))
    (h'' : walInos (entsOf m'' F.j) = (F.segs.drop t).map (·.ino))
    (h' : walInos (entsOf m' F.j) = (F.segs.drop (t + 1)).map (·.ino))
    (ht : t + 1 < F.segs.length) (hpur : segStart F.cuts (F.first + (t + 1)) ≤ d.pur) :
    CrashTo C Mr d F m' fo := by
  rcases h with ⟨-, h⟩ | ⟨q, I, -, hq, hinos, hI, hlen, -, hk, hlast⟩
  · rw [hent''] at h; cases h
  have hqt : q = t := by
    have := congrArg List.length (hinos.symm.trans h'')
    simp only [List.length_map, List.length_drop] at this
    omega
  subst hqt
  refine Or.inr ⟨q + 1, I, hent, ht, h', hI, hlen, Nat.le_min.2 ⟨hpur, ?_⟩, ?_, hlast⟩
  · exact Nat.le_trans (segStart_le_length hc _) hlen
  · intro k g hg hlt
    have hg' : (F.segs.drop q)[k + 1]? = some g := by
      rw [List.getElem?_drop] at hg ⊢
      rw [← hg]; congr 1; omega
    have e : F.first + q + (k + 1) = F.first + (q + 1) + k := by omega
    have := hk (k + 1) g hg' (by omega)
    rw [e] at this
    exact this

end pure

end WalFs
end EtcdGrove
end Perennial

end
