/-
**Probe: `wsRecvOk` from what each response records at its send** (2026-11-04, before any ghost
work for `wsRecv_ok.law`). `notes/mvcc-api-invariants.md` §2 (`wsRecv`) says the consumer's view
holds, for each received response, pure facts and persistent ghost elements only. This file asks
whether the frozen pure guarantee `wsRecvOk` follows from such facts, with every other premise
one an invariant keeps under monotone ghost state (the notified log and the compaction revision
only grow; the registry only gains entries, never changes one; the cancelled set only grows; a
registration's stamp is the sent count at its atomic step).

- `SentFact`: what a response records at its send (pure data); `SentFact.holds pre f`: what is
  true of it at the send, `pre` the responses sent before it.
- `SentInv σ S D F`: the premises (the chain of facts, the lower bounds, registry agreement, the
  cancelled set's monotonicity, the progress stamps).
- `wsRecvOk_of_sent`: `SentInv σ S D F → wsRecvOk σ S (F.map (·.r))` (and the unbundled form).
- `sentFacts_snoc`: a send keeps `SentInv`; `SentInv.take`: the received prefix keeps it; the
  other steps (`register`, `cancel`, `close`, the store's `notify`/`commit`/`compact`/`Restore`)
  keep it.

**Result (no `sorry`, no axiom beyond Lean's): every conjunct of `wsRecvOk` follows from pure facts
recorded at the sends.** What the facts had to be, against §2's wording:
- The cumulative delivery is `∃ hi ≤ |L|` (its watcher's kept events of `[lo, hi)`), not "up to the
  response's revision": a batched response (`eb.moreRev ≠ 0`, `watchable_store.go:397-401`) carries
  the events below `moreRev` at `Revision: curRev`. Only a progress response's (no events, no
  compaction) `hi` is its revision `+ 1`, a separate fact.
- "The events sent so far" is `recvEvs` of the **sent** prefix before the response (`pre`), with
  the response's own (`sentChain`); the received list is a prefix of the sent (`SentInv.take`).
- The `-1` response records its covered watchers with their registry info (`CovEntry`), the
  cancelled ones as ids (`dead`, each in the cancelled set `D`).
- Two premises beyond the four asked: `S.ws !! -1 = none` (in `registryAgree`; else conjunct 3's
  `r.id = id` case at `id = -1` asks a `-1` response for a watcher `-1`'s events), and `deadIn`
  (the recorded cancelled ids are in `D`).
- The steps' premises: a registration's stamp at least the **sent** count at its atomic step
  (`SentInv.register`'s `F.length ≤ w.k`, `F` the sent list: `wsSentLb`'s `k ≤ sent` is the other
  half); a `-1` send covers every watcher registered by then (`stampsAt S F.length`); `commit_mono`
  needs `MvccReachable σ` (no pending `[]`); `Restore` needs `σ.pending = none` (`restore_mono`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiState

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api
namespace probe

open go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## What a response records at its send -/

/-- A watcher a stream-wide (`-1`) progress response covers: its id and its registry info. -/
structure CovEntry where
  id : w64
  rg : WatchRange
  fs : List (EvM → Bool)
  lo : Nat

/-- **What a response records when it is sent** (§2): the response; its watcher's registry info
(the `ι.reg` element: range, filters, first revision; meaningless for a `-1` response); the
notified-log lower bound `L` and the compaction lower bound `c0` (the `γ.crevLb` fragment) at the
send; for a `-1` response, the watchers it covers (each with its registry element) and those
cancelled when it was sent (`ι.dead` elements). -/
structure SentFact where
  r : WResp
  rg : WatchRange
  fs : List (EvM → Bool)
  lo : Nat
  L : Log
  c0 : Int
  cov : List CovEntry
  dead : List w64

/-- The response's own shape against the bounds it was sent with (`wsRecvOk`'s first conjunct,
with `L` for the notified log and `c0` for the compaction revision). -/
def respShape (r : WResp) (L : Log) (c0 : Int) : Prop :=
  (∀ ev ∈ r.evs, sint.Z ev.kv.modRev ≤ sint.Z r.rev) ∧
  (r.compactRev = W64 0 → sint.nat r.rev < L.length) ∧
  (r.compactRev ≠ W64 0 → r.evs = [] ∧ r.id ≠ W64 (-1) ∧ r.rev = W64 0 ∧
    0 < sint.Z r.compactRev ∧ sint.Z r.compactRev ≤ c0) ∧
  (r.id = W64 (-1) → r.evs = [] ∧ r.compactRev = W64 0 ∧ 1 ≤ sint.Z r.rev) ∧
  (∀ ev ∈ r.evs, 0 < sint.Z ev.kv.modRev ∧
    (ev.del = false → 0 < sint.Z ev.kv.createRev ∧ 0 < sint.Z ev.kv.version))

/-- **What is true of a response at its send**, `pre` the responses sent before it: its shape;
the cumulative delivery of its watcher (while `onceUpTo L lo c0`, the watcher's events sent so
far, this response's included, are its kept events of `[lo, hi)` of `L`, some `hi`); a progress
response's (no events, no compaction) `hi` its revision `+ 1`; a `-1` response's coverage (each
covered watcher's events so far its kept events up to the response's revision). -/
def SentFact.holds (pre : List WResp) (f : SentFact) : Prop :=
  respShape f.r f.L f.c0 ∧
  (f.r.id ≠ W64 (-1) → onceUpTo f.L f.lo f.c0 →
    ∃ hi, hi ≤ f.L.length ∧
      recvEvs (pre ++ [f.r]) f.r.id = filtered f.fs (watchEvents f.L f.rg f.lo hi)) ∧
  (f.r.id ≠ W64 (-1) → f.r.evs = [] → f.r.compactRev = W64 0 → onceUpTo f.L f.lo f.c0 →
    recvEvs (pre ++ [f.r]) f.r.id =
      filtered f.fs (watchEvents f.L f.rg f.lo (sint.nat f.r.rev + 1))) ∧
  (f.r.id = W64 (-1) → ∀ c ∈ f.cov, onceUpTo f.L c.lo f.c0 →
    recvEvs (pre ++ [f.r]) c.id = filtered c.fs (watchEvents f.L c.rg c.lo (sint.nat f.r.rev + 1)))

/-! ## The premises -/

/-- Each fact holds of the responses sent before it (recorded at the send, constant after). -/
def sentChain (F : List SentFact) : Prop :=
  ∀ (j : Nat) (f : SentFact), F[j]? = some f → f.holds ((F.map SentFact.r).take j)

/-- The bounds a fact was sent with are below the store's state (`γ.rel`/`notifiedLb` and
`γ.crevLb` fragments). -/
def lbsOk (σ : MvccState) (F : List SentFact) : Prop :=
  ∀ f ∈ F, f.L <+: σ.notifiedLog ∧ f.c0 ≤ σ.crev

/-- The stream's state has the watcher `id` with this registry info (an `ι.reg` element). -/
def regAgree (S : StreamState) (id : w64) (rg : WatchRange) (fs : List (EvM → Bool)) (lo : Nat) :
    Prop :=
  ∃ w, S.ws !! id = some w ∧ w.rg = rg ∧ w.fs = fs ∧ w.lo = lo

/-- A fact's registry info agrees with the stream's state. -/
def factAgree (S : StreamState) (f : SentFact) : Prop :=
  (f.r.id ≠ W64 (-1) → regAgree S f.r.id f.rg f.fs f.lo) ∧
  (f.r.id = W64 (-1) → ∀ c ∈ f.cov, regAgree S c.id c.rg c.fs c.lo)

/-- **Registry agreement**: no watcher has the id `-1` (the stream's: `Watch` registers
`id ≠ -1`), and every fact's registry info is the stream's. -/
def registryAgree (S : StreamState) (F : List SentFact) : Prop :=
  S.ws !! W64 (-1) = none ∧ ∀ f ∈ F, factAgree S f

/-- **The cancelled set `D`** (`ι.dead`): each id in it a watcher of the stream, not live. -/
def deadMono (S : StreamState) (D : List w64) : Prop :=
  ∀ id ∈ D, ∃ w, S.ws !! id = some w ∧ w.live = false

/-- The ids a fact recorded cancelled are in the cancelled set (its elements persistent). -/
def deadIn (D : List w64) (F : List SentFact) : Prop :=
  ∀ f ∈ F, ∀ id ∈ f.dead, id ∈ D

/-- A `-1` response at `j` (stamp: the sent count) covers each watcher registered at a stamp at
most `j` (that is, registered before it was sent), or recorded it cancelled. -/
def stampsAt (S : StreamState) (j : Nat) (f : SentFact) : Prop :=
  f.r.id = W64 (-1) → ∀ id w, S.ws !! id = some w → w.k ≤ j →
    (∃ c ∈ f.cov, c.id = id) ∨ id ∈ f.dead

def stampsRecorded (S : StreamState) (F : List SentFact) : Prop :=
  ∀ (j : Nat) (f : SentFact), F[j]? = some f → stampsAt S j f

/-- **The premises, bundled.** -/
structure SentInv (σ : MvccState) (S : StreamState) (D : List w64) (F : List SentFact) : Prop where
  chain : sentChain F
  lbs : lbsOk σ F
  reg : registryAgree S F
  dead : deadMono S D
  deadIn : deadIn D F
  stamps : stampsRecorded S F

/-! ## Pure lemmas -/

theorem recvEvs_nil' (id : w64) : recvEvs [] id = [] := rfl

theorem recvEvs_snoc (rs : List WResp) (r : WResp) (id : w64) :
    recvEvs (rs ++ [r]) id = recvEvs rs id ++ (if r.id = id then r.evs else []) := by
  unfold recvEvs
  rw [List.filter_append]
  by_cases h : r.id = id <;> simp [h]

theorem onceUpTo_mono {L L' : Log} {lo : Nat} {c c' : Int} (hp : L <+: L') (hc : c ≤ c')
    (h : onceUpTo L' lo c') : onceUpTo L lo c := by
  intro r h1 h2
  by_cases hr : r < L.length
  · obtain ⟨T, rfl⟩ := hp
    have := h r h1 (by omega)
    simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hr] using this
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : L.length ≤ r)]

theorem sentChain_snoc (G : List SentFact) (f : SentFact) :
    sentChain (G ++ [f]) ↔ sentChain G ∧ f.holds (G.map SentFact.r) := by
  constructor
  · intro h
    refine ⟨fun j g hj => ?_, ?_⟩
    · have hjl : j < G.length := (List.getElem?_eq_some_iff.1 hj).1
      have := h j g (by rw [List.getElem?_append_left hjl]; exact hj)
      rwa [List.map_append, List.take_append_of_le_length (by simp; omega)] at this
    · have := h G.length f (by simp)
      rwa [List.map_append, List.take_append_of_le_length (by simp), List.take_of_length_le
        (by simp)] at this
  · rintro ⟨hG, hf⟩ j g hj
    rw [List.getElem?_append] at hj
    split at hj
    · rename_i hjl
      rw [List.map_append, List.take_append_of_le_length (by simp; omega)]
      exact hG j g hj
    · rename_i hjl
      rw [List.getElem?_singleton] at hj
      split at hj
      · rename_i hj0
        cases hj
        have : j = G.length := by omega
        subst this
        rw [List.map_append, List.take_append_of_le_length (by simp), List.take_of_length_le
          (by simp)]
        exact hf
      · cases hj

theorem sentChain_take (F : List SentFact) (n : Nat) (h : sentChain F) : sentChain (F.take n) := by
  intro j g hj
  rw [List.getElem?_take] at hj
  split at hj
  · rename_i hjn
    have e : ((F.take n).map SentFact.r).take j = (F.map SentFact.r).take j := by
      rw [List.map_take, List.take_take]; congr 1; omega
    rw [e]; exact h j g hj
  · cases hj

/-! ## The main result -/

/-- Induction on a list from its end. -/
theorem snoc_induction {α : Type _} {P : List α → Prop} (nil : P [])
    (snoc : ∀ l a, P l → P (l ++ [a])) : ∀ l, P l := by
  intro l
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact nil
  | cons a t ih => rw [List.reverse_cons]; exact snoc _ _ ih

private theorem fact_of_mem {F : List SentFact} {f : SentFact} (h : f ∈ F) :
    ∃ j : Nat, F[j]? = some f := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h
  exact ⟨j, by simp⟩

/-- Conjunct 2, by induction on the sent list (its last response for `id` decides). -/
theorem deliv_of_sent (σ : MvccState) (S : StreamState) :
    ∀ (F : List SentFact), sentChain F → lbsOk σ F → registryAgree S F →
    ∀ (id : w64) (w : WInfo), S.ws !! id = some w → onceUpTo σ.notifiedLog w.lo σ.crev →
      ∃ hi, hi ≤ σ.notifiedLog.length ∧
        recvEvs (F.map SentFact.r) id = filtered w.fs (watchEvents σ.notifiedLog w.rg w.lo hi) := by
  intro F
  induction F using snoc_induction with
  | nil =>
    intro _ _ _ id w _ _
    exact ⟨0, by omega, by rw [watchEvents_empty _ _ (by omega)]; rfl⟩
  | snoc G f ih =>
    intro hch hlb hreg id w hw hon
    rw [sentChain_snoc] at hch
    obtain ⟨hchG, hf⟩ := hch
    have hlbG : lbsOk σ G := fun g hg => hlb g (List.mem_append_left _ hg)
    have hregG : registryAgree S G := ⟨hreg.1, fun g hg => hreg.2 g (List.mem_append_left _ hg)⟩
    obtain ⟨hpf, hcf⟩ := hlb f (by simp)
    rw [List.map_append, List.map_singleton]
    by_cases hid : f.r.id = id
    · by_cases hneg : id = W64 (-1)
      · have hev : f.r.evs = [] := (hf.1.2.2.2.1 (hid.trans hneg)).1
        rw [recvEvs_snoc]
        simp only [hid, ↓reduceIte, hev, List.append_nil]
        exact ih hchG hlbG hregG id w hw hon
      · obtain ⟨w', hw', hrg, hfs, hlo⟩ := (hreg.2 f (by simp)).1 (hid ▸ hneg)
        rw [hid, hw] at hw'
        cases hw'
        have hon' : onceUpTo f.L f.lo f.c0 := hlo ▸ onceUpTo_mono hpf hcf hon
        obtain ⟨hi, hhi, heq⟩ := hf.2.1 (hid ▸ hneg) hon'
        refine ⟨hi, Nat.le_trans hhi hpf.length_le, ?_⟩
        rw [← hid, heq, ← hrg, ← hfs, ← hlo, watchEvents_prefix hpf _ hhi]
    · rw [recvEvs_snoc]
      simp only [hid, ↓reduceIte, List.append_nil]
      exact ih hchG hlbG hregG id w hw hon

/-- **`wsRecvOk` from the facts recorded at the sends.** -/
theorem wsRecvOk_of_sent' (σ : MvccState) (S : StreamState) (D : List w64) (F : List SentFact)
    (h : SentInv σ S D F) : wsRecvOk σ S (F.map SentFact.r) := by
  obtain ⟨hch, hlb, hreg, hdead, hdin, hst⟩ := h
  refine ⟨?_, deliv_of_sent σ S F hch hlb hreg, ?_⟩
  · -- conjunct 1: each response's shape
    intro r hr
    obtain ⟨f, hfF, rfl⟩ := List.mem_map.1 hr
    obtain ⟨j, hj⟩ := fact_of_mem hfF
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, -⟩ := hch j f hj
    obtain ⟨hpf, hcf⟩ := hlb f hfF
    refine ⟨fun hn => ?_, h1, fun hc => Nat.lt_of_lt_of_le (h2 hc) hpf.length_le,
      fun hc => ?_, h4, h5⟩
    · obtain ⟨w, hw, -⟩ := (hreg.2 f hfF).1 hn
      simp [hw]
    · obtain ⟨a, b, c, d, e⟩ := h3 hc
      exact ⟨a, b, c, d, Int.le_trans e hcf⟩
  · -- conjunct 3: progress
    intro j r id w hj hev hcr hw hon hcase
    rw [List.getElem?_map] at hj
    cases hFj : F[j]? with
    | none => rw [hFj] at hj; cases hj
    | some f =>
    rw [hFj] at hj
    cases hj
    have hfF : f ∈ F := List.mem_of_getElem? hFj
    have hf := hch j f hFj
    obtain ⟨hpf, hcf⟩ := hlb f hfF
    have htake : (F.map SentFact.r).take (j + 1) = (F.map SentFact.r).take j ++ [f.r] := by
      rw [List.take_add_one, List.getElem?_map, hFj]; rfl
    have hP : sint.nat f.r.rev + 1 ≤ f.L.length := hf.1.2.1 hcr
    rw [htake]
    rcases hcase with hid | ⟨hneg, hlive, hk⟩
    · have hneg : f.r.id ≠ W64 (-1) := by
        intro hn; rw [← hid, hn, hreg.1] at hw; cases hw
      obtain ⟨w', hw', hrg, hfs, hlo⟩ := (hreg.2 f hfF).1 hneg
      rw [hid, hw] at hw'
      cases hw'
      have hon' : onceUpTo f.L f.lo f.c0 := hlo ▸ onceUpTo_mono hpf hcf hon
      rw [← hid, hf.2.2.1 hneg hev hcr hon', ← hrg, ← hfs, ← hlo, watchEvents_prefix hpf _ hP]
    · rcases hst j f hFj hneg id w hw hk with ⟨c, hc, rfl⟩ | hd
      · obtain ⟨w', hw', hrg, hfs, hlo⟩ := (hreg.2 f hfF).2 hneg c hc
        rw [hw] at hw'
        cases hw'
        have hon' : onceUpTo f.L c.lo f.c0 := hlo ▸ onceUpTo_mono hpf hcf hon
        rw [hf.2.2.2 hneg c hc hon', ← hrg, ← hfs, ← hlo, watchEvents_prefix hpf _ hP]
      · obtain ⟨w', hw', hl⟩ := hdead id (hdin f hfF id hd)
        rw [hw] at hw'
        cases hw'
        rw [hlive] at hl
        cases hl

/-- **The probe's statement** (unbundled, as asked). -/
theorem wsRecvOk_of_sent (σ : MvccState) (S : StreamState) (D : List w64) (F : List SentFact) :
    (∀ f ∈ F, f.L <+: σ.notifiedLog ∧ f.c0 ≤ σ.crev) → sentChain F → registryAgree S F →
    deadMono S D → deadIn D F → stampsRecorded S F → wsRecvOk σ S (F.map SentFact.r) :=
  fun hlb hch hreg hd hdi hst => wsRecvOk_of_sent' σ S D F ⟨hch, hlb, hreg, hd, hdi, hst⟩

/-! ## The steps keep the premises -/

/-- **A send**: the new response's fact, true at its send (`holds` of the responses sent
before), with bounds below the store's state, registry info agreeing with the stream's, its
cancelled ids in the cancelled set, and (a `-1` response) every watcher registered by now covered
or cancelled. -/
theorem sentFacts_snoc (σ : MvccState) (S : StreamState) (D : List w64) (F : List SentFact)
    (f : SentFact) (h : SentInv σ S D F) (hf : f.holds (F.map SentFact.r))
    (hlb : f.L <+: σ.notifiedLog ∧ f.c0 ≤ σ.crev) (hag : factAgree S f)
    (hdi : ∀ id ∈ f.dead, id ∈ D) (hst : stampsAt S F.length f) :
    SentInv σ S D (F ++ [f]) := by
  obtain ⟨hch, hlbs, hreg, hdead, hdin, hsts⟩ := h
  refine ⟨(sentChain_snoc F f).2 ⟨hch, hf⟩, ?_, ⟨hreg.1, ?_⟩, hdead, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hlbs g hg
    · rw [List.mem_singleton.1 hg]; exact hlb
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hreg.2 g hg
    · rw [List.mem_singleton.1 hg]; exact hag
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hdin g hg
    · rw [List.mem_singleton.1 hg]; exact hdi
  · intro j g hj
    rw [List.getElem?_append] at hj
    split at hj
    · exact hsts j g hj
    · rename_i hjl
      rw [List.getElem?_singleton] at hj
      split at hj
      · cases hj
        have : j = F.length := by omega
        subst this
        exact hst
      · cases hj

/-- **The received prefix**: the consumer has received a prefix of what was sent. -/
theorem SentInv.take {σ S D F} (h : SentInv σ S D F) (n : Nat) : SentInv σ S D (F.take n) := by
  obtain ⟨hch, hlbs, hreg, hdead, hdin, hsts⟩ := h
  refine ⟨sentChain_take F n hch, fun g hg => hlbs g (List.mem_of_mem_take hg),
    ⟨hreg.1, fun g hg => hreg.2 g (List.mem_of_mem_take hg)⟩, hdead,
    fun g hg => hdin g (List.mem_of_mem_take hg), ?_⟩
  intro j g hj
  rw [List.getElem?_take] at hj
  split at hj
  · exact hsts j g hj
  · cases hj

theorem sentInv_nil (σ : MvccState) : SentInv σ wsStart [] [] :=
  ⟨fun j f h => by simp at h, fun f h => by simp at h, ⟨by simp [wsStart], fun f h => by simp at h⟩,
    fun id h => by simp at h, fun f h => by simp at h, fun j f h => by simp at h⟩

private theorem regAgree_register {S : StreamState} {id i : w64} {w : WInfo} {rg fs lo}
    (hnone : S.ws !! id = none) (h : regAgree S i rg fs lo) : regAgree (S.register id w) i rg fs lo := by
  obtain ⟨w', hw', h1, h2, h3⟩ := h
  have hne : id ≠ i := by rintro rfl; rw [hnone] at hw'; cases hw'
  exact ⟨w', by simp [StreamState.register, hne, hw'], h1, h2, h3⟩

/-- **A registration** (`Watch`'s update): a fresh id, not `-1`, at a stamp at least the sent
count (the count at the registration's atomic step). -/
theorem SentInv.register {σ S D F} (h : SentInv σ S D F) (id : w64) (w : WInfo)
    (hnone : S.ws !! id = none) (hneg : id ≠ W64 (-1)) (hk : F.length ≤ w.k) :
    SentInv σ (S.register id w) D F := by
  obtain ⟨hch, hlbs, hreg, hdead, hdin, hsts⟩ := h
  refine ⟨hch, hlbs, ⟨?_, fun f hf => ⟨fun hn => regAgree_register hnone ((hreg.2 f hf).1 hn),
      fun hn c hc => regAgree_register hnone ((hreg.2 f hf).2 hn c hc)⟩⟩, ?_, hdin, ?_⟩
  · simp [StreamState.register, hneg, hreg.1]
  · intro i hi
    obtain ⟨w', hw', hl⟩ := hdead i hi
    have hne : id ≠ i := by rintro rfl; rw [hnone] at hw'; cases hw'
    exact ⟨w', by simp [StreamState.register, hne, hw'], hl⟩
  · intro j f hj hn i w' hw' hk'
    by_cases he : id = i
    · subst he
      simp [StreamState.register] at hw'
      subst hw'
      have := (List.getElem?_eq_some_iff.1 hj).1
      omega
    · exact hsts j f hj hn i w' (by simpa [StreamState.register, he] using hw') hk'

private theorem cancel_lookup (S : StreamState) (id i : w64) :
    ∃ g : WInfo → WInfo, (∀ w, (g w).rg = w.rg ∧ (g w).fs = w.fs ∧ (g w).lo = w.lo ∧ (g w).k = w.k) ∧
      (S.cancel id).ws !! i = (S.ws !! i).map g ∧
      (i = id → ∀ w, (S.cancel id).ws !! i = some w → w.live = false) ∧
      (i ≠ id → (S.cancel id).ws !! i = S.ws !! i) := by
  unfold StreamState.cancel
  cases hS : S.ws !! id with
  | none =>
    refine ⟨fun w => w, fun _ => ⟨rfl, rfl, rfl, rfl⟩, by simp, ?_, fun _ => rfl⟩
    rintro rfl w hw; rw [hS] at hw; cases hw
  | some w0 =>
    by_cases he : i = id
    · subst he
      refine ⟨fun w => { w with live := false }, fun _ => ⟨rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
      · simp [hS]
      · intro _ w hw; simp at hw; subst hw; rfl
      · intro h; exact absurd rfl h
    · refine ⟨fun w => w, fun _ => ⟨rfl, rfl, rfl, rfl⟩, ?_, fun h => absurd h he, ?_⟩
      · simp [Ne.symm he]
      · intro _; simp [Ne.symm he]

/-- **A cancel** (`Cancel`'s update at its first check): the watcher, if any, not live and its id
in the cancelled set (an `ι.dead` element minted); an unknown id changes nothing. -/
theorem SentInv.cancel {σ S D F} (h : SentInv σ S D F) (id : w64) :
    SentInv σ (S.cancel id) (if (S.ws !! id).isSome then id :: D else D) F := by
  obtain ⟨hch, hlbs, hreg, hdead, hdin, hsts⟩ := h
  have hag : ∀ i rg fs lo, regAgree S i rg fs lo → regAgree (S.cancel id) i rg fs lo := by
    rintro i rg fs lo ⟨w, hw, h1, h2, h3⟩
    obtain ⟨g, hg, hl, -, -⟩ := cancel_lookup S id i
    obtain ⟨g1, g2, g3, -⟩ := hg w
    exact ⟨g w, by rw [hl, hw]; rfl, g1.trans h1, g2.trans h2, g3.trans h3⟩
  refine ⟨hch, hlbs, ⟨?_, fun f hf => ⟨fun hn => hag _ _ _ _ ((hreg.2 f hf).1 hn),
      fun hn c hc => hag _ _ _ _ ((hreg.2 f hf).2 hn c hc)⟩⟩, ?_, ?_, ?_⟩
  · obtain ⟨g, -, hl, -, -⟩ := cancel_lookup S id (W64 (-1))
    rw [hl, hreg.1]; rfl
  · have key : ∀ i, (∃ w, S.ws !! i = some w ∧ w.live = false) →
        ∃ w, (S.cancel id).ws !! i = some w ∧ w.live = false := by
      rintro i ⟨w, hw, hl⟩
      obtain ⟨g, -, hlk, hid, hne⟩ := cancel_lookup S id i
      by_cases he : i = id
      · exact ⟨g w, by rw [hlk, hw]; rfl, hid he _ (by rw [hlk, hw]; rfl)⟩
      · exact ⟨w, by rw [hne he, hw], hl⟩
    intro i hi
    split at hi
    · rename_i hs
      rcases List.mem_cons.1 hi with rfl | hi
      · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hs
        obtain ⟨g, -, hlk, hid, -⟩ := cancel_lookup S i i
        exact ⟨g w, by rw [hlk, hw]; rfl, hid rfl _ (by rw [hlk, hw]; rfl)⟩
      · exact key i (hdead i hi)
    · exact key i (hdead i hi)
  · intro f hf i hi
    have := hdin f hf i hi
    split
    · exact List.mem_cons_of_mem _ this
    · exact this
  · intro j f hj hn i w hw hk
    obtain ⟨g, hg, hlk, -, -⟩ := cancel_lookup S id i
    rw [hlk] at hw
    cases hS : S.ws !! i with
    | none => rw [hS] at hw; cases hw
    | some w0 =>
      rw [hS] at hw
      cases hw
      exact hsts j f hj hn i w0 hS (by rw [← (hg w0).2.2.2]; exact hk)

/-- **A stream's `Close`**: the watchers unchanged. -/
theorem SentInv.close {σ S D F} (h : SentInv σ S D F) : SentInv σ S.close D F := by
  obtain ⟨hch, hlbs, hreg, hdead, hdin, hsts⟩ := h
  exact ⟨hch, hlbs, hreg, hdead, hdin, hsts⟩

/-- A reachable state never has an empty pending revision. -/
theorem reach_pending_ne_nil : ∀ σ : MvccState, MvccReachable σ → σ.pending ≠ some [] := by
  intro σ h
  induction h with
  | start => simp [mvccStart]
  | notify σ pend _ _ _ _ =>
    simp only [MvccState.notify]
    split <;> simp_all
  | commit σ _ _ => simp [MvccState.commitPending]
  | compact σ r _ _ _ _ ih => exact ih

/-- The store's steps only extend the notified log and raise the compaction revision. -/
theorem lbsOk_mono {σ σ' : MvccState} {F : List SentFact} (hl : σ.notifiedLog <+: σ'.notifiedLog)
    (hc : σ.crev ≤ σ'.crev) (h : lbsOk σ F) : lbsOk σ' F :=
  fun f hf => ⟨(h f hf).1.trans hl, Int.le_trans (h f hf).2 hc⟩

theorem notify_mono (σ : MvccState) (pend : List Change) (hp : σ.pending = none) :
    σ.notifiedLog <+: (σ.notify pend).notifiedLog ∧ σ.crev ≤ (σ.notify pend).crev := by
  refine ⟨?_, Int.le_refl _⟩
  rw [MvccState.notify_notifiedLog]
  simp only [MvccState.notifiedLog, hp, commitLog]
  split
  · exact List.prefix_refl _
  · exact List.prefix_append _ _

theorem commit_mono (σ : MvccState) (hr : MvccReachable σ) :
    σ.notifiedLog <+: σ.commitPending.notifiedLog ∧ σ.crev ≤ σ.commitPending.crev := by
  refine ⟨?_, Int.le_refl _⟩
  have hne := reach_pending_ne_nil σ hr
  simp only [MvccState.commitPending, MvccState.notifiedLog, commitLog]
  cases hp : σ.pending with
  | none => simp
  | some p =>
    have : p ≠ [] := by rintro rfl; exact hne hp
    simp [this]

theorem compact_mono (σ : MvccState) (r : Int) (hr : σ.crev < r) :
    σ.notifiedLog <+: (σ.compactTo r).notifiedLog ∧ σ.crev ≤ (σ.compactTo r).crev :=
  ⟨by simp [MvccState.compactTo, MvccState.notifiedLog], by simp [MvccState.compactTo]; omega⟩

/-- `Restore`'s update (`KV.Restore.contract`: the restored history extends the old, the
compaction revision not lowered), **at a state with nothing pending**: the contract's AU does not
say `σ.pending = none`; with a pending revision `p`, `σ.log ++ [p]` need not be a prefix of
`σ'.log`, and a fact recorded against the notified log would be lost. The implementation fires the
update with no transaction open, so it knows `σ.pending = none` from the writer's state. -/
theorem restore_mono (σ σ' : MvccState) (hp : σ.pending = none) (hp' : σ'.pending = none)
    (hl : σ.log <+: σ'.log) (hc : σ.crev ≤ σ'.crev) :
    σ.notifiedLog <+: σ'.notifiedLog ∧ σ.crev ≤ σ'.crev := by
  simp only [MvccState.notifiedLog, hp, hp']
  exact ⟨hl, hc⟩

/-- **Every reachable step keeps the premises** (the stream's part untouched). -/
theorem SentInv.step {σ σ' S D F} (h : SentInv σ S D F) (hl : σ.notifiedLog <+: σ'.notifiedLog)
    (hc : σ.crev ≤ σ'.crev) : SentInv σ' S D F :=
  { h with lbs := lbsOk_mono hl hc h.lbs }

end probe
end api
end mvcc
end EtcdGrove
end Perennial
