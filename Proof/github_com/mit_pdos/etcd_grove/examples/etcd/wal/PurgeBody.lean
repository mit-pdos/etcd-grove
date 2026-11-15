/-
**The body of `purgeRound`'s axiom** (WAL W4c, the purgeRound Freeze; the plan's §5 consistency
check, as `Proof/go_etcd_io/etcd/server/v3/storage/WalBodies.lean` does for the WAL's axioms).
Proved: nothing here is trusted.

`purgeRound` is names-only (`Spec/.../examples/etcd/wal/purgeRound.lean`): its spec is an axiom,
and its body is read as one that performs the abstract-disk extension's step `"WalPurge"` of
`(dir, k)`, `k` the start of the first file the round leaves.

* `purgeRound_commit`: the body. At the access, `"WalPurge"` of `k` with the accessed `walDiskAt`
  is the commit, at the chosen `k` (the update's `∀∀ k`, with the step's guard as the pure fact
  the commit hands over). The handle and its right are framed: the step needs neither
  (`wp_WalPurge`), which is why the axiom, not the step, takes them (the W4c gate M1). The post is
  the axiom's (`Q d k` with the rights), and holds no fact about a past state.
* The step's guard `cut ≤ k ≤ max pur unl` is satisfiable at every reachable state, by
  `k := cut` (a round that deletes nothing): the extension's semantics keeps `cut ≤ pur` for every
  WAL (`absCutLePur`: true at the start, `absCutLePur_init`; kept by every step,
  `absCutLePur_step`, and by the crash, `absCutLePur_crash`, which establishes it afresh), so `walPurge_guard_cut`. The accessed
  `walDiskAt dir d` agrees with the real state on `cut`, `pur` and `unl` (`walDurLe` keeps them
  exact), so the body is never stuck. What `k` Go's round produces is argued in the axiom's
  docstring (oldest first, stopping at the first locked file), as the other axioms argue their
  steps' arguments (`walCode`'s docstring).

**What the lemma does not show** (the axiom review's m1). `d` and `k` are parameters fixed before
the access. `d` is a function of the state, as in `WalBodies.lean`. `k` is a function of the future:
Go's round learns where it stops only after the commit, at its first lock or remove that fails. So
the commit at the round's first step uses a prophesied `k`. That is sound, because only the guard
constrains `k`, and a crash mid-round needs no particular `k` (`walCrash` chooses the read position
afresh, at most `min pur |I|`). A step `"WalPurge"` that chose `k` itself, within the guard, would
make a body realizable without fixing `d` (a possible later change to `Impl.lean`, not made).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalDisk

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI

/-! ## `cut ≤ pur`: the step's guard is satisfiable -/

/-- Every WAL's read position is at most its purge bound. -/
def absCutLePur (s : AbsDiskState) : Prop :=
  ∀ dir d, s.wal !! dir = some d → d.cut ≤ d.pur

theorem absCutLePur_init {s : AbsDiskState} (h : absDiskInitOk s) : absCutLePur s := by
  intro dir d hd
  rw [h.2.2.2] at hd
  simp at hd

theorem absCutLePur_upd {s : AbsDiskState} (dir : GoString) (f : WalDur → WalDur)
    (hf : ∀ d, s.wal !! dir = some d → d.cut ≤ d.pur → (f d).cut ≤ (f d).pur)
    (hs : absCutLePur s) :
    absCutLePur (absDiskUpd s dir f) := by
  intro k d h
  unfold absDiskUpd at h
  cases hd : s.wal !! dir with
  | none => rw [hd] at h; exact hs k d h
  | some d0 =>
    rw [hd] at h
    simp only at h
    by_cases hk : dir = k
    · subst hk
      rw [GMap.lookup_insert] at h
      cases h
      exact hf d0 hd (hs dir d0 hd)
    · rw [GMap.lookup_insert_ne _ _ hk] at h; exact hs k d h

/-- Every step keeps `cut ≤ pur`. -/
theorem absCutLePur_step [GooseExts] [GoGlobalContext] {op : String} {v : val}
    {h h' : GMap Loc (NonAtomic val)} {s s' : AbsDiskState} {g g' : Unit} {e' : Expr}
    (hst : AbsDiskStep op v h s g e' h' s' g') (hs : absCutLePur s) : absCutLePur s' := by
  unfold AbsDiskStep at hst
  obtain ⟨-, -, hst⟩ := hst
  split at hst
  · obtain ⟨dir, md, -, -, -, rfl⟩ := hst
    intro k d hk
    by_cases hdk : dir = k
    · subst hdk
      simp only [GMap.lookup_insert] at hk
      cases hk
      simp [walDurFresh]
    · simp only [GMap.lookup_insert_ne _ _ hdk] at hk
      exact hs k d hk
  · obtain ⟨dir, -, rfl⟩ := hst
    exact absCutLePur_upd dir _ (fun _ _ h => h) hs
  · obtain ⟨dir, o, -, rfl⟩ := hst
    exact absCutLePur_upd dir _ (fun _ _ h => h) hs
  · obtain ⟨dir, n, -, -, rfl⟩ := hst
    exact absCutLePur_upd dir _ (fun _ _ h => h) hs
  · obtain ⟨dir, p, -, rfl⟩ := hst
    exact absCutLePur_upd dir _ (fun _ _ h => h) hs
  · obtain ⟨dir, k, -, hk, rfl⟩ := hst
    exact absCutLePur_upd dir _ (fun d hd _ => (hk d hd).2) hs
  · obtain ⟨d, -, -, rfl⟩ := hst
    exact hs
  · exact hst.elim

/-- The crash gives `cut ≤ pur` (whatever held before): the new read position is at most the
clamped purge bound. -/
theorem absCutLePur_crash {s s' : AbsDiskState} (hc : absDisk_semantics.crash s s') :
    absCutLePur s' := by
  intro dir d' h'
  cases hd : s.wal !! dir with
  | none => rw [hc.2.2.2 dir hd] at h'; cases h'
  | some d =>
    have hcr := hc.2.2.1 dir d hd
    rw [h'] at hcr
    rcases hcr with ⟨-, hn⟩ | ⟨I, k, -, hk, he⟩
    · cases hn
    · cases he
      exact hk

/-- **The step's guard holds at `k := cut`** in every state the semantics reaches. -/
theorem walPurge_guard_cut {s : AbsDiskState} (hs : absCutLePur s) {dir : GoString} {d : WalDur}
    (hd : s.wal !! dir = some d) : d.cut ≤ d.cut ∧ d.cut ≤ max d.pur d.unl :=
  ⟨Nat.le_refl _, Nat.le_trans (hs dir d hd) (Nat.le_max_left _ _)⟩

/-! ## The body -/

section body
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt absDiskExt] [go_gctx : GoGlobalContext]
  [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- **`purgeRound`'s commit**: at the access, `"WalPurge"` of `k` with the accessed `walDiskAt`
(its guard `hk`), and the commit at `k`; the handle and its right framed. -/
theorem purgeRound_commit (w : Loc) (dir : GoString) (d : WalDur) (k : Nat)
    (hk : d.cut ≤ k ∧ k ≤ max d.pur d.unl) (Ψ : Nat → IProp GF) :
    walOpenW (L := hG.goose_localGS) w dir ∗ walPurgeW (L := hG.goose_localGS) w dir ∗
      (|={⊤,∅}=> walDiskAt (L := hG.goose_localGS) dir d ∗
        (∀ k', ⌜d.cut ≤ k' ∧ k' ≤ max d.pur d.unl⌝ ∗
          walDiskAt (L := hG.goose_localGS) dir { d with pur := max d.pur d.unl, cut := k' }
            ={∅,⊤}=∗ Ψ k'))
    ⊢ WP (ExternalOp absDiskExt.name "WalPurge" (Val (PairV (#dir) (#(walCode k))))) {{ _v,
        walOpenW (L := hG.goose_localGS) w dir ∗ walPurgeW (L := hG.goose_localGS) w dir ∗
          Ψ k }} := by
  iintro ⟨Hw, Hr, Hacc⟩
  iapply wp_WalPurge dir k d hk
  imod Hacc with ⟨Hd, Hcommit⟩
  imodintro
  iframe Hd
  iintro Hd %s' _ %_
  inext
  imod Hcommit $$ [Hd] with HΨ
  · iframe Hd; ipureintro; exact hk
  imodintro
  iframe Hw Hr HΨ

end body

end etcd_wal
end EtcdGrove
end Perennial
