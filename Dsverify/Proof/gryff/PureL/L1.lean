/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureL/L1.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L: **L1** (`notes/stage2-proof.md` §L): an operation's place is at least the frontier at its
creation, strictly above it for producers (writes, RMWs).

`front l o.g` is the frontier just before `o`'s request label (the cut of `o.g` labels).
-/
module

public import Dsverify.Proof.gryff.PureL.Store
public import Dsverify.Proof.gryff.PureL.F4
public import Dsverify.Proof.gryff.PureL.Witness
public import Dsverify.Proof.gryff.PureL.WRec
public import Dsverify.Proof.gryff.PureLb.L1Read

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

theorem Op.rank_le (o : Op) : o.rank ≤ 1 := by
  unfold Op.rank; split <;> omega

theorem Op.rank_read {o : Op} (h : o.rank ≠ 0) : o.inp = .read := by
  unfold Op.rank at h; split at h
  · assumption
  · exact absurd rfl h

/-- **L1 for writes**: a write's `WriteTag` is above the frontier at its creation.

Proof: from the write-record invariant `WInv` (`PureL/WRec.lean`, `l1_write_of_inv`). Paper: the tag is `(ts + 1, cid, 0)` with `ts` the maximum of two `Write1Reply`s'
tags from distinct replicas (the coordinator's record only gets its own operation's replies: the
key guard `RState.used`); each reply carries its replica's store at its handling, after the
creation, so two stores at creation are at most `(ts, _, _)` < the tag
(`median3_le_of_two`, `cut_tag_mono`). Needs the coordinator-record invariant (a `wops` record's
counters count distinct repliers' replies to this operation's `Write1`s, each carrying the
replier's store at a time after the request) and the tag bound (`ts + 1` does not wrap: tags' `ts`
are below the number of writes, ≤ 72 by the budget). -/
theorem l1_write {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {v : w64} (hi : o.inp = .write v) {t : model.Tag}
    (ht : place l o = some t) : tagLt (front l o.g) t.toP :=
  l1_write_of_inv h ho hi ht

/-- An RMW's place comes from an execution, at some label `n`, of its instance with a command:
the executing replica's committed copy, and the result's tag above its base. -/
theorem rmwPlace_exec {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    {t : model.Tag} (ht : rmwPlace l o = some t) :
    ∃ n r cp, (cutSt l n r).inst (rmwInst l o).1 (rmwInst l o).2 = some cp ∧
      cp.status = St.COMMITTED ∧ cp.cmds ≠ [] ∧ tagLt cp.base.t.toP t.toP := by
  obtain ⟨r, -, hr⟩ := List.exists_of_findSome?_eq_some ht
  unfold execTag at hr
  obtain ⟨j, -, hj⟩ := List.exists_of_findSome?_eq_some hr
  split at hj
  · rename_i q i hes
    split at hj
    · rename_i hx
      obtain ⟨vt, hvt, rfl⟩ := Option.map_eq_some_iff.1 hj
      obtain ⟨n, hn, hpn⟩ := proj_index l r hes
      have hs : stOf r ((projR l r).take j) = cutSt l n r := by unfold cutSt; rw [hpn]
      unfold outsOf resOf at hvt
      rw [hes] at hvt
      simp only at hvt
      rw [hs] at hvt
      cases hres : stepR r (cutSt l n r) (Ev.exec q i) with
      | error f => rw [hres] at hvt; simp [execRes] at hvt
      | ok p =>
        obtain ⟨s', o'⟩ := p
        rw [hres] at hvt
        simp only at hvt
        obtain ⟨cp, hcp, hst, hcm, t0, hle, heq, hor⟩ := stepExec_res hres hvt
        have hx1 : q = (rmwInst l o).1 := by rw [← hx]
        have hx2 : i = (rmwInst l o).2 := by rw [← hx]
        rw [hx1, hx2] at hcp
        refine ⟨n, r, cp, hcp, hst, hcm, ?_⟩
        rw [heq]
        obtain ⟨hb1, hb2⟩ := rmwc_bounded h n r
        have hbound : sint.Z t0.rmwc < 2 ^ 31 - 1 := by
          rcases hor with e | ⟨pvt, hp, e⟩
          · rw [e]; exact hb2 _ _ _ hcp
          · rw [e]; exact hb1 _ hp
        exact tagLt_of_le_of_lt hle (tagLt_rmwc_succ t0 hbound)
    · cases hj
  · cases hj

/-- **L1 for RMWs**: an RMW's result tag is above the frontier at its creation: the result tag is
above the executed copy's (committed) base (`rmwPlace_exec`), which two distinct replicas' stores
at the creation do not exceed (`witness_committed`, the witness invariant). -/
theorem l1_rmw {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {a b : w64} (hi : o.inp = .cas a b) {t : model.Tag}
    (ht : place l o = some t) : tagLt (front l o.g) t.toP := by
  have ht' : rmwPlace l o = some t := by unfold place at ht; rw [hi] at ht; exact ht
  obtain ⟨n, r, cp, hcp, hst, hcm, hlt⟩ := rmwPlace_exec h ht'
  obtain ⟨w1, w2, hne, h1, h2⟩ := witness_committed h ho hi hcp hst hcm
  exact tagLt_of_le_of_lt (median3_le_of_pair hne h1 h2) hlt

/-- **L1 for reads**: a read's returned tag is at least the frontier at its creation.

Proved from the read-record invariant `RInv` (`PureLb/RInv.lean`, `l1_read_of_inv` in
`PureLb/L1Read.lean`). Proof (paper): (first `Read1Reply`) the replier first overwrites with the coordinator's
store as of the request (carried in `Read1Proxied.vt`), then replies with its own store, so the
tag is at least two distinct stores at creation; (short-circuited by a write's `Write2Reply`) the
write's tag was applied (`applied = 1`: the store was below it) at two replicas after the read's
request (the read joined the write's `shortReads` before its `Write2`s were sent). -/
theorem l1_read {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) (hi : o.inp = .read) {t : model.Tag}
    (ht : place l o = some t) : tagLe (front l o.g) t.toP :=
  l1_read_of_inv h ho hi ht

/-- **L1** for every operation. -/
theorem l1 {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {t : model.Tag} (ht : place l o = some t) :
    tagLe (front l o.g) t.toP ∧ (o.rank = 0 → tagLt (front l o.g) t.toP) := by
  cases hi : o.inp with
  | read =>
    refine ⟨l1_read h ho hi ht, fun hr => ?_⟩
    simp [Op.rank, hi] at hr
  | write v =>
    have := l1_write h ho hi ht; exact ⟨tagLe_of_lt this, fun _ => this⟩
  | cas a b =>
    have := l1_rmw h ho hi ht; exact ⟨tagLe_of_lt this, fun _ => this⟩

/-- L1 at an earlier cut: an operation created at or after cut `k` has its place at least the
frontier at `k` (strictly for producers). -/
theorem l1_cut {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {t : model.Tag} (ht : place l o = some t) {k : Nat} (hk : k ≤ o.g) :
    tagLe (front l k) t.toP ∧ (o.rank = 0 → tagLt (front l k) t.toP) := by
  have hm := front_mono h hk
  obtain ⟨h1, h2⟩ := l1 h ho ht
  exact ⟨tagLe_trans hm h1, fun hr => tagLt_of_le_of_lt hm (h2 hr)⟩

end Perennial.gryff.pure
