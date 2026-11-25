/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLc/Facts.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-c: the run-level facts F1 rests on (`notes/unit-Lc.md`), proved from their own modules
(`l2_write`: unit L-b's `l2_write_lb`).

* L3 (values) for the carriers F1 reads: stores (`prod_store`), an RMW's execution
  (`prod_exec`: the result is the CAS, by the RMW's own command, of a produced pair `vt0` with
  tag `max(base, prev)`, and the result's tag is `vt0`'s with `rmwc + 1`), a read's reply
  (`prod_read`: the value returned with the read's place).
* Producer uniqueness: writes in `lin` (`write_place_uniq`, by `WB` and L2 for writes); proved
  elsewhere: RMWs' `rmw_res_uniq` (`PureLc/Chain.lean`), writes' tags have `rmwc = 0`
  (`write_place_rmwc`, `PureLc/WTag.lean`).
-/
module

public import Dsverify.Proof.gryff.PureLc.ReadRep
public import Dsverify.Proof.gryff.PureL.L1
public import Dsverify.Proof.gryff.PureLb.L2W

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

/-- **L3 for stores**: a store's pair is produced.

From the values invariant over all carriers (`PureLc/Vals.lean`, `PureLc/VInv.lean`: `vinv`). -/
theorem prod_store {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (n : Nat)
    (r : Fin 3) : Prod l (cutSt l n r).val (cutSt l n r).tag :=
  (vinv_cut h n r).store.1

/-- **L3 for `PrevValTag`**: the executor's previous result is produced (and its `rmwc` is not
negative).

From `vinv`. -/
theorem prod_prev {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (n : Nat)
    (r : Fin 3) {vt : ValTag} (hv : (cutSt l n r).prevValTag = some vt) :
    Prod l vt.v vt.t ∧ 0 ≤ sint.Z vt.t.rmwc :=
  (vinv_cut h n r).prev vt hv

/-- **L3 for committed bases**: a committed copy's base is produced (and its `rmwc` is not
negative).

From `vinv`. -/
theorem prod_base {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) (n : Nat)
    (r : Fin 3) {q i : w32} {cp : Copy} (hcp : (cutSt l n r).inst q i = some cp)
    (hst : cp.status = St.COMMITTED) :
    Prod l cp.base.v cp.base.t ∧ 0 ≤ sint.Z cp.base.t.rmwc :=
  ((vinv_cut h n r).inst q i cp hcp).1

/-- **The commands invariant** (`PureLc/Cmds.lean`, `cinv`): a committed copy, with commands, of
an RMW's instance has the RMW's command first. -/
theorem exec_cmd {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {a b : w64} (hi : o.inp = .cas a b) {n : Nat} {r : Fin 3} {cp : Copy}
    (hcp : (cutSt l n r).inst (rmwInst l o).1 (rmwInst l o).2 = some cp)
    (hst : cp.status = St.COMMITTED) {c0 : Cmd} {rest : List Cmd} (hc : cp.cmds = c0 :: rest) :
    c0.oldV = a ∧ c0.v = b := by
  obtain ⟨cn, h1, -, h3⟩ := grun_cut h n
  have hci := cinv (L := l) _ _ h1 (List.take_prefix n l)
  have hs : stR cn r = cutSt l n r := by
    obtain ⟨o', ho'⟩ := h3 r; unfold cutSt; rw [stOf_of_runP ho']; rfl
  have hok := (hci r).1 _ _ cp (by rw [hs]; exact hcp)
  obtain ⟨o', ho', hi', hx⟩ := hok.1 c0 rest hc
  have e := rmwInst_inj h ho' ho hi' hi hx
  subst e
  rw [hi] at hi'
  cases hi'
  exact ⟨rfl, rfl⟩

/-- **The RMW chain step** (L3 for an execution): an RMW's result is the CAS, by its own command,
of a produced pair `vt0` (the newer of the executed copy's base and `PrevValTag`), with tag
`vt0.t` with `rmwc + 1` (no wrap). -/
theorem prod_exec {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {a b : w64} (hi : o.inp = .cas a b) {vt : ValTag}
    (hr : rmwRes l o = some vt) :
    ∃ vt0 : ValTag, Prod l vt0.v vt0.t ∧ 0 ≤ sint.Z vt0.t.rmwc ∧
      sint.Z vt0.t.rmwc < 2 ^ 31 - 1 ∧ vt.t = { vt0.t with rmwc := vt0.t.rmwc + 1 } ∧
      vt.v = (if vt0.v = a then b else vt0.v) := by
  obtain ⟨r, hm⟩ := rmwRes_mem hr
  obtain ⟨j, hj, hv⟩ := (mem_execSeq r).1 hm
  obtain ⟨n, s', o', -, hc, hs, -, ho'⟩ := proj_step h hj
  rw [ho'] at hv
  change stepExec _ _ _ = _ at hs
  obtain ⟨cp, c0, rest, hcp, hst, hcm, vt0, hor, -, -, htt, hvv⟩ := stepExec_full hs hv
  rw [← hc] at hcp
  obtain ⟨hb1, hb2⟩ := rmwc_bounded h n r
  have hP : Prod l vt0.v vt0.t ∧ 0 ≤ sint.Z vt0.t.rmwc ∧ sint.Z vt0.t.rmwc < 2 ^ 31 - 1 := by
    rcases hor with e | e
    · rw [e]; exact ⟨(prod_base h n r hcp hst).1, (prod_base h n r hcp hst).2, hb2 _ _ _ hcp⟩
    · rw [← hc] at e
      exact ⟨(prod_prev h n r e).1, (prod_prev h n r e).2, hb1 _ e⟩
  obtain ⟨e1, e2⟩ := exec_cmd h ho hi hcp hst hcm
  refine ⟨vt0, hP.1, hP.2.1, hP.2.2, htt, ?_⟩
  rw [hvv, e1, e2]
  by_cases e : vt0.v = a
  · rw [if_pos e, if_pos e.symm]
  · rw [if_neg e, if_neg (Ne.symm e)]

/-- **L3 for a read's reply**: the value a read returns, with its place, is produced.

From `vinv` and the reply handlers (`PureLc/ReadRep.lean`: `step_rr`, `prod_read'`). -/
theorem prod_read {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) (hi : o.inp = .read) {j : Nat} {v : w64} (hr : readReply l o = some (j, v))
    {t : model.Tag} (ht : readPlace l o = some t) : Prod l v t :=
  prod_read' h hi hr ht

/-- **L2 for writes**: when a write is replied to (label `n`), its place is at most the frontier
(after the label). Unit L-b's `l2_write_lb` (integration). -/
theorem l2_write {l : List Label} {c : Cfg gNet} (h : GRun (Cfg.init gNet) l c) {o : Op}
    (ho : o ∈ ops l) {v : w64} (hi : o.inp = .write v) {n : Nat} (hr : RepliesTo l n o)
    {t : model.Tag} (ht : place l o = some t) : tagLe t.toP (front l (n + 1)) :=
  l2_write_lb h ho hi hr ht -- unit L-b (`PureLb/L2W.lean`)

end Perennial.gryff.pure
