/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/Exec.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
Helpers of the execution loops (`onPrepareOK`, `onCommit`) and of the lagging branches
(`onCommit`, `onPrepare`): the replica with a commit number and a last executed op
(`withExec`), the client table's coverage under `recordResult`/`recordRequest`, a logging call
without arguments (`wp_log0`), and the state transfer branch (`lag_st`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Send
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Log
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Helpers
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.InitiateStateTransfer

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel


/-- The client table's coverage is kept by `recordResult`. -/
theorem replica.covers_recRes_mono [GooseExts] (tbl : GMap w64 replica.ClientTableData)
    (l : List Entry) (c q : w64) (res : GoString) (h : replica.Covers tbl l) :
    replica.Covers (replica.recRes tbl c q res) l := fun e he => by
  obtain ⟨d, hd, hle⟩ := h e he
  obtain ⟨d', hd', hle'⟩ := replica.recRes_ge tbl c q res _ d hd
  exact ⟨d', hd', Nat.le_trans hle hle'⟩

/-- The client table's coverage is kept by `recordRequest`. -/
theorem replica.covers_recReq_mono [GooseExts] (tbl : GMap w64 replica.ClientTableData)
    (l : List Entry) (c q : w64) (h : replica.Covers tbl l) :
    replica.Covers (replica.recReq tbl c q) l := fun e he => by
  obtain ⟨d, hd, hle⟩ := h e he
  obtain ⟨d', hd', hle'⟩ := replica.recReq_ge tbl c q _ d hd
  exact ⟨d', hd', Nat.le_trans hle hle'⟩

/-- The replica `v` with commit number `cn` and last executed op `le` (the execution loops). -/
abbrev replica.withExec [GooseExts] (v : replica.Replica) (cn le : w64) : replica.Replica :=
  { ({ v with state' := { v.state' with CommitNumber' := cn } } : replica.Replica) with
    internal' := { v.internal' with lastExecutedOpNum' := le } }

set_option hygiene false in
/-- A logging call without arguments (`nil` arguments' slice). -/
macro "wp_log0" : tactic => `(tactic| (
  try wp_auto
  wp_apply (replica.wp_logMethod H _ _ _ slice.nil ([] : List GoInterface) (DFrac.own 1) (by decide))
    $$ [] as -
  · iframe Hlogger
    isplitl []
    · iapply (ownSlice_nil (V := GoInterface) (DFrac.own 1))
    · iapply (BI.BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro))

set_option hygiene false in
/-- A lagging replica's branch of `onCommit` (and `onPrepare`): a state transfer (its spec), a
log line, and the replica's state from it. -/
macro "lag_st" : tactic => `(tactic| (
  wp_log
  wp_apply (replica.wp_initiateStateTransfer H rp γ r tcp v n _ _) $$ [-HΦ r Hev]
    as ⟨%v', Hr, Hinv, %Hsame⟩
  · iframe Hr Hsize
    isplitl
    · unfold replica.repInv
      iexists lg, mine, cw, mw, me, C, F, P, ms, tbl, pk, sv, dv, vst, cst, n
      iFrameNamed
      ipureintro
      exact ⟨Hid, Hmslen, Hnet, Htime, Hstatus, Hst, Hopnum, Hcommit, Hmine, Htmine, Htlog⟩
    · ipureintro; intro _; exact hnotp
  obtain ⟨-, -, hlg, -, -⟩ := Hsame
  irename Hlogger => Hlogger0
  ihave #Hlogger : log.slog.isLogger v'.logger' $$ []
  · rw [hlg]; iexact Hlogger0
  wp_log0
  unfold replica.repInv
  iapply HΦ
  iexists v'
  iframe Hr
  iexact Hinv))

end Perennial.github_com.tangledbytes.go_vsr.pkg
