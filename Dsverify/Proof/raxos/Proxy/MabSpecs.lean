/-
Package `proxy`: leader mode 2's functions (`proxymabhandler.go`), their internal specs (as
`Prop`s, so that each proof takes the specs of what it calls as hypotheses).

* `getLeaderSequence(i)`: an order `q` of the replicas `1..n` (a permutation: round robin for
  the first `2n` epochs; the summary decided at the previous epoch's first slot, parsed; or the
  replica itself last, when it does not know it), and when `q` starts with the replica itself,
  the evidence that it leads slot `i` (`leadEv`).
* `getLeaderWait(q)`: the replica's rank in `q` times the leader timeout.
* `isBeginningOfEpoch(i)`: `sumSlot`.
* `calculateSequence(e)`: `seqStr p` of a permutation `p` of `1..n`.
* `updateEpochTime(i)`, `hasAllDecided(e)`: the epochs' times (any values).
-/
module

public import Dsverify.Proof.raxos.Proxy.OwnProp
public import Dsverify.Proof.raxos.Cons.Laws

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

/-- A leader sequence's `int64`s. -/
def seqOf (q : List Nat) : List w64 := q.map (fun x : Nat => W64 (x : Int))

/-- `calculateSequence`'s string of the order `p`: its replicas comma-separated (`summaryId p`
is `"Epoch"` and it). -/
def seqStr (p : List Nat) : GoString := (List.intersperse go!"," (p.map decimal)).flatten

theorem summaryId_seqStr (p : List Nat) : summaryId p = go!"Epoch" ++ seqStr p := rfl

theorem w64_mul_small (t : Nat) (jj : w64) (ht : t ≤ 40000) (h0 : 0 ≤ sint.Z jj) (h5 : sint.Z jj ≤ 5) :
    W64 (t : Int) * jj = W64 ((t : Int) * sint.Z jj) := by
  have hb : (t : Int) * sint.Z jj ≤ 200000 := by
    have := Int.mul_le_mul (a := (t:Int)) (b := sint.Z jj) (c := 40000) (d := 5) (by omega) h5 h0 (by omega)
    omega
  have hb0 : 0 ≤ (t : Int) * sint.Z jj := Int.mul_nonneg (by omega) h0
  have h1 : BitVec.toInt (W64 (t:Int) * jj) = t * sint.Z jj := by
    have : sint.Z (W64 (t : Int)) = t := by word
    rw [BitVec.toInt_mul, show BitVec.toInt (W64 (t:Int)) = t from this]
    change Int.bmod ((t : Int) * sint.Z jj) _ = _
    exact Int.bmod_eq_of_le (by simp; omega) (by simp; omega)
  have h2 : sint.Z (W64 ((t : Int) * sint.Z jj)) = t * sint.Z jj := by
    generalize (t : Int) * sint.Z jj = m at *
    word
  apply BitVec.eq_of_toInt_eq; exact h1.trans h2.symm


theorem w64_mul_toInt (a b : w64) (ha : 0 ≤ sint.Z a ∧ sint.Z a ≤ 1000000)
    (hb : 0 ≤ sint.Z b ∧ sint.Z b ≤ 1000000) : sint.Z (a * b) = sint.Z a * sint.Z b := by
  have h1 : sint.Z a * sint.Z b ≤ 1000000 * 1000000 :=
    Int.mul_le_mul ha.2 hb.2 hb.1 (by omega)
  have h0 : 0 ≤ sint.Z a * sint.Z b := Int.mul_nonneg ha.1 hb.1
  show BitVec.toInt _ = _
  rw [BitVec.toInt_mul]
  change Int.bmod (sint.Z a * sint.Z b) _ = _
  exact Int.bmod_eq_of_le (by simp; omega) (by simp; omega)


section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]

attribute [local instance] HeapGS.goose_globalGS

/-- The replicated log, read (the main loop's: returned unchanged). -/
def logRd (γ : QNames) (γs : GName) (c : QConf) (pr : Loc) (rl : GoSlice) (slots : List Slot)
    (L : List (Option (List GoString))) : IProp GF :=
  iprop(pr.[Proxy, go!"replicatedLog"] ↦ rl ∗ rl ↦* slots ∗ logP γ γs c slots L)

/-- `pr.getLeaderSequence(i)`: an order `q` of `1..n`; if it starts with replica `k`, `k` leads
slot `i` (`leadEv`). -/
abbrev getLeaderSequence_spec : Prop :=
  ∀ (γ : QNames) (γs : GName) (c : QConf) (k : Nat) (pr : Loc) (i : w64) (rl : GoSlice)
    (slots : List Slot) (L : List (Option (List GoString))),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ sharedConsts c k pr ∗
      ⌜c.ok ∧ 1 ≤ k ∧ k ≤ c.n ∧ 0 ≤ sint.Z i ∧ sint.Z i ≤ 100000⌝ ∗
      inv consN (consInv γ) ∗ confIs γ c ∗ logRd γ γs c pr rl slots L }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"getLeaderSequence")) (Val #i))
  {{ (sl : GoSlice) (q : List Nat), RET #sl; sl ↦* seqOf q ∗ ⌜isPerm c.n q⌝ ∗
      (if decide (q.head? = some k) then leadEv γ c (sint.Z i) k else iprop(True)) ∗
      logRd γ γs c pr rl slots L }}

/-- `pr.getLeaderWait(q)`: replica `k`'s rank in `q` times the timeout. -/
abbrev getLeaderWait_spec : Prop :=
  ∀ (c : QConf) (k : Nat) (pr : Loc) (sl : GoSlice) (q : List Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ sharedConsts c k pr ∗
      ⌜c.ok ∧ 1 ≤ k ∧ k ≤ c.n ∧ isPerm c.n q⌝ ∗ sl ↦* seqOf q }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"getLeaderWait")) (Val #sl))
  {{ RET #(W64 (c.tmo * q.idxOf k)); ⌜q.idxOf k < c.n⌝ ∗ sl ↦* seqOf q }}

/-- `pr.isBeginningOfEpoch(i)`: slot `i` is a summary slot. -/
abbrev isBeginningOfEpoch_spec : Prop :=
  ∀ (c : QConf) (k : Nat) (pr : Loc) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ sharedConsts c k pr ∗
      ⌜c.ok ∧ 0 ≤ sint.Z i ∧ sint.Z i ≤ 100000⌝ }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"isBeginningOfEpoch")) (Val #i))
  {{ RET #(decide (sumSlot c.n c.ep (sint.Z i))); True }}

/-- `pr.hasAllDecided(e)`: whether the epoch's slots (but its last) are decided here. -/
abbrev hasAllDecided_spec : Prop :=
  ∀ (c : QConf) (k : Nat) (pr : Loc) (e : w64) (rl : GoSlice) (slots : List Slot),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ sharedConsts c k pr ∗
      ⌜c.ok ∧ 0 ≤ sint.Z e ∧ sint.Z e ≤ 100000⌝ ∗
      pr.[Proxy, go!"replicatedLog"] ↦ rl ∗ rl ↦* slots }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"hasAllDecided")) (Val #e))
  {{ (b : Bool), RET #b; pr.[Proxy, go!"replicatedLog"] ↦ rl ∗ rl ↦* slots }}

/-- `pr.updateEpochTime(i)`: the epochs' times updated (any values). -/
abbrev updateEpochTime_spec : Prop :=
  ∀ (c : QConf) (k : Nat) (pr : Loc) (i : w64) (rl : GoSlice) (slots : List Slot),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ sharedConsts c k pr ∗
      ⌜c.ok ∧ 0 ≤ sint.Z i ∧ sint.Z i ≤ 100000⌝ ∗ epochOwn pr ∗
      pr.[Proxy, go!"replicatedLog"] ↦ rl ∗ rl ↦* slots }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"updateEpochTime")) (Val #i))
  {{ RET #(); epochOwn pr ∗ pr.[Proxy, go!"replicatedLog"] ↦ rl ∗ rl ↦* slots }}

/-- `pr.calculateSequence(e)` for an epoch `e ≥ 2n`: the string of an order `p` of `1..n`. -/
abbrev calculateSequence_spec : Prop :=
  ∀ (γ : QNames) (γs : GName) (c : QConf) (k : Nat) (pr : Loc) (e : w64) (rl : GoSlice)
    (slots : List Slot) (L : List (Option (List GoString))),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ sharedConsts c k pr ∗
      ⌜c.ok ∧ 1 ≤ k ∧ k ≤ c.n ∧ 2 * (c.n : Int) ≤ sint.Z e ∧ sint.Z e ≤ 1000⌝ ∗
      inv consN (consInv γ) ∗ confIs γ c ∗ logRd γ γs c pr rl slots L ∗ epochOwn pr }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"calculateSequence")) (Val #e))
  {{ (p : List Nat), RET #(seqStr p); ⌜isPerm c.n p⌝ ∗ logRd γ γs c pr rl slots L ∗
      epochOwn pr }}

end specs

end Perennial.raxos
