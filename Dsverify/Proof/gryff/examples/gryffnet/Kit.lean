/-
# The gryff kit on `examples/lib/remote` (notes/dsv-gryff.md): the far side's store

* **The register** `casB` (`ModelSet.lean`): linkv's pending-writes store of the register with
  compare-and-swap, kit.go's `apply`; Writes and CASes pending when their outcome is unknown.
* **The store's outputs are values** (`casBK`: `casB` with `Out{false, V}` read as `V`; `pseq_K`
  relates their sequential models): remote's `PendDec` needs each output to decode as one.
* **The far side's store** `casR γ` (`remote.RBase`): the register's state is Gryff's invariant's
  other half (`regHalf γ.proto`, the abstract register), the mask of the update is `gryffN`
  (Gryff's invariant: a replica's step fires a client's update with it open), the Go values are
  boxed `In`/`Out`, the bytes `Codec()`'s (an input 24 bytes, an output 9).
* **Its linearization point is the Gryff client's update** (`lin_opAU`): remote's `lin` is
  `Proto/InvDefs.lean`'s `opAU` at the input's `RegInput` (`toRI`), its output read back
  (`fromRO`).
-/
module

public import Dsverify.Proof.gryff.examples.gryffnet.ModelDefs
public import Dsverify.Proof.gryff.Proto.InvDefs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace gryff.examples.gryffnet

open EtcdGrove EtcdGrove.linkv github_com.mit_pdos.etcd_grove.examples.lib.remote
open dsverify_lab.harness

/-! ## The register's inputs and outputs as the protocol's -/

section pure
variable [GooseExts]

/-- kit.go's `In` as the protocol's input: `Write(A)`, `CAS(A, B)`, else a `Read`. -/
def toRI (i : In) : RegInput w64 :=
  if i.Op' = W64 1 then .write i.A' else if i.Op' = W64 2 then .cas i.A' i.B' else .read

/-- The protocol's output as kit.go's `Out` (a Read's value; `Out{}` for a Write's and a CAS's). -/
def fromRO : RegOutput w64 → Out
  | .value v => ⟨false, v⟩
  | .done => outDone
  | .swapped _ => outDone

/-- kit.go's `apply` is the protocol's step. -/
theorem applyG_casApply (v : w64) (i : In) :
    applyG v i = ((casApply v (toRI i)).1, fromRO (casApply v (toRI i)).2) := by
  unfold applyG toRI
  by_cases h1 : i.Op' = W64 1
  · rw [if_pos h1, if_pos h1]; rfl
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : i.Op' = W64 2
    · rw [if_pos h2, if_pos h2]; rfl
    · rw [if_neg h2, if_neg h2]; rfl

/-- Every output of `apply` is known (`Unknown = false`). -/
theorem applyG_known (v : w64) (i : In) : (applyG v i).2.Unknown' = false := by
  unfold applyG
  by_cases h1 : i.Op' = W64 1
  · rw [if_pos h1]; all_goals rfl
  · rw [if_neg h1]
    by_cases h2 : i.Op' = W64 2
    · rw [if_pos h2]; all_goals rfl
    · rw [if_neg h2]; all_goals rfl

/-- **The register with its outputs' values** (`casB` with `Out{false, V}` read as `V`): the
far side's store's sequential spec. remote's `PendDec` asks every output `o` to decode as `.ok o`,
which an `Out` with `Unknown` set does not (it is an unknown outcome): the store's outputs are the
values. -/
def casBK : PendSpec w64 In w64 where
  init := W64 0
  step i v := ((applyG v i).1, (applyG v i).2.V')
  isWrite := isWriteG

/-- An answer of `casBK` as `casB`'s. -/
def mapAns : Ans w64 → Ans Out
  | .ok v => .ok ⟨false, v⟩
  | .err => .err

theorem psilent_K {c c' : PCfg w64 In} : PSilent casB c c' ↔ PSilent casBK c c' := by
  constructor
  · intro h
    cases h with
    | apply i h => exact PSilent.apply (P := casBK) _ i h
    | perm p h => exact PSilent.perm (P := casBK) _ p h
  · intro h
    cases h with
    | apply i h => exact PSilent.apply (P := casB) _ i h
    | perm p h => exact PSilent.perm (P := casB) _ p h

theorem preach_K {c c' : PCfg w64 In} : PReach casB c c' ↔ PReach casBK c c' := by
  constructor
  · intro h
    induction h with
    | refl c => exact PReach.refl c
    | step hs _ ih => exact PReach.step (psilent_K.1 hs) ih
  · intro h
    induction h with
    | refl c => exact PReach.refl c
    | step hs _ ih => exact PReach.step (psilent_K.2 hs) ih

theorem pstep_K {c c₁ : PCfg w64 In} {i : In} {a : Ans w64} :
    PStep casB c i (mapAns a) c₁ ↔ PStep casBK c i a c₁ := by
  constructor
  · intro h
    generalize hA : mapAns a = A at h
    cases h with
    | ok ho =>
      have hk := applyG_known c.st i
      cases a with
      | ok v =>
        simp only [mapAns, Ans.ok.injEq] at hA
        have hv : v = (applyG c.st i).2.V' := by
          have := congrArg Out.V' hA; exact this
        subst hv
        exact PStep.ok (P := casBK) c i rfl
      | err => simp [mapAns] at hA
    | errW h ho =>
      cases a with
      | ok v => simp [mapAns] at hA
      | err => exact PStep.errW (P := casBK) c i h rfl
    | errR h ho =>
      cases a with
      | ok v => simp [mapAns] at hA
      | err => exact PStep.errR (P := casBK) c i h rfl
    | obs o h ho => exact absurd h (by simp [casB])
  · intro h
    cases h with
    | ok ho =>
      have hk := applyG_known c.st i
      have he : (mapAns (.ok (casBK.step i c.st).2) : Ans Out) = .ok (casB.step i c.st).2 := by
        simp only [mapAns, casBK, casB, Ans.ok.injEq]
        cases hr : (applyG c.st i).2 with
        | mk u w => rw [hr] at hk; simp only at hk; subst hk; rfl
      rw [he]
      exact PStep.ok (P := casB) c i rfl
    | errW h ho => exact PStep.errW (P := casB) c i h rfl
    | errR h ho => exact PStep.errR (P := casB) c i h rfl
    | obs o h ho => exact absurd h (by simp [casBK])

open Classical in
/-- `casB`'s sequential model on an answer is `casBK`'s on its value. -/
theorem pseq_K (S : PSet w64 In) (i : In) (a : Ans w64) :
    (pSeq casB).step S (i, mapAns a) = (pSeq casBK).step S (i, a) := by
  have hp : ppost casB S i (mapAns a) = ppost casBK S i a := by
    funext c'
    apply propext
    unfold ppost
    constructor
    · rintro ⟨c₀, c, c₁, h0, h1, h2, h3⟩
      exact ⟨c₀, c, c₁, h0, preach_K.1 h1, pstep_K.1 h2, preach_K.1 h3⟩
    · rintro ⟨c₀, c, c₁, h0, h1, h2, h3⟩
      exact ⟨c₀, c, c₁, h0, preach_K.2 h1, pstep_K.2 h2, preach_K.2 h3⟩
  unfold pSeq
  simp only
  rw [hp]

end pure

/-! ## `Codec()`'s bytes -/

section vals
variable [GooseExts] [GoGlobalContext]

/-- `Codec()`'s `EncIn`: `Op`, `A`, `B`, 8 bytes little-endian each. -/
def encInB (i : In) : List w8 := u64Le i.Op' ++ u64Le i.A' ++ u64Le i.B'

/-- `Codec()`'s `EncOut` of `Out{u, v}`: `1` if unknown, else `0`, then `V`. -/
def encOutB (o : Out) : List w8 := (if o.Unknown' then W8 1 else W8 0) :: u64Le o.V'

open Classical in
/-- `Codec()`'s bytes of a value: a boxed `Out`'s, or nothing for any other value (never
encoded). -/
def encOutV (v : GoInterface) : List w8 :=
  if h : ∃ o : Out, v = outV o then encOutB (choose h) else []

end vals

/-! ## The far side's store -/

section base
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [AllG GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The far side's store**: the Gryff register (see the file header). -/
def casR (γ : ProtoNames) : RBase GF w64 In In w64 where
  B := casBK
  sysState σ := regHalf γ σ
  Eop := ↑gryffN
  iv := inV
  ov v := outV ⟨false, v⟩
  unk _ := outV ⟨true, W64 0⟩
  encIn := encInB
  encOut := encOutV
  reads_stay i st h := by
    simp only [casBK, isWriteG, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    show (applyG st i).1 = st
    unfold applyG
    rw [if_neg h.1, if_neg h.2]
  encIn_len i := by simp [encInB, u64Le_length]
  encOut_len v := by
    unfold encOutV
    split
    · simp [encOutB, u64Le_length]
    · simp

instance casR_timeless (γ : ProtoNames) (σ : w64) :
    Timeless ((casR (GF := GF) γ).sysState σ) := by
  unfold casR regHalf; simp only; infer_instance

/-- **The register's linearization point is the Gryff client's update** (`opAU`, for the
caller's postcondition read back through `fromRO`'s value). -/
theorem lin_opAU [NetProtoGS] [RemoteGS] (γ : ProtoNames) (i : In) (Φ : w64 → IProp GF) :
    lin (Gg := Gg) (casR γ) i Φ ⊢ opAU γ (toRI i) (fun _ _ o => Φ (fromRO o).V') := by
  have hs : ∀ v, casBK.step i v =
      ((casApply v (toRI i)).1, (fromRO (casApply v (toRI i)).2).V') := by
    intro v
    show ((applyG v i).1, (applyG v i).2.V') = _
    rw [applyG_casApply]
  refine (lin_linF (casR γ) i Φ).trans ?_
  unfold linF opAU
  show iprop(|={⊤ \ ↑gryffN, ∅}=> ∃ st, regHalf γ st ∗
      (regHalf γ (casBK.step i st).1 ={∅, ⊤ \ ↑gryffN}=∗ Φ (casBK.step i st).2)) ⊢ _
  simp only [hs]
  exact .rfl

end base

end gryff.examples.gryffnet

end Perennial
