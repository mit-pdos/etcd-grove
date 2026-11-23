/-
# The gryff kit on `examples/lib/remote` (notes/dsv-gryff.md): the far side's store

* **The register** `casB` (`ModelSet.lean`): linkv's pending-writes store of the register with
  compare-and-swap, kit.go's `apply`; Writes and CASes pending when their outcome is unknown.
* **The far side's store** `casR γ` (`remote.RBase`): the register's state is Gryff's invariant's
  other half (`regHalf γ.proto`, the abstract register), the mask of the update is `gryffN`
  (Gryff's invariant: a replica's step fires a client's update with it open), the Go values are
  boxed `In`/`Out`, the bytes `Codec()`'s (an input 24 bytes, an output 9).
* **Its linearization point is the Gryff client's update** (`lin_opAU`): remote's `lin` is
  `Proto/InvDefs.lean`'s `opAU` at the input's `RegInput` (`toRI`), its output read back
  (`fromRO`).
-/
module

public import Dsverify.Proof.gryff.examples.gryffnet.ModelProof
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
def casR (γ : ProtoNames) : RBase GF w64 In Out where
  B := casB
  sysState σ := regHalf γ σ
  Eop := ↑gryffN
  iv := inV
  ov := outV
  unk _ := outV ⟨true, W64 0⟩
  encIn := encInB
  encOut := encOutV
  reads_stay i st h := by
    simp only [casB, isWriteG, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
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
caller's postcondition read back through `fromRO`). -/
theorem lin_opAU [NetProtoGS] [RemoteGS] (γ : ProtoNames) (i : In) (Φ : Out → IProp GF) :
    lin (Gg := Gg) (casR γ) i Φ ⊢ opAU γ (toRI i) (fun _ _ o => Φ (fromRO o)) := by
  have hs : ∀ v, casB.step i v = ((casApply v (toRI i)).1, fromRO (casApply v (toRI i)).2) :=
    fun v => applyG_casApply v i
  unfold lin opAU
  show iprop(|={⊤ \ ↑gryffN, ∅}=> ∃ st, regHalf γ st ∗
      (regHalf γ (casB.step i st).1 ={∅, ⊤ \ ↑gryffN}=∗ Φ (casB.step i st).2)) ⊢ _
  simp only [hs]
  exact .rfl

end base

end gryff.examples.gryffnet

end Perennial
