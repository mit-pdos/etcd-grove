/-
# The vr kit on `examples/lib/remote` (notes/dsv-vr.md, step 3): the far side's store
* **The store** `kvB`: linkv's pending-writes store (`linkv.PendSpec`) of the key-value map
  (`Store`, the ghost layer's abstract state), on the kit's inputs `KIn` (an input the ghost layer
  accepts, `InputOk`, `InputBounded`, with a key shorter than 256 bytes: `Codec()`'s `EncIn` writes
  its length in a byte). A get is a read, a put a write (one of unknown outcome is pending).
* **The far side's store** `kvR g` (`remote.RBase`): the map's state is the ghost layer's abstract
  half (`absOwnI g`), the update's mask `vsrE` (every invariant of the ghost layer), the Go values
  and bytes `Codec()`'s. Its linearization point is the ghost layer's client update: `lin_AUof`.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Ghost.System
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Pend
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open VsrModel VsrGhost.Impl

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

attribute [local instance] kvInCountable

section store
variable [GooseExts]

/-! ## The store -/

/-- What the kit's inputs satisfy: the ghost layer's `InputOk` and `InputBounded`, and a key
shorter than 256 bytes (`EncIn` writes its length in a byte). -/
def KInOk (i : KvInI) : Prop :=
  InputOk i ∧ InputBounded i ∧ (match i with | .get k => k.length | .put k _ => k.length) < 256

/-- The kit's inputs. -/
abbrev KIn := {i : KvInI // KInOk i}

instance KIn.countable : Pos.Countable KIn :=
  .ofInjective (fun x : KIn => Pos.Countable.encode x.1)
    (fun a b h => Subtype.ext (Pos.encode_inj h))

@[reducible] instance (priority := high) KIn.beq : BEq KIn := instBEqOfDecidableEq

/-- The key-value map's outputs, countable. -/
instance KvOutI.countable : Pos.Countable KvOutI :=
  countableOfLeftInverse
    (fun o : KvOutI => match o with
      | .got v => (Sum.inl v : Option GoString ⊕ Unit)
      | .done => .inr ())
    (fun x => match x with | .inl v => .got v | .inr _ => .done)
    (fun o => by cases o <;> rfl)

/-- The key-value map's step, as a function (`kvStep` is its graph: `kvStep_fn`). -/
def kvFn (σ : VsrModel.Store) : KvInI → VsrModel.Store × KvOutI
  | .get k => (σ, .got (σ k))
  | .put k v => ((fun k' => if k' = k then some v else σ k'), .done)

theorem kvStep_fn (σ σ' : VsrModel.Store) (i : KvInI) (o : KvOutI) :
    kvStep σ i σ' o ↔ (σ', o) = kvFn σ i := by
  cases i <;> simp [kvStep, kvFn, _root_.and_comm]

/-- What the kit's outputs satisfy: a found value is shorter than 2^16 bytes (the store's values
are inputs' values, `InputBounded`); `Codec()`'s bytes then have a bounded length. -/
def KOutOk : KvOutI → Prop
  | .got (some v) => v.length < 2 ^ 16
  | _ => True

/-- The kit's outputs. -/
abbrev KOut := {o : KvOutI // KOutOk o}

instance KOut.countable : Pos.Countable KOut :=
  .ofInjective (fun x : KOut => Pos.Countable.encode x.1)
    (fun a b h => Subtype.ext (Pos.encode_inj h))

open Classical in
/-- An output as the kit's (a too long found value, which no run of the kit has, as `got none`). -/
def bndO (o : KvOutI) : KOut :=
  if h : KOutOk o then ⟨o, h⟩ else ⟨.got none, trivial⟩

theorem bndO_of {o : KvOutI} (h : KOutOk o) : bndO o = ⟨o, h⟩ := by
  unfold bndO; rw [dif_pos h]

/-- The key-value map with failed puts (linkv's pending-writes store). -/
def kvB : linkv.PendSpec VsrModel.Store KIn KOut where
  init := fun _ => none
  step i σ := ((kvFn σ i.1).1, bndO (kvFn σ i.1).2)
  isWrite i := match i.1 with | .get _ => false | .put _ _ => true

end store

section vals
variable [GooseExts] [GoGlobalContext]

/-- An input as `In`'s fields. -/
def inFields : KvInI → Bool × GoString × GoString
  | .get k => (false, k, [])
  | .put k v => (true, k, v)

/-- An input, boxed (`any` holding an `In`). -/
def inV (i : KvInI) : GoInterface :=
  interface.mkOk In.ty #(In.mk (inFields i).1 (inFields i).2.1 (inFields i).2.2)

/-- An output's fields `(Done, Found, V)` (`Out`, not unknown). -/
def outFields : KvOutI → Bool × Bool × GoString
  | .done => (true, false, [])
  | .got none => (false, false, [])
  | .got (some v) => (false, true, v)

/-- A Go `Out` value. -/
def outVal (u d f : Bool) (v : GoString) : GoInterface := interface.mkOk Out.ty #(Out.mk u d f v)

/-- An output, boxed (`any` holding an `Out`; not unknown). -/
def outV (o : KvOutI) : GoInterface := outVal false (outFields o).1 (outFields o).2.1 (outFields o).2.2

/-- The unknown output, boxed. -/
def unkV : GoInterface := outVal true false false []

/-- An answer, boxed. -/
def ansV : linkv.Ans KOut → GoInterface
  | .ok o => outV o.1
  | .err => unkV

/-- `Codec()`'s bytes of an input (`EncIn`): its kind, its key's length, its key and value. -/
def encInB (i : KvInI) : List w8 :=
  (if (inFields i).1 then W8 1 else W8 0) :: W8 (inFields i).2.1.length ::
    ((inFields i).2.1 ++ (inFields i).2.2)

/-- `Codec()`'s bytes of an output `Out{u, d, f, v}` (`EncOut`). -/
def encOutB (u d f : Bool) (v : GoString) : List w8 :=
  (if u then W8 1 else W8 0) :: (if d then W8 1 else W8 0) :: (if f then W8 1 else W8 0) :: v

open Classical in
/-- `Codec()`'s bytes of a value: a short `Out`'s, or nothing for any other value (never
encoded). -/
def encOutV (x : GoInterface) : List w8 :=
  if h : ∃ p : Bool × Bool × Bool × GoString, p.2.2.2.length < 2 ^ 16 ∧
      x = outVal p.1 p.2.1 p.2.2.1 p.2.2.2
  then encOutB (Classical.choose h).1 (Classical.choose h).2.1 (Classical.choose h).2.2.1
    (Classical.choose h).2.2.2 else []

theorem encInB_len (i : KIn) : (encInB i.1).length < 2 ^ 63 := by
  obtain ⟨i, -, hb, -⟩ := i
  cases i <;> simp only [InputBounded] at hb <;> simp [encInB, inFields] <;> omega

theorem encOutV_len (x : GoInterface) : (encOutV x).length < 2 ^ 63 := by
  unfold encOutV
  split
  · rename_i h
    have := (Classical.choose_spec h).1
    simp only [encOutB, List.length_cons]
    omega
  · simp

open Classical in
/-- porcupine's operations as the store's: a boxed input and a boxed answer; anything else
decodes to nothing. -/
def kvDec (io : OpV) : Option (KIn × linkv.Ans KOut) :=
  if h : ∃ (i : KIn) (a : linkv.Ans KOut), io = (inV i.1, ansV a) then
    some (Classical.choose h, Classical.choose (Classical.choose_spec h))
  else none

/-- **The store's porcupine model**, as the pending library's invariant sees it: `pSeq kvB`
through `kvDec`. -/
def kvS0 {GF : BundledGFunctors} : ModelSpec GF (linkv.PSet VsrModel.Store KIn) where
  M := linkv.pM kvB kvDec
  rep _ _ _ := iprop(True)
  ioOk i o := iprop(⌜(∃ x : KIn, i = inV x.1) ∧ ∃ a : linkv.Ans KOut, o = ansV a⌝)
  ioOk_pers _ _ := by infer_instance

end vals

/-! ## The far side's store -/

section base
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]

/-- **The far side's store**: the key-value map of the ghost layer (see the file header). -/
def kvR (g : GN) : RBase GF VsrModel.Store KIn KOut where
  B := kvB
  sysState σ := absOwnI g σ
  Eop := vsrE
  iv i := inV i.1
  ov o := outV o.1
  unk _ := unkV
  encIn i := encInB i.1
  encOut := encOutV
  reads_stay i st h := by
    revert h
    obtain ⟨i, -⟩ := i
    cases i <;> simp [kvB, kvFn]
  encIn_len i := encInB_len i
  encOut_len v := encOutV_len v

instance kvR_timeless (g : GN) (σ : VsrModel.Store) : Timeless ((kvR (GF := GF) g).sysState σ) := by
  unfold kvR; simp only; infer_instance

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The store's linearization point is the ghost layer's client update** (`AUof`, which a
client registers with its request: `ghost_register`), for the caller's postcondition of the
output. -/
theorem lin_AUof [NetProtoGS] (g : GN) (i : KIn) (Φ : KOut → IProp GF) :
    lin (Gg := Gg) (kvR g) i Φ ⊢ AUof g i.1 (fun _ _ o => Φ (bndO o)) := by
  unfold lin AUof
  simp only [kvR, kvB]
  iintro H
  imod H with ⟨%σ, Hσ, Hc⟩
  imodintro
  iexists σ
  iframe Hσ
  iintro %σ' %o ⟨Hσ', %hs⟩
  have h := (kvStep_fn σ σ' i.1 o).1 hs
  rw [← h]
  iapply Hc $$ Hσ'

end base

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial
