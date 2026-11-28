/-
# The hraft kit on `examples/lib/remote` (notes/dsv-hraft.md, S5): the far side's store

* **The store** `regB`: linkv's pending-writes store (`linkv.PendSpec`) of the register (`service.Reg`,
  absent or a value), on the kit's inputs `HIn` (an `In` that `Codec()` carries: a way below 3, a value
  shorter than 256 bytes, since `EncIn` writes its length in a byte). A put is a write (one of unknown
  outcome is pending), a get in any way a read.
* **The far side's store** `regR g` (`remote.RBase`): the register's state is the half of the ghost
  variable `g` the clients' state at the frontier keeps the other half of (`KitQ.lean`), the update's
  mask `kitE` (the frontier's invariant and the clients' escrow), the Go values and bytes `Codec()`'s.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Base
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.service.FsmDefs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Defs
public import Perennial.Ghost.GhostVar

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

/-! ## The store -/

section store
variable [GooseExts]

/-- An input's fields: put, way, value. -/
abbrev InF := Bool × w64 × GoString

/-- What the kit's inputs satisfy: `DecIn`'s way bound and a value shorter than 256 bytes. -/
def HInOk (x : InF) : Prop := uint.Z x.2.1 ≤ 2 ∧ x.2.2.length < 256

/-- The kit's inputs. -/
abbrev HIn := {x : InF // HInOk x}

instance HIn.countable : Pos.Countable HIn :=
  .ofInjective (fun x : HIn => Pos.Countable.encode x.1)
    (fun a b h => Subtype.ext (Pos.encode_inj h))

/-- An output's fields (not unknown): found, value. -/
abbrev OutF := Bool × GoString

/-- The kit's outputs: a value shorter than 256 bytes (`EncOut` writes its length in a byte). -/
abbrev HOut := {o : OutF // o.2.length < 256}

instance HOut.countable : Pos.Countable HOut :=
  .ofInjective (fun x : HOut => Pos.Countable.encode x.1)
    (fun a b h => Subtype.ext (Pos.encode_inj h))

open Classical in
/-- An output as the kit's (a too long value, which no run has, as nothing found). -/
def bndO (o : OutF) : HOut := if h : o.2.length < 256 then ⟨o, h⟩ else ⟨(false, []), by simp⟩

theorem bndO_of {o : OutF} (h : o.2.length < 256) : bndO o = ⟨o, h⟩ := by
  unfold bndO; rw [dif_pos h]

/-- The register's answer to a read: whether it holds a value, and the value. -/
def regOut (st : service.Reg) : OutF := (st.isSome, st.getD [])

/-- **The register with failed puts** (linkv's pending-writes store): a put sets it and answers
nothing found; a get answers it. -/
def regB : linkv.PendSpec service.Reg HIn HOut where
  init := none
  step i st := if i.1.1 then (some i.1.2.2, bndO (false, [])) else (st, bndO (regOut st))
  isWrite i := i.1.1

theorem regB_reads_stay (j : HIn) (st : service.Reg) (h : regB.isWrite j = false) :
    (regB.step j st).1 = st := by
  simp only [regB] at h ⊢; simp [h]

end store

section vals
variable [GooseExts] [GoGlobalContext]

/-- An input, boxed (`any` holding an `In`). -/
def inV (x : InF) : GoInterface := interface.mkOk In.ty #(In.mk x.1 x.2.1 x.2.2)

/-- A Go `Out` value. -/
def outVal (u f : Bool) (v : GoString) : GoInterface := interface.mkOk Out.ty #(Out.mk u f v)

/-- An output, boxed (not unknown). -/
def outV (o : OutF) : GoInterface := outVal false o.1 o.2

/-- The unknown output, boxed. -/
def unkV : GoInterface := outVal true false []

/-- `Codec()`'s bytes of an input (`EncIn`): the put flag, the way, the value's length and bytes. -/
def encInB (x : InF) : List w8 :=
  (if x.1 then W8 1 else W8 0) :: W8 (uint.Z x.2.1) :: W8 x.2.2.length :: x.2.2

/-- `Codec()`'s bytes of an output `Out{u, f, v}` (`EncOut`). -/
def encOutB (u f : Bool) (v : GoString) : List w8 :=
  (if u then W8 1 else W8 0) :: (if f then W8 1 else W8 0) :: W8 v.length :: v

open Classical in
/-- `Codec()`'s bytes of a value: a short `Out`'s, or nothing for any other value (never
encoded). -/
def encOutV (x : GoInterface) : List w8 :=
  if h : ∃ p : Bool × Bool × GoString, p.2.2.length < 256 ∧ x = outVal p.1 p.2.1 p.2.2
  then encOutB (Classical.choose h).1 (Classical.choose h).2.1 (Classical.choose h).2.2 else []

theorem encInB_len (i : HIn) : (encInB i.1).length < 2 ^ 63 := by
  obtain ⟨⟨p, w, v⟩, -, hv⟩ := i
  simp only [encInB, List.length_cons]
  simp only at hv
  omega

theorem encOutV_len (x : GoInterface) : (encOutV x).length < 2 ^ 63 := by
  unfold encOutV
  split
  · rename_i h
    have := (Classical.choose_spec h).1
    simp only [encOutB, List.length_cons]
    omega
  · simp

end vals

/-! ## The far side's store -/

/-- The clients' escrow's namespace (`KitQ.lean`). -/
def escN : Namespace := nroot.@"hraftesc"

/-- The mask of the store's update: the frontier's invariant and the escrow. -/
def kitE : CoPset := ↑service.frN ∪ ↑escN

section base
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]

/-- **The far side's store**: the register, the model's half of the ghost variable `g` (see the
file header). -/
def regR (g : GName) : RBase GF service.Reg HIn HIn HOut where
  B := regB
  sysState st := ghostVar (A := service.Reg) g (1 : Qp).half st
  Eop := kitE
  iv i := inV i.1
  ov o := outV o.1
  unk _ := unkV
  encIn i := encInB i.1
  encOut := encOutV
  reads_stay i st h := regB_reads_stay i st h
  encIn_len i := encInB_len i
  encOut_len v := encOutV_len v

end base

end github_com.hashicorp.raft.examples.hraftnet
end Perennial
