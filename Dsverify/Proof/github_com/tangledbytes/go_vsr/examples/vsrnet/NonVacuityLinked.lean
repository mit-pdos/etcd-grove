/-
**Test only** (the NON-VACUITY rule; kitgen's `NonVacuityLinked.lean`, notes/dsv-kitgen.md): the
premise of the vr kit's statement (`vr_remote_robust.spec`,
`Dsverify/Spec/github_com/tangledbytes/go_vsr/examples/vsrnet/TopLevelRobustness.lean`) has an
instance, at every machine's heap. It is the only hypothesis-class premise left (no `InitHyp`:
every package initializer of the kit is proved):

  `∀ G L π, letI := heapAt G L; ∃ (_ : DecoderRep remoteGF), JsonHyps`

* the data class, **a concrete definition over the encoding/json model's fields**
  (`models/encoding/json/v2_stream.go`; the main tree's translation `Code/encoding/json.lean`, whose
  `Decoder` struct and typed points-to are generated):
  - `decOkM dec rd I R U`: `dec` points to a `Decoder` reading `rd`, its sticky error nil, its
    buffer `buf` holding the stream's bytes from `baseOffset` on (`R.drop baseOffset`; `buf`'s
    capacity owned, for `fetch`'s appends), the last value's end `prevEnd` within it, and `U` the
    bytes after `prevEnd`; with the stream's resource `I R`;
  - `decErrM dec rd`: `dec` points to a `Decoder` reading `rd` whose sticky error is set (an error
    with a message: `bufio.errOrNil`, as every read error of a connection is, `net.connReadE`);
* `JsonHyps`' two fields over them, **local axioms** (test-only), each the field's own statement at
  these definitions (the main tree translates neither `NewDecoder` nor `Decode`). Why each is true
  of the model, at these definitions: `newDecoder`: `NewDecoder(r)` with `r` non-nil returns
  `&Decoder{r: r}` (`decOkM` at `R = U = []`, `I [] = recvTok cn s P []`); `Decode_frame`:
  `Decode` returns a set sticky error again (`decErrM`); else `readValue` scans `buf` from
  `prevEnd` with the registered codec's `Scan` (`codecSet`) and fetches from the connection
  (`recvTok`, whose protocol `protoOf γ` makes every complete line an event's `encEvent m` with
  its `fact`), so it returns the next value's bytes (the frame `m`'s, `rstreamAt` moving one
  message on) or a read error, kept as the sticky error (`decErrM`); then `*Frame`'s
  `JSONModelUnmarshal` (`unmarshalVia`, proved: `vsrnet.frameUnmarshalOk`) decodes it into a
  fresh `Data` slice.
No statement or proof imports this module: its local axioms are in no trust base.

Why per heap (the statement's `∃` inside `∀ G L`): a representation owns the heap's memory (the
points-to of the model's fields), which depends on the machine's heap, so no one representation
serves every heap.
-/
module

public import Dsverify.Spec.github_com.tangledbytes.go_vsr.examples.vsrnet.TopLevelRobustness

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace github_com.tangledbytes.go_vsr.examples.vsrnet.instances

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

/-! ### The representations, over the model's fields -/

section reps
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [encoding.json.Assumptions]

/-- A healthy `*Decoder` reading `rd` (stream resource `I`), read `R`, unread `U`. -/
def decOkM (dec : Loc) (rd : GoInterface) (I : List w8 → IProp GF) (R U : List w8) : IProp GF :=
  iprop(∃ (d : encoding.json.Decoder) (bs : List w8), dec ↦ d ∗ d.buf' ↦* bs ∗
    ownSliceCap w8 d.buf' (DFrac.own 1) ∗ I R ∗
    ⌜d.r' = rd ∧ d.err' = interface.nil ∧ bs = R.drop (uint.nat d.baseOffset') ∧
      uint.nat d.prevStart' ≤ uint.nat d.prevEnd' ∧ uint.nat d.prevEnd' ≤ bs.length ∧
      U = bs.drop (uint.nat d.prevEnd')⌝)

/-- A `*Decoder` reading `rd` whose sticky error is set. -/
def decErrM (dec : Loc) (rd : GoInterface) : IProp GF :=
  iprop(∃ d : encoding.json.Decoder, dec ↦ d ∗ ⌜d.r' = rd ∧ d.err' ≠ interface.nil⌝ ∗
    bufio.errOrNil d.err')

/-- The decoder representation (at this heap). -/
def decRep : encoding.json.DecoderRep GF := ⟨decOkM, decErrM⟩

end reps

/-! ### The fields: local axioms (test-only) -/

section axioms
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [field_sem : net.FieldAssumptions] [π : NetProtoGS]

attribute [local instance] decRep

/-- **Local axiom (test-only)**: `json.NewDecoder(conn)`, at `decOkM` (file header). -/
axiom local_newDecoder : pkg.events.newDecoder.spec (GF := GF) (hG := hG)

/-- **Local axiom (test-only)**: `dec.Decode(&f)` of a frame, at `decOkM`/`decErrM` (file header). -/
axiom local_Decode_frame : pkg.events.Decoder.Decode_frame.spec (GF := GF) (hG := hG)

/-- **`JsonHyps` holds** at these representations. -/
theorem jsonHyps_holds : JsonHyps (GF := GF) (hG := hG) :=
  ⟨local_newDecoder, local_Decode_frame⟩

end axioms

/-! ### At the statement's heaps -/

section statement
open github_com.mit_pdos.etcd_grove.examples.lib.remote.counter (remoteGF)
attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet
variable [GoGlobalContext] [lctx : GoLocalContext] [go.Semantics]
variable [github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions] [net.FieldAssumptions]

/-- **The non-vacuity instance** (the NON-VACUITY rule): the statement's premise, in its own form
(`vr_remote_robust.spec`: at `remoteGF` and every machine's heap). -/
theorem nonvacuous_premises : ∀ G L (π : NetProtoGS), letI := heapAt G L;
    ∃ (_ : encoding.json.DecoderRep remoteGF), JsonHyps (GF := remoteGF) := by
  intro G L π
  exact ⟨decRep, jsonHyps_holds⟩

end statement

end github_com.tangledbytes.go_vsr.examples.vsrnet.instances
end Perennial
