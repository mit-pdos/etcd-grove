/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/MarshalSpecs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The swift messages' writers' varint callee: `putVarint` (internal statement, the swift group's).

Perennial's `encoding/binary` gives `PutVarint` as a name only (no body), so the fork (change P1,
notes/prove-swift.md §13) copies Go's `PutVarint`/`PutUvarint` into `swift/varint.go` as
`putVarint`/`putUvarint` and calls them from `defs.go`; this statement is proved from the copy
(`swift.PutVarint.wp_proof`, Proof/swift/PutVarint.lean).

`PutVarint(buf, x)` for a length `x` (`0 ≤ x < 2^62`) into a buffer of at least 10 bytes: the
zig-zag varint of `x` (`sp.varintLen`, Spec/swift/Wire.lean) at the buffer's front, the rest
unchanged; the result is the varint's length.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.BatcherDefs
@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]

/-- `putVarint(buf, x)` (see the file header). -/
def swift.PutVarint.specH : Prop :=
  ∀ (s : GoSlice) (bs : List w8) (x : w64),
  {{ (s ↦* bs : IProp netDistGF) ∗ ⌜10 ≤ bs.length ∧ 0 ≤ sint.Z x ∧ sint.Z x < 2 ^ 62⌝ }}
    (App (App (Val (@! swift.putVarint)) (Val #s)) (Val #x))
  {{ (n : w64), RET #n;
      ⌜sint.Z n = ((sp.varintLen (sint.nat x)).length : Int)⌝ ∗
      s ↦* (sp.varintLen (sint.nat x) ++ bs.drop (sp.varintLen (sint.nat x)).length) }}

/-- `(*MNewLeader).Marshal` (the run loop's recovery arm sends it with `SendToAll`; the struct
is read only: the run loop persists it before sending it). -/
def swift.MNewLeader.marshalH : Prop :=
  ∀ (l : Loc) (r b : w32), sp.Msg.wf (.newLeader r b) →
    ⊢ sp.marshalOk (interface.mkOk (go.GoType.PointerType swift.MNewLeader.ty) #l) (.newLeader r b)
        iprop(typedPointsto l (swift.MNewLeader.mk r b) DFrac.discard)

end specs

end Perennial.github_com.imdea_software.swiftpaxos
