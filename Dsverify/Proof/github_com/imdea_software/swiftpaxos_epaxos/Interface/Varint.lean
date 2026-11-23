/-
Split out of dsverify-lab examples/epaxos/proof/Epaxos/Interface/Marshal.lean (notes/dsv-epaxos.md):
`epaxos`'s `putVarint` (`epaxos/varint.go`, a byte-identical copy of `encoding/binary`'s), which
needs no bufio, and the packages' initialization facts the marshal layer names. The port of
`Interface/Marshal` imports this file and does not restate them.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.PeerWire
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.defs.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.state.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- A list length below `2^63` as a signed word (the lab's `Harness/NetLib.lean`). -/
theorem sint_Z_W64_length {n : Nat} (h : n < 2 ^ 63) : sint.Z (W64 n) = n := by
  have : ((n : Int) : w64).toInt = (n : Int) := by
    rw [BitVec.toInt_intCast]; apply Int.bmod_eq_of_le <;> omega
  exact this

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]

/-- The packages' initialization facts. -/
abbrev pkgInit_state : IProp GF :=
  isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.state
abbrev pkgInit_defs : IProp GF :=
  isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.replica.defs
abbrev pkgInit_epaxos : IProp GF :=
  isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.epaxos

variable [epaxos.Assumptions]

/-- `putVarint(buf, x)` (`len(buf)` at least the encoding's length): writes `varintEnc x` at the
front of `buf`, returns its length. -/
def epaxos.putVarint.spec : Prop :=
  ∀ (buf : GoSlice) (bs : List w8) (x : w64),
  {{ pkgInit_epaxos (GF := GF) ∗ ⌜(varintEnc x).length ≤ bs.length⌝ ∗ buf ↦* bs }}
    (App (App (Val (@! epaxos.putVarint)) (Val #buf)) (Val #x))
  {{ RET #(W64 (varintEnc x).length);
      buf ↦* (varintEnc x ++ bs.drop (varintEnc x).length) }}

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
