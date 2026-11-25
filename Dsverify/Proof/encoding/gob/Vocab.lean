/-
The fixed vocabulary of `encoding/gob`'s per-function axioms (dsv-fix4, mit-pdos/etcd-grove#49 fix 4;
SwiftPaxos's `MSync` over gob). Until dsv-fix4 swiftpaxos's statement quantified it, `∀ (l :
SwiftNetPkgState netDistGF)`, and took the gob specs over `l` as the premise `SwiftHyps`
(`Dsverify/Proof/github_com/imdea_software/swiftpaxos/Hyps.lean`); now the predicates are fixed
here and the specs are axioms over them (`NewEncoder.lean`, `NewDecoder.lean`,
`Encoder__EncodeW.lean`, `Decoder__Decode.lean`).

* **gob's wire format for an `*MSync`** (`sp.GobFmt`, whose docstring argues each law of Go's
  `encoding/gob`, `Dsverify/Spec/github_com/imdea_software/swiftpaxos/swift/Wire.lean`): the opaque
  predicates `wireBytes m bs` (`bs` is what a fresh `gob.Encoder` may write for one `*MSync` holding
  `m`) and `wireFits m` (its value message is under the encoder's limit), and their laws as
  **trust-boundary axioms** (`wireBytes_peel`, `wireFits_of`, `wireBytes_exists`), each the field of
  `sp.GobFmt` verbatim, `wireFmt` the instance they make.
* **an encoder's and a decoder's state**: `encoderTok hG enc w` (a fresh `*gob.Encoder` at `enc`
  writing to `w`) and `decoderTok hG dec r` (a fresh `*gob.Decoder` at `dec` reading `r`
  directly), opaque: real gob's.
* `swiftLibsOf π`: SwiftPaxos's libraries' state (`SwiftNetPkgState`) at the net protocols' names `π`,
  over these.
Review: `notes/axiom-review/dsv-fix4/encoding-gob.md`.
-/
module

public import Dsverify.Spec.encoding.gob.Defs

@[expose] public section

noncomputable section

namespace Perennial.encoding.gob

open Iris Iris.BI Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp

open github_com.imdea_software.swiftpaxos (SwiftNetPkgState)
open github_com.imdea_software.swiftpaxos.sp (SyncWire KitVal GobFmt)

/-- `bs` is what a fresh `gob.Encoder` may write for one `*MSync` holding `m` (`GobFmt.bytes`).
Opaque: real gob's. -/
opaque wireBytes : SyncWire → List w8 → Prop

/-- The value message of `m` is shorter than the encoder's limit (`GobFmt.fits`). Opaque: real
gob's. -/
opaque wireFits : SyncWire → Prop

/-- **Trust-boundary axiom** (`GobFmt.peel`): a gob stream of one value is self-delimiting and
determines the value. -/
axiom wireBytes_peel : ∀ {a b : SyncWire} {ba bb x y : List w8}, wireBytes a ba → wireBytes b bb →
    ba ++ x = bb ++ y → a = b ∧ ba = bb

/-- **Trust-boundary axiom** (`GobFmt.fits_of`): a value whose lab-codec measure is under `2 ^ 31`
bytes fits. -/
axiom wireFits_of : ∀ m : SyncWire, m.cEnc.length < 2 ^ 31 → wireFits m

/-- **Trust-boundary axiom** (`GobFmt.exists_bytes`): an `*MSync` with distinct map keys that fits
is encoded as a stream of some listing of its maps. -/
axiom wireBytes_exists : ∀ m : SyncWire, KitVal.wf (.msync m) → wireFits m →
    ∃ (m' : SyncWire) (bs : List w8), KitVal.equiv (.msync m) (.msync m') ∧ wireBytes m' bs

/-- gob's format over the fixed predicates. -/
def wireFmt : GobFmt := ⟨wireBytes, wireBytes_peel, wireFits, wireFits_of, wireBytes_exists⟩

section toks
variable [go_gctx : GoGlobalContext] {GF : BundledGFunctors}

/-- A fresh `*gob.Encoder` at `enc` writing to `w`. Opaque: real gob's. -/
opaque encoderTok : HeapGS HasLC.hasLC GF → Loc → GoInterface → IProp GF :=
  fun _ _ _ => iprop(True)

/-- A fresh `*gob.Decoder` at `dec` reading `r` directly. Opaque: real gob's. -/
opaque decoderTok : HeapGS HasLC.hasLC GF → Loc → GoInterface → IProp GF :=
  fun _ _ _ => iprop(True)

/-- SwiftPaxos's libraries' state at the net protocols' names `π`, over the fixed vocabulary. -/
def swiftLibsOf (π : Net.NetProtoGS) : SwiftNetPkgState GF :=
  { toSwiftLibs := { toNetProtoGS := π, gobFmt := wireFmt, gobEncoder := encoderTok,
                     gobDecoder := decoderTok } }

end toks

end Perennial.encoding.gob
