/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/gob/Defs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The vocabulary of the specs of the real `encoding/gob` (names only here: its specs are hypotheses,
`SwiftHyps`) as SwiftPaxos's `MSync` uses it (`swift/defs.go`: `Marshal` is
`gob.NewEncoder(w).Encode(m)`, `Unmarshal` is `gob.NewDecoder(r).Decode(m)`, a fresh encoder and a
fresh decoder per message).

**Port change (the lab's gob was a model).** The lab's `encoding/gob` model framed the kit codec's
bytes (`codecSet`: its `codec` variable held the kit's `rpcEncode`/`rpcDecode`; `gobFrame`: an
8-byte length, then the codec's encoding). The real `encoding/gob` writes neither: a fresh encoder
writes the type definitions of the types it sends, then the value, in gob's own encoding. The
specs here are stated over that real format, abstractly (`sp.GobFmt`, Spec/swift/Wire.lean):
* `ownEncoder enc w`: the `*gob.Encoder` at `enc` is fresh (has sent nothing) and writes to `w`;
  `Encode` uses it up (a second `Encode` on it would not resend the type definitions: the kit never
  does that).
* `ownDecoder dec r`: the `*gob.Decoder` at `dec` is fresh (has read nothing) and reads `r`
  directly: `r` is a `*bufio.Reader` (`NewDecoder` wraps any reader that is not an
  `io.ByteReader` in a `bufio.Reader` of its own, which would read ahead; the kit passes a replica's
  peer `*bufio.Reader`).
* `syncOwn l dq m`: the `*MSync` at `l` holds `m` (`structOwn`, the lab kit's representation:
  its maps listed in `m`'s order).
* `writeSink e S Q`: the writer `e`'s `Write` appends the bytes to the abstract stream `S` (the
  caller's obligation `□ Q` of the extended stream), and after a `Write` that fails the stream is
  dead (`∀ X, S X`: a `*bufio.Writer`'s error is sticky, `wire.wsink`): what `Encode`, which stops
  at its first failed `Write`, needs to give the whole value's stream back.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Wire
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Codec

@[expose] public section

noncomputable section

namespace Perennial.encoding.gob

open Iris Iris.BI Iris.ProgramLogic Iris.Std Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp

section defs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [github_com.imdea_software.swiftpaxos.examples.swiftnet.Assumptions]

/-- gob's format (`sp.GobFmt`, the libraries' `SwiftLibs.gobFmt`) at any `GF`: at `netDistGF` the
same as the instance `swiftGobFmt`'s (by definition). -/
abbrev gobBytes [l : github_com.imdea_software.swiftpaxos.SwiftLibs GF]
    (m : github_com.imdea_software.swiftpaxos.sp.SyncWire) (bs : List w8) : Prop :=
  l.gobFmt.bytes m bs

abbrev gobFits [l : github_com.imdea_software.swiftpaxos.SwiftLibs GF]
    (m : github_com.imdea_software.swiftpaxos.sp.SyncWire) : Prop :=
  l.gobFmt.fits m

/-- The lab model's `codecSet` (its `codec` variable held the kit codec's functions), kept as a
name so that the invariants that carry it (`RunInv`, `New`'s spec, `handleNewLeaderAckNs`'s
spec) need not change: the real `encoding/gob` has no codec to set, so it is `True` (to be
dropped from them). -/
def codecSet : IProp GF := iprop(True)

instance codecSet_persistent : Persistent (codecSet (GF := GF)) := by
  unfold codecSet; infer_instance

/-- A fresh `*gob.Encoder` at `enc` writing to `w` (`SwiftLibs.gobEncoder`). -/
def ownEncoder [l : github_com.imdea_software.swiftpaxos.SwiftLibs GF] (enc : Loc)
    (w : GoInterface) : IProp GF :=
  l.gobEncoder hG enc w

/-- A fresh `*gob.Decoder` at `dec` reading `r` directly (`SwiftLibs.gobDecoder`). -/
def ownDecoder [l : github_com.imdea_software.swiftpaxos.SwiftLibs GF] (dec : Loc)
    (r : GoInterface) : IProp GF :=
  l.gobDecoder hG dec r

/-- The `*MSync` at `l` holds `m` (see the file header). -/
def syncOwn (l : Loc) (dq : DFrac) (m : github_com.imdea_software.swiftpaxos.sp.SyncWire) :
    IProp GF :=
  github_com.imdea_software.swiftpaxos.structOwn github_com.imdea_software.swiftpaxos.swift.MSync.ty
    l dq (.msync m)

/-- `w.Write` appends to the stream `S`, which dies when a `Write` fails (see the file
header). -/
def writeSink (e : GoInterfaceOk) (S Q : List w8 → IProp GF) : IProp GF :=
  iprop(□ ∀ (p : GoSlice) (dq : DFrac) (W bs : List w8) (Φ : val → IProp GF),
      S W -∗ □ Q (W ++ bs) -∗ p ↦*{dq} bs -∗
      ▷ (∀ (nn : w64) (err : GoInterface),
          ((⌜err = interface.nil⌝ ∗ S (W ++ bs)) ∨ (⌜err ≠ interface.nil⌝ ∗ ∀ X, S X)) -∗
          p ↦*{dq} bs -∗ Φ (PairV #nn #err)) -∗
      WP (App (Val #(methods e.ty go!"Write" e.v)) (Val #p)) {{ Φ }})

instance writeSink_persistent (e : GoInterfaceOk) (S Q : List w8 → IProp GF) :
    Persistent (writeSink e S Q) := by
  unfold writeSink; infer_instance

end defs

end Perennial.encoding.gob
