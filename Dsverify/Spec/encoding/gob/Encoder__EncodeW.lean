/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/gob/Encoder__EncodeW.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`enc.Encode(v)`, `enc` fresh, `v` an `*MSync`, over a writer `w` that appends to an abstract
stream `S` (`writeSink`). What Go's `Encoder.Encode` does (`encoder.go`, `EncodeValue`): it
encodes the type definitions the value needs and writes each as a message (`writeMessage`, one
`w.Write` each), then encodes the value, iterating its maps in the run time's order, and writes
it as one message unless it is too big (`tooBig`); after a failed `Write` it may still write the
remaining type definitions (measured, go1.27.3: notes/axiom-review/dsv-fix4/encoding-gob.md), which
`writeSink`'s dead stream absorbs; it returns the first error, or nil. So the bytes it writes, if no `Write` fails, are a gob stream
`bs` of a listing `m'` of `v`'s maps (`GobFmt.bytes m' bs`, `m'` equal to `m` up to the maps'
order, `KitVal.equiv`), in one or more `Write`s of consecutive pieces of `bs`; the size error
cannot happen when every such listing fits (`GobFmt.fits`). The caller's obligations: `□ Q` of
the stream extended by each candidate `bs`, and `Q` closed under prefixes (each `Write`'s
obligation is for a prefix). After a failed `Write` the stream is dead (`writeSink`), so the
postcondition gives the stream extended by `bs` in either case. `v`'s struct and maps are read
with the fraction `dq` and given back.
-/
module

public import Dsverify.Spec.encoding.gob.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.NetRpc

@[expose] public section

noncomputable section

namespace Perennial.encoding.gob

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]
variable [github_com.imdea_software.swiftpaxos.examples.swiftnet.Assumptions]

/-- `enc.Encode(v)` (see the file header). -/
abbrev Encoder.EncodeW.spec : Prop :=
  ∀ (enc : Loc) (e : GoInterfaceOk) (S Q : List w8 → IProp GF) (W : List w8) (l : Loc)
    (dq : DFrac) (m : github_com.imdea_software.swiftpaxos.sp.SyncWire),
  (∀ m', github_com.imdea_software.swiftpaxos.sp.KitVal.equiv (.msync m) (.msync m') →
    encoding.gob.gobFits (GF := GF) m') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.gob ∗
      writeSink e S Q ∗ bufio.prefixClosed Q ∗
      encoding.gob.ownEncoder enc (interface.ok e) ∗ S W ∗ syncOwn l dq m ∗
      □ (∀ (m' : github_com.imdea_software.swiftpaxos.sp.SyncWire) (bs : List w8),
        ⌜github_com.imdea_software.swiftpaxos.sp.KitVal.equiv (.msync m) (.msync m') ∧
          encoding.gob.gobBytes (GF := GF) m' bs⌝ -∗ □ Q (W ++ bs)) }}
    (App (Val (enc @!! go.GoType.PointerType encoding.gob.Encoder.ty @!! go!"Encode"))
      (Val #(interface.mkOk (go.GoType.PointerType github_com.imdea_software.swiftpaxos.swift.MSync.ty) #l)))
  {{ (err : GoInterface), RET #err;
      ∃ (m' : github_com.imdea_software.swiftpaxos.sp.SyncWire) (bs : List w8),
      ⌜github_com.imdea_software.swiftpaxos.sp.KitVal.equiv (.msync m) (.msync m') ∧
        encoding.gob.gobBytes (GF := GF) m' bs⌝ ∗
      syncOwn l dq m ∗ S (W ++ bs) }}

end spec

end Perennial.encoding.gob
