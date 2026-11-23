/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/gob/Decoder__Decode.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`dec.Decode(v)`, `dec` fresh over a `*bufio.Reader` `rd` (`ownDecoder`: no read-ahead), `v` an
`*MSync` holding the zero value (the kit's `MSync.New()`). What Go's `Decoder.Decode` does
(`decoder.go`): it reads messages, each by `io.ReadFull` of its length (a gob unsigned integer)
and then of its contents, until a value message, installing the type definitions before it, and
decodes the value into `*v` (a map sent is made and filled: `v` held zero maps). So it reads some
bytes `data` from `rd` (`readsOk`), and when it returns nil:
* `data` ends with the value's message, so if the stream holds a fresh encoder's gob stream `bs` of
  some `m` (`GobFmt.bytes m bs`) where `data` began, `data` is `bs` (it read through the first
  value message, `bs`'s last), and
* `*v` holds `m` up to the maps' order (`KitVal.equiv`: the decoded maps' listing is the run
  time's).
Given for every such `m` and `bs`: the decoder does not know what the stream was meant to hold.
On an error (a short read, the connection's, or bytes that are not such a stream) `*v` is given
up (it may be partly filled).
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

/-- `dec.Decode(v)` (see the file header). -/
abbrev Decoder.Decode.spec : Prop :=
  ∀ (dec : Loc) (rd : GoInterface) (I : List w8 → IProp GF) (R : List w8) (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.gob ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
      bufio.readsOk rd I ∗ I R ∗ encoding.gob.ownDecoder dec rd ∗
      l ↦ (Perennial.zero_val github_com.imdea_software.swiftpaxos.swift.MSync) }}
    (App (Val (dec @!! go.GoType.PointerType encoding.gob.Decoder.ty @!! go!"Decode"))
      (Val #(interface.mkOk (go.GoType.PointerType github_com.imdea_software.swiftpaxos.swift.MSync.ty) #l)))
  {{ (e : GoInterface), RET #e; ∃ data : List w8, I (R ++ data) ∗
      ((⌜e = interface.nil⌝ ∗ ∃ m' : github_com.imdea_software.swiftpaxos.sp.SyncWire,
          ⌜∀ (m : github_com.imdea_software.swiftpaxos.sp.SyncWire) (bs u w : List w8),
            encoding.gob.gobBytes (GF := GF) m bs → data ++ u = bs ++ w →
            data = bs ∧ github_com.imdea_software.swiftpaxos.sp.KitVal.equiv (.msync m) (.msync m')⌝ ∗
          syncOwn l (DFrac.own 1) m') ∨
        ⌜e ≠ interface.nil⌝) }}

end spec

end Perennial.encoding.gob
