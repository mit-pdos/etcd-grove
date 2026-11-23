/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/gob/NewDecoder.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`gob.NewDecoder(r)` on a `*bufio.Reader` (an `io.ByteReader`, so Go's `NewDecoder` keeps it as the
decoder's reader instead of wrapping it in a `bufio.Reader` of its own): a fresh decoder reading
`r` directly.
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

/-- `NewDecoder(r)`, `r` a `*bufio.Reader`, returns a fresh `*Decoder` reading `r`. -/
abbrev NewDecoder.spec : Prop :=
  ∀ (br : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.encoding.gob }}
    (App (Val (@! encoding.gob.NewDecoder))
      (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
  {{ (dec : Loc), RET #dec;
      encoding.gob.ownDecoder dec (interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br) }}

end spec

end Perennial.encoding.gob
