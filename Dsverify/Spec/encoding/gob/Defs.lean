/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/gob/Defs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The vocabulary of the specs of the lab's `encoding/gob` model (`Swift.Code.encoding.gob`, the
harness's `rpcmodel/src/encoding/gob`) as SwiftPaxos's `MSync` uses it:
* `codecFns c`: the `*gob.Codec` `c` holds the kit's codec functions (`rpcEncode`, `rpcDecode`,
  the same as the net/rpc model's: the kit's generated `registerRPC` registers them with both),
  for good (persistent);
* `codecSet`: the model's `codec` variable holds such a codec, for good (persistent; made by
  `SetCodec`; every `getCodec` then returns it).
The model's package state (`SwiftNetPkgState.gob`, the run's choice) must keep `codec` nil or
such a codec under `codecMu` (as `net.rpc`'s `codecInv`); the specs take its `isPkgInit`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Wire

@[expose] public section

noncomputable section

namespace Perennial.encoding.gob

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section defs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors}

attribute [local instance] Dsv.netShaExts

/-- The gob codec encodes and decodes as the kit's `RpcCodec`, for good (persistent): a
hypothesis (`SwiftLibs.gobCodecSet`). The lab's was its model's `codec` variable holding the
kit's functions; `encoding/gob` is names only here. -/
def codecSet [l : github_com.imdea_software.swiftpaxos.SwiftLibs GF] : IProp GF :=
  l.gobCodecSet

instance codecSet_persistent [l : github_com.imdea_software.swiftpaxos.SwiftLibs GF] :
    Persistent (codecSet (GF := GF)) := l.gobCodecSet_persistent

/-- The `*gob.Encoder` at `enc` writes to `w` (`SwiftLibs.gobEncoder`). -/
def ownEncoder [l : github_com.imdea_software.swiftpaxos.SwiftLibs GF] (enc : Loc) (dq : DFrac)
    (w : GoInterface) : IProp GF :=
  l.gobEncoder enc dq w

/-- The `*gob.Decoder` at `dec` reads from `r` (`SwiftLibs.gobDecoder`). -/
def ownDecoder [l : github_com.imdea_software.swiftpaxos.SwiftLibs GF] (dec : Loc) (dq : DFrac)
    (r : GoInterface) : IProp GF :=
  l.gobDecoder dec dq r

end defs

end Perennial.encoding.gob
