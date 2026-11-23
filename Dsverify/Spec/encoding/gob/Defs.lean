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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [net.rpc.RpcKit]

/-- The `*gob.Codec` `c` holds the kit's encoding and decoding functions, for good. -/
def codecFns (c : Loc) : IProp GF :=
  iprop(structFieldRef encoding.gob.Codec go!"Encode" c ↦□ net.rpc.kitFn go!"rpcEncode" ∗
    structFieldRef encoding.gob.Codec go!"Decode" c ↦□ net.rpc.kitFn go!"rpcDecode")

/-- The model's `codec` holds a non-nil codec with the kit's functions, for good. -/
def codecSet : IProp GF :=
  iprop(∃ c : Loc, ⌜c ≠ null⌝ ∗ globalAddr encoding.gob.codec ↦□ c ∗ codecFns c)

instance codecFns_persistent (c : Loc) : Persistent (codecFns (GF := GF) c) := by
  unfold codecFns; infer_instance

instance codecSet_persistent : Persistent (codecSet (GF := GF)) := by
  unfold codecSet; infer_instance

end defs

end Perennial.encoding.gob
