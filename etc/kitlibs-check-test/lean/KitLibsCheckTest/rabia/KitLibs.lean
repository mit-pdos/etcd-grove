/-
kitlibs-check's validation on rabia (notes/dsv-kitlibs-check.md): a `KitLibs` equal to rabia's landed
premises (`Dsverify/Spec/rabia/examples/rabianet/TopLevelRobustness.lean`'s ten classes), as the
fields of one class. In a challenge the library `Spec.lean` files would not be shipped (they are the
reference solution), so the agent would write their definitions in this file; kitlibs-check reads both
the same way (it unfolds definitions and structures down to the triples).
-/
module

public import Dsverify.Proof.rabia.examples.rabianet.TopLevelDefs
public import Dsverify.Proof.github_com.rs.zerolog.Init
public import Dsverify.Proof.github_com.rs.zerolog.Spec
public import Dsverify.Proof.github_com.gogo.protobuf.proto.Init
public import Dsverify.Proof.github_com.gogo.protobuf.proto.Spec
public import Dsverify.Proof.github_com.gogo.protobuf.gogoproto.Init
public import Dsverify.Proof.github_com.go_redis.redis.v8.Init
public import Dsverify.Proof.os.signal.Init
public import Dsverify.Proof.os.signal.Spec
public import Dsverify.Proof.math.rand.Spec

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace rabia.examples.rabianet

/-- rabia's landed premises (the file header). -/
class KitLibs [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [GoGlobalContext]
    (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics]
    [github_com.rs.zerolog.Assumptions] : Prop where
  zerolog_init : github_com.rs.zerolog.InitHyp GF
  proto_init : github_com.gogo.protobuf.proto.InitHyp GF
  proto : github_com.gogo.protobuf.proto.Hyps GF
  gogoproto_init : github_com.gogo.protobuf.gogoproto.InitHyp GF
  redis_init : github_com.go_redis.redis.v8.InitHyp GF
  signal_init : os.signal.InitHyp GF
  zerolog : github_com.rs.zerolog.Hyps GF
  rand : math.rand.Hyps GF
  no_signals : os.signal.NoSignals os.signal.quietSigs GF

end rabia.examples.rabianet
end Perennial
