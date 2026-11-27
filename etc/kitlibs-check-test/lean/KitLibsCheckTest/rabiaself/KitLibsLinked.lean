/-
kitlibs-check's validation on rabia, self-contained: the non-vacuity instance of KitLibsCheckTest/rabiaself/KitLibs.lean.
rabia's library premises have no proved instance (zerolog, gogo proto, go-redis and os/signal are
translated names only; math/rand's specs are hypotheses), so it rests on one axiom per landed class,
confined to this module, each about a library package's functions or initializer: kitlibs-check lists
them for the lab to judge.
-/
module

public import KitLibsCheckTest.rabiaself.Statement

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Net

namespace rabia.examples.rabianet

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [GoGlobalContext]
variable (GF : BundledGFunctors) [HeapGS HasLC.hasLC GF] [go.Semantics]

axiom zerolog_init_ax : github_com.rs.zerolog.InitHyp GF
axiom proto_init_ax : github_com.gogo.protobuf.proto.InitHyp GF
axiom proto_ax : pb.Hyps GF
axiom gogoproto_init_ax : github_com.gogo.protobuf.gogoproto.InitHyp GF
axiom redis_init_ax : github_com.go_redis.redis.v8.InitHyp GF
axiom signal_init_ax : os.signal.InitHyp GF
axiom zerolog_ax [github_com.rs.zerolog.Assumptions] : zl.Hyps GF
axiom rand_ax : rnd.math.rand.Hyps GF
axiom no_signals_ax : sig.NoSignals sig.quietSigs GF
end

attribute [local instance] netExts netExtsSemantics netExtsInterp netExts_hasNet

/-- The non-vacuity instance (the file header). -/
theorem kitLibs_nonvacuity : kitLibs.premise := by
  unfold kitLibs.premise
  intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G L
  letI := heapAt G L
  exact ⟨zerolog_init_ax _, proto_init_ax _, proto_ax _, gogoproto_init_ax _, redis_init_ax _,
    signal_init_ax _, zerolog_ax _, rand_ax _, no_signals_ax _⟩

end rabia.examples.rabianet
end Perennial
