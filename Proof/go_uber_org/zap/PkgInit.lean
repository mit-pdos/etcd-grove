/-
The package-initialization instances of zap and `zapcore`, and zap's internal packages. One home, shared by the server's
`Base.lean` files and the WAL (until 2026-11-15 declared in the cache's `Base.lean` and the WAL's `DepsPkgInit.lean`; notes/wal-lean-integration.md).
-/
module

public import GeneratedProof.go_uber_org.zap
public import GeneratedProof.go_uber_org.zap.internal.pool
public import GeneratedProof.go_uber_org.zap.internal.color
public import GeneratedProof.go_uber_org.zap.internal
public import GeneratedProof.go_uber_org.zap.internal.stacktrace
public import GeneratedProof.go_uber_org.zap.internal.bufferpool
public import GeneratedProof.go_uber_org.zap.buffer
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.io
public import Perennial.Proof.runtime.Base
public import Perennial.Proof.fmt
public import Perennial.Proof.time
public import Perennial.Proof.sync
public import Perennial.Proof.strings
public import Perennial.Proof.errors
public import Perennial.Proof.sort
public import Perennial.Proof.context
public import Perennial.Proof.bytes
public import Perennial.Proof.math
public import Proof.os.PkgInit
public import Proof.net.url.PkgInit

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

-- zap's internal `pool` and `color` (prove-misc, 2026-11-20: zapcore's package variables call them)
namespace go_uber_org.zap.internal.pool

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_uber_org.zap.internal.pool :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_uber_org.zap.internal.pool :=
  build_get_is_pkg_init_wf

end go_uber_org.zap.internal.pool

namespace go_uber_org.zap.internal.color

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_uber_org.zap.internal.color :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_uber_org.zap.internal.color :=
  build_get_is_pkg_init_wf

end go_uber_org.zap.internal.color

-- `Logger.check` names its stack capture; its package variable is skipped (zap-z1, 2026-11-23)
namespace go_uber_org.zap.internal.stacktrace

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_uber_org.zap.internal.stacktrace :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_uber_org.zap.internal.stacktrace :=
  build_get_is_pkg_init_wf

end go_uber_org.zap.internal.stacktrace

-- `bufferpool` calls its `NewPool` (zap-z1, 2026-11-23)
namespace go_uber_org.zap.buffer

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_uber_org.zap.buffer :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_uber_org.zap.buffer :=
  build_get_is_pkg_init_wf

end go_uber_org.zap.buffer

-- `Logger.check` reads its `Get`; its variables hold a buffer pool and its `Get` method value (zap-z1, 2026-11-23)
namespace go_uber_org.zap.internal.bufferpool

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_uber_org.zap.internal.bufferpool :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_uber_org.zap.internal.bufferpool :=
  build_get_is_pkg_init_wf

end go_uber_org.zap.internal.bufferpool

namespace go_uber_org.zap.zapcore

/-- `zapcore`: `DefaultClock` holds a fixed `systemClock` (prove-initleft, 2026-11-21: zap's
`NewNop`, which zap's initializer runs for `_globalL`, loads it; until then `True`). -/
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_uber_org.zap.zapcore :=
  define_is_pkg_init iprop(∃ c : go_uber_org.zap.zapcore.systemClock,
    typedPointsto (globalAddr go_uber_org.zap.zapcore.DefaultClock) c DFrac.discard)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_uber_org.zap.zapcore :=
  build_get_is_pkg_init_wf

end go_uber_org.zap.zapcore

-- zap's `internal` (types only: `LeveledEnabler`, which zap's `var _` asserts; prove-initleft, 2026-11-21)
namespace go_uber_org.zap.internal

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_uber_org.zap.internal :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_uber_org.zap.internal :=
  build_get_is_pkg_init_wf

end go_uber_org.zap.internal

namespace go_uber_org.zap

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_uber_org.zap :=
  define_is_pkg_init iprop(∃ tmin tmax : _root_.Perennial.time.Time,
    typedPointsto (globalAddr go_uber_org.zap._minTimeInt64) tmin DFrac.discard ∗
    typedPointsto (globalAddr go_uber_org.zap._maxTimeInt64) tmax DFrac.discard)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_uber_org.zap :=
  build_get_is_pkg_init_wf

end go_uber_org.zap

end init

end Perennial
