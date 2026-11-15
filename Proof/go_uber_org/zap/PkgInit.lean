/-
The package-initialization instances of zap and `zapcore`: fact `True` (names only). One home, shared by the server's
`Base.lean` files and the WAL (until 2026-11-15 declared in the cache's `Base.lean` and the WAL's `DepsPkgInit.lean`; notes/wal-lean-integration.md).
-/
module

public import GeneratedProof.go_uber_org.zap
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.io
public import Perennial.Proof.fmt
public import Perennial.Proof.time
public import Perennial.Proof.sync
public import Perennial.Proof.strings
public import Perennial.Proof.errors
public import Perennial.Proof.sort
public import Perennial.Proof.context
public import Perennial.Proof.bytes

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

namespace go_uber_org.zap.zapcore

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_uber_org.zap.zapcore :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_uber_org.zap.zapcore :=
  build_get_is_pkg_init_wf

end go_uber_org.zap.zapcore

namespace go_uber_org.zap

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_uber_org.zap :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_uber_org.zap :=
  build_get_is_pkg_init_wf

end go_uber_org.zap

end init

end Perennial
