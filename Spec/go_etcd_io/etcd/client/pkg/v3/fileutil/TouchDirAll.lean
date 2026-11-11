/-
`fileutil.TouchDirAll(lg, d)` (WAL W4a, 2026-11-11; the approved W4 Draft's §1.4, `notes/decisions.md`,
"WAL W4a"). Lean-first. Names-only: an axiom at the trust boundary (`Proof/...`), true of the Go code
at the etcd pin `b18c2d500` (`client/pkg/fileutil/fileutil.go:49-85`, with F-N2 and F-N4's part 1)
under the world assumptions of `GooseLang/Ext/AbsDisk/Impl.lean`; the Go evidence is the WAL tester
under the crash harness (`notes/decisions.md`, "WAL W3"). The body is read as one that performs the
abstract-disk extension's `"DirDurable"` step.
-/
module

public import GooseLang.Ext.AbsDisk.Specs
public import Spec.go_uber_org.zap.Defs
public import GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt absDiskExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- **`TouchDirAll(lg, d)`**, `d` a single path element `name` under the durable directory `parent`:
creates `d` if it is missing (`MkdirAll`), and fsyncs its parent whether or not it created it
(F-N2, F-N4's part 1), so on success `d`'s entry and its ancestors' are durable (`dirDurable`).
(No package-initialization premise: `fileutil`'s initializer sets only its lock functions and
`ErrLocked`, which `TouchDirAll` does not read; the package is outside `etc/gen-init.py`'s closure
until W4c.) -/
abbrev fileutil.TouchDirAll.spec : Prop :=
  ∀ (lg : Loc) (d parent name : GoString),
  d = parent ++ go!"/" ++ name → name ≠ [] → W8 47 ∉ name → name ≠ go!"." → name ≠ go!".." →
  {{ zapLoggerOk (GF := GF) lg ∗ dirDurable parent }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.TouchDirAll)) (Val #lg)) (Val #d))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ -∗ dirDurable d }}

end spec

end EtcdGrove
end Perennial
