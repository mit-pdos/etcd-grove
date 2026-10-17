/- Lean-first (no Rocq counterpart).

# Adequacy of the register's cluster driver (2026-10-12)

A closed theorem about the operational semantics of `Main()` (`examples/register/cluster.go`):
the program `initialize'(); Main()` -- the register package's initialization (which
initializes its dependencies, raft's among them, then the package itself) followed by
`Main` -- is safe (`MainSafe`, `examples/Adequacy.lean`) from a fresh state (no package
initialized): for every real execution from one thread, of any length, it never gets stuck,
no thread of it ends in a panic, and the main thread's result, if it has one, is `#()`.

It is `mainSafe_of_wp` (`examples/Adequacy.lean`) with the WP from `register_Main`
(`Spec/.../register/Main.lean`) and the register package's `wp_initialize'` (`Init.lean`); what
is the register's own here is the program and the post-initialization table of the packages it
reaches (`pkgInitTable`).

The statement is parametric in the Go semantics, as every Perennial result is: the
`GoGlobalContext`, the language semantics `go.Semantics` at the initial state's local
context and the package assumptions `register.Assumptions` (the translated function bodies
behind each name, the struct layouts, recursively for the imported packages) are instance
arguments.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.Adequacy

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] disk_op disk_model disk_semantics disk_interp

/-! ## Package initialization's starting point -/

section pkgs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]

/-- The post-initialization predicate of every package the register (transitively)
imports, and of the register itself: what `ownInitializing` hands out for an initialized
package. -/
def pkgInitTable : List (GoString × IProp GF) :=
  [(pkg_id.github_com.mit_pdos.etcd_grove.examples.register,
      isPkgInit pkg_id.github_com.mit_pdos.etcd_grove.examples.register),
   (pkg_id.sync, isPkgInit pkg_id.sync),
   (pkg_id.internal.synctest, isPkgInit pkg_id.internal.synctest),
   (pkg_id.internal.race, isPkgInit pkg_id.internal.race),
   (pkg_id.sync.atomic, isPkgInit pkg_id.sync.atomic),
   (pkg_id.encoding.binary, isPkgInit pkg_id.encoding.binary),
   (pkg_id.slices, isPkgInit pkg_id.slices),
   (pkg_id.math.bits, isPkgInit pkg_id.math.bits),
   (pkg_id.«unsafe», isPkgInit pkg_id.«unsafe»),
   (pkg_id.cmp, isPkgInit pkg_id.cmp),
   (pkg_id.math, isPkgInit pkg_id.math),
   (pkg_id.io, isPkgInit pkg_id.io),
   (pkg_id.errors, isPkgInit pkg_id.errors),
   (pkg_id.go_etcd_io.raft.v3.raftpb, isPkgInit pkg_id.go_etcd_io.raft.v3.raftpb),
   -- raft v3.7 (stage R6b): protobuf-go's packages (`proto`, its reflection and runtime), which
   -- raft, `raftpb` and the register import
   (pkg_id.google_golang_org.protobuf.proto, isPkgInit pkg_id.google_golang_org.protobuf.proto),
   (pkg_id.google_golang_org.protobuf.reflect.protoreflect,
      isPkgInit pkg_id.google_golang_org.protobuf.reflect.protoreflect),
   (pkg_id.google_golang_org.protobuf.runtime.protoimpl,
      isPkgInit pkg_id.google_golang_org.protobuf.runtime.protoimpl),
   (pkg_id.google_golang_org.protobuf.internal.impl,
      isPkgInit pkg_id.google_golang_org.protobuf.internal.impl),
   (pkg_id.google_golang_org.protobuf.internal.pragma,
      isPkgInit pkg_id.google_golang_org.protobuf.internal.pragma),
   (pkg_id.fmt, isPkgInit pkg_id.fmt),
   (pkg_id.go_etcd_io.raft.v3, isPkgInit pkg_id.go_etcd_io.raft.v3),
   (pkg_id.go_etcd_io.raft.v3.tracker, isPkgInit pkg_id.go_etcd_io.raft.v3.tracker),
   (pkg_id.go_etcd_io.raft.v3.quorum, isPkgInit pkg_id.go_etcd_io.raft.v3.quorum),
   (pkg_id.strconv, isPkgInit pkg_id.strconv),
   (pkg_id.strings, isPkgInit pkg_id.strings),
   (pkg_id.go_etcd_io.raft.v3.confchange, isPkgInit pkg_id.go_etcd_io.raft.v3.confchange),
   (pkg_id.math.big, isPkgInit pkg_id.math.big),
   (pkg_id.crypto.rand, isPkgInit pkg_id.crypto.rand),
   (pkg_id.bytes, isPkgInit pkg_id.bytes),
   (pkg_id.context, isPkgInit pkg_id.context),
   (pkg_id.time, isPkgInit pkg_id.time),
   (pkg_id.os, isPkgInit pkg_id.os),
   (pkg_id.log, isPkgInit pkg_id.log)]

/-- `get_is_pkg_init` for the register's program: a package's entry in `pkgInitTable`. -/
def getIsPkgInit (s : GoString) : IProp GF :=
  ((pkgInitTable (GF := GF)).lookup s).getD iprop(True)

theorem getIsPkgInit_wf :
    GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.register
      (getIsPkgInit (GF := GF)) := by
  repeat' (first | exact True.intro | apply And.intro | rfl)

end pkgs

/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- The register's program: the package's initialization, then `Main()`. -/
def registerProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.register.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.register.Main) #()

/-- **The register's cluster driver is safe** (`MainSafe`): every real execution of
`registerProgram` (the register package's initialization, then `Main()`) from a fresh state
-- no package initialized (`IsInit`), one live thread -- of any length: if the main thread
has finished, its result is `#()`; no thread is stuck; no thread has ended in a panic
(client B's check of its `Get` among them). Parametric in the Go semantics: any
`go.Semantics` at the state's local context and any package assumptions (the translated
bodies behind the register's and its imports' names). -/
theorem register_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
    (σ : state) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ) :
    MainSafe registerProgram σ := by
  refine mainSafe_of_wp registerProgram σ Hlctx Hinit fun {hG} HL => ?_
  subst HL
  refine ⟨getIsPkgInit, ?_⟩
  iintro Hown
  unfold registerProgram
  wp_apply (github_com.mit_pdos.etcd_grove.examples.register.wp_initialize' _
    getIsPkgInit_wf) $$ Hown as ⟨_, #Hinit⟩
  wp_apply register.wp_Main $$ Hinit
  ipureintro
  rfl

end adequacy

end EtcdGrove
end Perennial
