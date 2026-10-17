/-
etcd's auto-periodic compactor (`server/etcdserver/api/v3compactor/autoperiodic.go`, added by
etcd#22095): the shared vocabulary of
`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3compactor/*.lean`. Lean-first (no Rocq
counterpart).

An `AutoPeriodic` `ac` holds, read-only once `newAutoPeriodic` has built it, its logger, clock,
retention (a revision count), the quota `maxBytes`, the revision getter `rg`, the compactable
`c` (the server's `Compact`), the size getter `sg` (the backend's `Size`), and a cancellable
context `ctx` with its `cancel`; and, under the mutex `ac.mu`, the flag `paused`.
`isAutoPeriodic ac P` (persistent) is all of that: the fields at `↦□` with values `P`, the
context (`isContext`, with the cancel function's spec), and the mutex with its lock invariant
`apLockInv ac` (the flag, owned).

The callees behind the interfaces are contracts (the trust boundary of the compactor, stated
here and premises of `Run`'s spec, not axioms):

* `apClockOk clk`: `clk.Now()` returns some time; `clk.After(d)` some channel from which a
  receive yields a time (a bag of times, as the cache's timers: `isChanBag`).
* `apSizeOk sg`: `sg.Size()` returns some `int64` (the backend's file size; the spec does not
  model sizes).
* `apRevOk rg R`: `rg.Rev()` returns some non-negative `v` with `R v`, a persistent fact the
  caller chooses (the server: "the store's current revision is at least `v`").
* `apCompactOk c R T retention`: `c.Compact(ctx, req)` with `req` a non-physical
  `CompactionRequest` at revision `r`, called with `r > 0`, `r = v - retention` for some `v`
  with `R v` (so it keeps the last `retention` revisions of a store at revision at least `v`),
  and `r` above `p`, the last revision `T` records, returns some response and error (an error
  `errors.Is` can classify, `apErrIs`), and then either `T p` again or, after an update,
  `T r` (`T p ∧ |==> T r`: the caller of `Compact` chooses, and `Run` takes `T r` exactly when
  the compaction succeeded or was already done, `mvcc.ErrCompacted`). `T` is the caller's
  record of the last compaction; `Run` owns it from the start (`T 0`).

The package-level tuning variables (`AutoPeriodicHighWater`, ...) are read-only here
(`apTuning`): production code never writes them (only the PR's tests do, between runs), and
their values are opaque floats or durations the spec does not interpret.

Floats are opaque in Perennial (`FloatOps`: uninterpreted bit patterns), and Perennial gives no
semantics to the conversion of a `float64` to an integer type, which `Run` does twice
(`int64(AutoPeriodicHighWater * float64(ac.maxBytes))`, `time.Duration(.../rate)`): without it
the code is stuck. `Float64ToInt64Semantics` is that missing step, an opaque function of the
float (Go's conversion truncates; out of range it is implementation-defined but does not
panic): a model assumption of this repository, carried as an instance argument of the specs
that need it (`notes/STATUS.md`, "Float-to-integer conversion"), not a change to Perennial.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base
public import Perennial.Proof.context
public import Proof.github_com.jonboulle.clockwork.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api

/-! ## The float-to-integer conversion (a model assumption) -/

/-- The conversion `int64(f)` of a `float64`: an opaque function of the float's bits. -/
class Float64ToInt64 where
  float64ToInt64 : w64 → w64

/-- Go's `int64(f)` (and a conversion to a named type over `int64`, `time.Duration(f)`, through
the underlying types): it steps to `float64ToInt64 f`. Perennial gives no semantics to it. -/
class Float64ToInt64Semantics [FfiSyntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions] [Float64ToInt64] : Prop where
  convert_float64_to_int64 (v : w64) :
    ⟦Convert go.float64 go.int64, #v⟧ ⤳[under] #(Float64ToInt64.float64ToInt64 v)

attribute [instance] Float64ToInt64Semantics.convert_float64_to_int64

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

abbrev apLgAddr (ac : Loc) : Loc := structFieldRef v3compactor.AutoPeriodic go!"lg" ac
abbrev apClockAddr (ac : Loc) : Loc := structFieldRef v3compactor.AutoPeriodic go!"clock" ac
abbrev apRetentionAddr (ac : Loc) : Loc := structFieldRef v3compactor.AutoPeriodic go!"retention" ac
abbrev apMaxBytesAddr (ac : Loc) : Loc := structFieldRef v3compactor.AutoPeriodic go!"maxBytes" ac
abbrev apRgAddr (ac : Loc) : Loc := structFieldRef v3compactor.AutoPeriodic go!"rg" ac
abbrev apCAddr (ac : Loc) : Loc := structFieldRef v3compactor.AutoPeriodic go!"c" ac
abbrev apSgAddr (ac : Loc) : Loc := structFieldRef v3compactor.AutoPeriodic go!"sg" ac
abbrev apCtxAddr (ac : Loc) : Loc := structFieldRef v3compactor.AutoPeriodic go!"ctx" ac
abbrev apCancelAddr (ac : Loc) : Loc := structFieldRef v3compactor.AutoPeriodic go!"cancel" ac
abbrev apMuAddr (ac : Loc) : Loc := structFieldRef v3compactor.AutoPeriodic go!"mu" ac
abbrev apPausedAddr (ac : Loc) : Loc := structFieldRef v3compactor.AutoPeriodic go!"paused" ac

end addrs

/-- The read-only fields of an `AutoPeriodic` (what `newAutoPeriodic` stores). -/
structure APParams [FfiSyntax] where
  lg : Loc
  clock : GoInterface
  retention : w64
  maxBytes : w64
  rg : GoInterface
  c : GoInterface
  sg : GoInterface

/-- The values of the tuning variables: `AutoPeriodicHighWater` (a float), `...SampleInterval`,
`...LeadTime`, `...Cooldown` (durations), `autoPeriodicRateAlpha` (a float). -/
structure APTuning where
  hw : w64
  si : w64
  lt : w64
  cd : w64
  α : w64

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The lock invariant of `ac.mu`: the flag `ac.paused`, owned. -/
def apLockInv (ac : Loc) : IProp GF :=
  iprop(∃ b : Bool, apPausedAddr ac ↦ b)

/-- `ac` is an auto-periodic compactor with fields `P` (persistent): the read-only fields, its
context (cancellable, never done but by `cancel`) and the mutex over `paused`. -/
def isAutoPeriodic (ac : Loc) (P : APParams) : IProp GF :=
  iprop(apLgAddr ac ↦□ P.lg ∗ apClockAddr ac ↦□ P.clock ∗ apRetentionAddr ac ↦□ P.retention ∗
    apMaxBytesAddr ac ↦□ P.maxBytes ∗ apRgAddr ac ↦□ P.rg ∗ apCAddr ac ↦□ P.c ∗
    apSgAddr ac ↦□ P.sg ∗
    (∃ (ctx : GoInterfaceOk) (γ : context.ContextNames) (cancel : GoFunc),
      apCtxAddr ac ↦□ GoInterface.ok ctx ∗ apCancelAddr ac ↦□ cancel ∗
      context.isContext ctx { Values := ∅, Deadline := none, Done_gn := γ, PDone := iprop(True) } ∗
      context.cancelSpec cancel γ iprop(True)) ∗
    sync.isMutex (apMuAddr ac) (apLockInv ac))

instance isAutoPeriodic_persistent (ac : Loc) (P : APParams) :
    Persistent (isAutoPeriodic (GF := GF) ac P) := by
  unfold isAutoPeriodic; infer_instance

/-- The tuning variables, read-only, at the values `tv` (opaque floats and durations). -/
def apTuning (tv : APTuning) : IProp GF :=
  iprop(globalAddr v3compactor.AutoPeriodicHighWater ↦□ tv.hw ∗
    globalAddr v3compactor.AutoPeriodicSampleInterval ↦□ tv.si ∗
    globalAddr v3compactor.AutoPeriodicLeadTime ↦□ tv.lt ∗
    globalAddr v3compactor.AutoPeriodicCooldown ↦□ tv.cd ∗
    globalAddr v3compactor.autoPeriodicRateAlpha ↦□ tv.α)

instance apTuning_persistent (tv : APTuning) : Persistent (apTuning (GF := GF) tv) := by
  unfold apTuning; infer_instance

/-- The clock: `clockwork.isClock` (`Now()` returns some time, `After(d)` some channel of
times). -/
abbrev apClockOk (clk : GoInterface) : IProp GF := clockwork.isClock clk

/-- The size getter: `Size()` returns some `int64`. -/
def apSizeOk (sg : GoInterface) : IProp GF :=
  iprop(∃ si : GoInterfaceOk, ⌜sg = GoInterface.ok si⌝ ∗
    {{ True }} (App (Val #(methods si.ty go!"Size" si.v)) (Val #()))
      {{ (n : w64), RET #n; True }})

instance apSizeOk_persistent (sg : GoInterface) : Persistent (apSizeOk (GF := GF) sg) := by
  unfold apSizeOk; infer_instance

/-- The revision getter: `Rev()` returns some non-negative `v` with `R v`. -/
def apRevOk (rg : GoInterface) (R : w64 → IProp GF) : IProp GF :=
  iprop(∃ ri : GoInterfaceOk, ⌜rg = GoInterface.ok ri⌝ ∗
    {{ True }} (App (Val #(methods ri.ty go!"Rev" ri.v)) (Val #()))
      {{ (v : w64), RET #v; ⌜0 ≤ sint.Z v⌝ ∗ □ R v }})

instance apRevOk_persistent (rg : GoInterface) (R : w64 → IProp GF) :
    Persistent (apRevOk (GF := GF) rg R) := by
  unfold apRevOk; infer_instance

/-- An error `errors.Is` can classify against any target (the first half of the apply
package's `applyErrIs`). -/
def apErrIs (err : GoInterface) : IProp GF :=
  iprop(□ ∀ target : GoInterface, ∃ (S : GoInterface → Prop) (M : GoInterfaceOk → Prop),
    _root_.Perennial.errors.errorIsTree (GF := GF) S M target ∗
    ⌜S err ∧ (ptrTarget target → _root_.Perennial.errors.TreeTyped S target)⌝)

instance apErrIs_persistent (err : GoInterface) : Persistent (apErrIs (GF := GF) err) := by
  unfold apErrIs; infer_instance

/-- The compactable: `Compact(ctx, req)` at revision `r` (see the file's header). -/
def apCompactOk (c : GoInterface) (R : w64 → IProp GF) (T : w64 → IProp GF) (retention : w64) :
    IProp GF :=
  iprop(∃ ci : GoInterfaceOk, ⌜c = GoInterface.ok ci⌝ ∗
    □ ∀ (ctx : GoInterface) (req : Loc) (m : _root_.Perennial.go_etcd_io.etcd.api.v3.etcdserverpb.CompactionRequest) (p r v : w64),
      {{ req ↦ m ∗ ⌜m.Revision' = r ∧ m.Physical' = false⌝ ∗ T p ∗ □ R v ∗
          ⌜0 < sint.Z r ∧ sint.Z p < sint.Z r ∧ sint.Z r + sint.Z retention = sint.Z v⌝ }}
        (App (App (Val #(methods ci.ty go!"Compact" ci.v)) (Val #ctx)) (Val #req))
      {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
          apErrIs err ∗ (T p ∧ |==> T r) }})

instance apCompactOk_persistent (c : GoInterface) (R T : w64 → IProp GF) (retention : w64) :
    Persistent (apCompactOk (GF := GF) c R T retention) := by
  unfold apCompactOk; infer_instance

/-- `mvcc.ErrCompacted`, read-only: a pointer error (`errors.New`), a leaf. -/
def apErrCompacted : IProp GF :=
  iprop(∃ e : GoInterfaceOk,
    globalAddr go_etcd_io.etcd.server.v3.storage.mvcc.ErrCompacted ↦□ GoInterface.ok e ∗
    ⌜errLeaf e⌝)

instance apErrCompacted_persistent : Persistent (apErrCompacted (GF := GF)) := by
  unfold apErrCompacted; infer_instance

end defs

end EtcdGrove
end Perennial
