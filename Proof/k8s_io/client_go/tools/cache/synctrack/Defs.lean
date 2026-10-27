/-
client-go's `synctrack.SingleFileTracker` (`tools/cache/synctrack/synctrack.go`): a counter of the
initial-list notifications a listener has started but not finished, and whether its upstream
synced. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the shared informer's listeners).

* `isSFT t γ` (persistent): the tracker `t`; its counter `count` and its upstream flag
  `upstreamHasSynced` live in an invariant (`sftInv`), the counter `n` being exactly the number of
  outstanding start tokens `sftTok γ` (`ownTokAuth γ n`), with `n` time receipts (`⧗ n`) so that
  `Start` cannot wrap it (`receiptBound GF ≤ 2^63`, the Perennial bound on an execution's Go
  steps); its `cancel` function (read only) returns.
* `Start` hands out a token, `Finished` takes one back: so `Finished` never sees a negative counter
  (its panic is unreachable).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.cacher.Base
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.TokSet
public import Proof.ReceiptTactics

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace synctrack

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache.synctrack

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.synctrack.Assumptions]

/-- The tracker's invariant's namespace. -/
def sftN : Namespace := nroot.@"synctrack.SingleFileTracker"

/-- **The tracker's invariant**: the counter is the number `n` of outstanding start tokens (with
`n` time receipts), the upstream flag some boolean. -/
def sftInv (t : Loc) (γ : GName) : IProp GF :=
  iprop(∃ (n : Nat) (b : Bool),
    ⌜n < 2 ^ 63⌝ ∗
    structFieldRef SingleFileTracker go!"count" t ↦ (W64 (n : Int)) ∗ ownTokAuth γ n ∗ ⧗ n ∗
    sync.atomic.ownBool (structFieldRef SingleFileTracker go!"upstreamHasSynced" t) (DFrac.own 1) b)

/-- **The tracker** (persistent): its invariant, and its `cancel` function, which returns. -/
def isSFT (t : Loc) (γ : GName) : IProp GF :=
  iprop(∃ f : GoFunc, structFieldRef SingleFileTracker go!"cancel" t ↦□ f ∗
    □ (∀ Φ : val → IProp GF, ▷ Φ #() -∗ WP (App (Val #f) (Val #())) {{ Φ }}) ∗
    inv sftN (sftInv t γ))

instance isSFT_persistent (t : Loc) (γ : GName) : Persistent (isSFT (GF := GF) t γ) := by
  unfold isSFT; infer_instance

/-- **A start token**: one initial-list notification started and not yet finished. -/
def sftTok (γ : GName) : IProp GF := ownToks γ 1

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

/-- (Time receipts) `wp_AddInt64` for the call `atomic.AddInt64(addr, v)` before the function is
resolved, as Goose emits it (as Perennial's `wp_AddUint64_receipt`): resolving `AddInt64` is a Go
instruction, whose receipt `⧗ 1` the atomic update receives. -/
theorem wp_AddInt64_receipt (addr : Loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (⧗ 1 -∗ |={⊤,∅}=> ▷ ∃ oldv : w64, addr ↦ oldv ∗
        (addr ↦ (oldv + v) ={∅,⊤}=∗ Φ #(oldv + v))) -∗
      WP (App (App (App (Val (GoInstruction (FuncResolve sync.atomic.AddInt64 []))) (Val #()))
        (Val #addr)) (Val #v)) {{ Φ }} := by
  iintro %Φ #Hpkg HΦ
  wp_bind (App (Val (GoInstruction _)) (Val _))
  iapply wp_go_step_receipt'
  case hv => exact isPanic_intoVal ()
  inext
  iintro Hr _
  iapply wp_value'
  iapply sync.atomic.wp_AddInt64 addr v $$ %Φ Hpkg
  iapply HΦ $$ Hr

end lemmas

end synctrack
end EtcdGrove
end Perennial
