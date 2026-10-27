/-
What `watch.go` reads of package variables, the part `v3rpc`'s initializer gives (D19j,
2026-10-18: moved here from `InvWatch.lean`, so that `v3rpc`'s package facts (`Base.lean`,
`watchPkgVars`) can state them): the shapes of the error and histogram variables
(`msgErrVar`, `histVar`), the progress interval's lock and what it guards (`intervalMu`,
`intervalP`), and the lemmas that turn other packages' facts into these shapes (`auth`'s
`authErrVar`, the cache's `errorStringSpec`).
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.etcd.server.v3.auth.Base
public import Perennial.Golang.Theory.Map
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.GhostMap
public import Perennial.IrisLib.BI
public import Perennial.Proof.sync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The progress interval's lock (the package variable `progressReportIntervalMu`). -/
abbrev v3rpc.intervalMu : Loc :=
  globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.progressReportIntervalMu

end addrs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The package variable `g` holds a fixed error whose `Error()` returns (persistent). -/
def v3rpc.msgErrVar (g : GoString) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗ errMsgOk e)

instance v3rpc.msgErrVar_persistent (g : GoString) : Persistent (v3rpc.msgErrVar (GF := GF) g) := by
  unfold v3rpc.msgErrVar errMsgOk; infer_instance

/-- The package variable `g` holds a fixed histogram whose `Observe` returns (persistent). -/
def v3rpc.histVar (g : GoString) : IProp GF :=
  iprop(∃ h : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok h ∗
    □ (∀ x : w64, {{ True }} (App (Val #(methods h.ty go!"Observe" h.v)) (Val #x))
      {{ RET #(); True }}))

instance v3rpc.histVar_persistent (g : GoString) : Persistent (v3rpc.histVar (GF := GF) g) := by
  unfold v3rpc.histVar; infer_instance

/-- **The progress interval** at the fraction `q` (what `progressReportIntervalMu` guards): a
duration of at least `10` nanoseconds (`GetProgressReportInterval`'s jitter `rand.Int63n(d / 10)`
needs `d / 10 > 0`) and at most `2 ^ 62` (`d + d / 10` must not wrap:
`issues/etcd-watch-progress-interval-overflow.md`). -/
def v3rpc.intervalP (q : Qp) : IProp GF :=
  iprop(∃ d : w64, typedPointsto (globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.progressReportInterval)
      d (DFrac.own q) ∗ ⌜10 ≤ sint.Z d ∧ sint.Z d ≤ 2 ^ 62⌝)

instance v3rpc.intervalP_fractional : Fractional (v3rpc.intervalP (GF := GF)) where
  fractional q1 q2 := by
    unfold v3rpc.intervalP
    constructor
    · iintro ⟨%d, Hd, %Hb⟩
      icases (typedPointsto_frac_add _ _ q1 q2).1 $$ Hd with ⟨H1, H2⟩
      isplitl [H1]
      · iexists d; iframe; ipureintro; exact Hb
      · iexists d; iframe; ipureintro; exact Hb
    · iintro ⟨⟨%d1, H1, %Hb⟩, ⟨%d2, H2, -⟩⟩
      icombine H1 H2 gives %Hd
      subst Hd
      iexists d1
      isplitl [H1 H2]
      · iapply (typedPointsto_frac_add _ _ q1 q2).2; iframe
      · ipureintro; exact Hb

/-! ### The progress interval's reader slots, pooled (2026-10-20, watchkv)

`v3rpc`'s initializer makes `progressReportIntervalMu`'s reader slots (`sync.init_RWMutex`), and a
package fact cannot hold them (it is persistent) nor can an initializer return them (a package
is initialized once, by whichever importer runs first). So they go in an invariant, the pool,
which the package fact names (`intervalPool`, in `watchPkgVars`). A thread borrows a slot by
depositing its thread token (`threadTok`) and gets it back by returning the slot: at most
`threadBound GF` tokens can be deposited, so while `threadBound GF` is at most the slots' number
(`actualMaxReaders`, `2 ^ 30 - 1`) the pool is never empty for a borrower. -/

/-- The pool's namespace. -/
def v3rpc.intervalN : Namespace := nroot .@ "v3rpc_interval_pool"

/-- The pool's content: `k` reader slots of the interval's lock, the `d` thread tokens of the
threads that borrowed one, and their loans' authority (`γl`), `k + d` the slots' number. -/
def v3rpc.intervalPoolInv (γl : GName) : IProp GF :=
  iprop(∃ k d : Nat,
    ([∗list] _x ∈ List.replicate k (), sync.ownRWMutex v3rpc.intervalMu v3rpc.intervalP) ∗
    threadToks d ∗ ownTokAuth γl d ∗ ⌜k + d = Int.toNat sync.rwmutex.actualMaxReaders⌝)

/-- **The interval's lock, with its pooled reader slots** (persistent; the package fact's part):
the lock's guard (a writer's, `SetProgressReportInterval`) and the pool. -/
def v3rpc.intervalPool : IProp GF :=
  iprop(sync.isRWMutexGuard v3rpc.intervalMu v3rpc.intervalP ∗
    ∃ γl : GName, inv v3rpc.intervalN (v3rpc.intervalPoolInv γl))

instance v3rpc.intervalPool_persistent : Persistent (v3rpc.intervalPool (GF := GF)) := by
  unfold v3rpc.intervalPool; infer_instance

/-- A loan of a reader slot of the pool `γl` (what returning it takes). -/
def v3rpc.intervalLoan : IProp GF :=
  iprop(∃ γl : GName, inv v3rpc.intervalN (v3rpc.intervalPoolInv γl) ∗ ownToks γl 1)

/-- **The pool's allocation** (`v3rpc`'s initializer): every reader slot of the lock. -/
theorem v3rpc.intervalPool_alloc (E : CoPset) :
    sync.isRWMutexGuard (GF := GF) v3rpc.intervalMu v3rpc.intervalP ∗
      ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        sync.ownRWMutex v3rpc.intervalMu v3rpc.intervalP) ⊢ |={E}=> v3rpc.intervalPool := by
  iintro ⟨#Hg, Hs⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γl, Ha⟩
  ihave Ht : threadToks (GF := GF) 0 $$ []
  · unfold threadToks
    iexists []
    isplitr
    · ipureintro; rfl
    unfold threadTokList; itrivial
  imod (inv_alloc v3rpc.intervalN E (v3rpc.intervalPoolInv γl)) $$ [Hs Ht Ha] with #Hi
  · inext
    unfold v3rpc.intervalPoolInv
    iexists Int.toNat sync.rwmutex.actualMaxReaders, 0
    iframe
    ipureintro; rfl
  imodintro
  unfold v3rpc.intervalPool
  iframe Hg
  iexists γl
  iexact Hi

/-- An `auth` error variable (`authErrVar`) in the apply package's shape (`errVarLeaf`). -/
theorem v3rpc.errVarLeaf_of_authErrVar (g : GoString) :
    go_etcd_io.etcd.server.v3.auth.authErrVar (GF := GF) g ⊢ errVarLeaf g := by
  unfold go_etcd_io.etcd.server.v3.auth.authErrVar errVarLeaf errLeaf errMsgOk
  iintro ⟨%e, #He, %Hl, #Hm⟩
  iexists e
  iframe He Hm
  ipureintro; exact Hl

/-- An error whose `Error()` returns (the cache's `errorStringSpec`), as a triple (`errMsgOk`). -/
theorem v3rpc.errMsgOk_of_errorStringSpec (e : GoInterfaceOk) :
    go_etcd_io.etcd.cache.v3.errorStringSpec (GF := GF) e ⊢ errMsgOk e := by
  unfold go_etcd_io.etcd.cache.v3.errorStringSpec errMsgOk
  iintro #H
  iintro !> %Φ - HΦ
  iapply H
  inext
  iintro %s
  iapply HΦ
  itrivial

/-- An error variable whose `Error()` returns (the cache's `errorStringSpec`), as `msgErrVar`. -/
theorem v3rpc.msgErrVar_of_spec (g : GoString) :
    (∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗
        go_etcd_io.etcd.cache.v3.errorStringSpec (GF := GF) e) ⊢ v3rpc.msgErrVar g := by
  iintro ⟨%e, #He, #Hs⟩
  unfold v3rpc.msgErrVar
  iexists e
  iframe He
  iapply v3rpc.errMsgOk_of_errorStringSpec
  iexact Hs

end defs

section pool
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Borrowing a reader slot**: the thread's token for a slot and a loan, while
`threadBound GF` is at most the slots' number. -/
theorem v3rpc.intervalPool_borrow (E : CoPset) (hE : ↑v3rpc.intervalN ⊆ E)
    (hb : threadBound GF ≤ Int.toNat sync.rwmutex.actualMaxReaders) :
    v3rpc.intervalPool (GF := GF) ∗ £ 1 ∗ threadTok ⊢
      |={E}=> sync.ownRWMutex v3rpc.intervalMu v3rpc.intervalP ∗ v3rpc.intervalLoan := by
  unfold v3rpc.intervalPool
  iintro ⟨⟨-, %γl, #Hi⟩, Hlc, Htok⟩
  iinv Hi with Hp Hclose
  imod (lc_fupd_elim_later (E := E \ ↑v3rpc.intervalN)) $$ Hlc Hp with Hp
  iunfold v3rpc.intervalPoolInv at Hp
  icases Hp with ⟨%k, %d, Hs, Ht, Ha, %Hkd⟩
  ihave ⟨%Hlt, Ht⟩ := threadToks_add_one_lt d $$ [Htok Ht]
  · iframe
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [List.replicate_succ]
  icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨Hslot, Hs⟩
  imod ownTokAuth_S γl d $$ Ha with ⟨Ha, Hloan⟩
  imod Hclose $$ [Hs Ht Ha] with -
  · inext
    iunfold v3rpc.intervalPoolInv
    iexists k', d + 1
    iframe
    ipureintro; omega
  imodintro
  iframe Hslot
  unfold v3rpc.intervalLoan
  iexists γl
  iframe Hi Hloan

/-- **Returning a reader slot**: the slot and its loan for the thread's token. -/
theorem v3rpc.intervalPool_return (E : CoPset) (hE : ↑v3rpc.intervalN ⊆ E) :
    v3rpc.intervalLoan (GF := GF) ∗ £ 1 ∗ sync.ownRWMutex v3rpc.intervalMu v3rpc.intervalP ⊢
      |={E}=> threadTok := by
  unfold v3rpc.intervalLoan
  iintro ⟨⟨%γl, #Hi, Hloan⟩, Hlc, Hslot⟩
  iinv Hi with Hp Hclose
  imod (lc_fupd_elim_later (E := E \ ↑v3rpc.intervalN)) $$ Hlc Hp with Hp
  iunfold v3rpc.intervalPoolInv at Hp
  icases Hp with ⟨%k, %d, Hs, Ht, Ha, %Hkd⟩
  icombine Ha Hloan gives %Hle
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  imod ownTokAuth_delete_S γl d' $$ Ha Hloan with Ha
  icases (threadToks_add d' 1).1 $$ Ht with ⟨Ht, Htok⟩
  imod Hclose $$ [Hs Ht Ha Hslot] with -
  · inext
    iunfold v3rpc.intervalPoolInv
    iexists k + 1, d'
    iframe
    isplitl [Hs Hslot]
    · rw [List.replicate_succ]
      iapply BigSepL.bigSepL_cons.2
      iframe
    ipureintro; omega
  imodintro
  iexact Htok

end pool

end EtcdGrove
end Perennial
