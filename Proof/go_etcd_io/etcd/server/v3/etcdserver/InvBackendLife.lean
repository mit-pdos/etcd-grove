/-
**The server's backend from open to closed** (`server.go`: `s.be` under `s.bemu`; `StorageVersion`
reads it, `Cleanup` closes it; etcd PR #22190, `notes/pr-verify/etcd-22190.md`). Lean-first.

**The backend's open token.** A backend (the interface value `s.be`) comes with a fractional open
token `O` (`beLifeOk b O`): its `ReadTx()` returns a read transaction whose `RLock`, reads and
`RUnlock` need a fraction of `O` (`schemaReadTx`), and its `Close()` takes all of it. (The verified
backend's own open token is `bOpen γ` of `storage/backend/InvBackend.lean`, which its `Close`
takes whole and its readers' `RLock` a fraction of; relating the two is the construction premise's,
not done here.)

**`bemu`'s resource** (`bemuP s L q`): half of `s.be` (scaled; the other half is the apply
thread's, its only writer, which `Cleanup` reads unlocked), the backend's contract, and either a
fraction of its open token or the backend **shut**: closed for good (`L.γc`'s flag discarded at
`true`), and `s.stopping` closed (its done view, persistent). So a reader under the read lock that
sees `stopping` open holds a fraction of the open token: the shut case's done view makes its
non-blocking receive ready. `Cleanup`, with the closer's flag (`beCloser L`, at `false`: the
backend not shut), write-locks, takes the whole open token (the shut case is excluded by the
flag), closes the backend, and puts the shut case back with `stopping`'s done view, which its
caller (`run`'s shutdown, after `close(s.stopping)`) holds.

`L` (`BeLife`: the open token and the closer's flag's name) is existential in each holder's slot
(`srvBemuReader s`, `srvCleanupRes s`): one mutex has one lock invariant (`sync.init_RWMutex`
allocates `isRWMutex`'s state once), so the construction premise that hands out the slots gives
them the same `L`; no proof here relies on it.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

abbrev srvBemuAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"bemu" s
abbrev srvBeAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"be" s

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A read transaction of a backend whose open token is `O`** (persistent): `RLock` with a
fraction `O q` gives a held state `H q`, its `UnsafeRange` reads keep it, `RUnlock` gives `O q`
back. (What `schema.DetectSchemaVersion` does with its transaction; `UnsafeRange`'s results are
not described: the trust-boundary contract of `DetectSchemaVersion` reads them.) -/
def schemaReadTx (rt : GoInterfaceOk) (O : Qp → IProp GF) : IProp GF :=
  iprop(∃ H : Qp → IProp GF,
    □ (∀ q : Qp, {{ O q }} (App (Val #(methods rt.ty go!"RLock" rt.v)) (Val #()))
        {{ RET #(); H q }}) ∗
    □ (∀ (q : Qp) (bk : GoInterface) (key endKey : GoSlice) (limit : w64),
        {{ H q }} (App (App (App (App (Val #(methods rt.ty go!"UnsafeRange" rt.v)) (Val #bk))
          (Val #key)) (Val #endKey)) (Val #limit))
        {{ (keys vals : GoSlice), RET (PairV #keys #vals); H q }}) ∗
    □ (∀ q : Qp, {{ H q }} (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #()))
        {{ RET #(); O q }}))

instance schemaReadTx_persistent (rt : GoInterfaceOk) (O : Qp → IProp GF) :
    Persistent (schemaReadTx rt O) := by
  unfold schemaReadTx; infer_instance

/-- **The server's backend `b` with open token `O`** (persistent): `O` fractional, `ReadTx()`
returns a `schemaReadTx` of `O`, `Close()` takes all of `O`. -/
def beLifeOk (b : GoInterface) (O : Qp → IProp GF) : IProp GF :=
  iprop(□ (∀ q1 q2, O (q1 + q2) ∗-∗ O q1 ∗ O q2) ∗
    ∃ bi : GoInterfaceOk, ⌜b = GoInterface.ok bi⌝ ∗
    □ ({{ True }} (App (Val #(methods bi.ty go!"ReadTx" bi.v)) (Val #()))
       {{ (rt : GoInterfaceOk), RET #(GoInterface.ok rt); schemaReadTx rt O }}) ∗
    □ ({{ O 1 }} (App (Val #(methods bi.ty go!"Close" bi.v)) (Val #()))
       {{ (err : GoInterface), RET #err; True }}))

instance beLifeOk_persistent (b : GoInterface) (O : Qp → IProp GF) :
    Persistent (beLifeOk b O) := by
  unfold beLifeOk; infer_instance

/-- The backend's life: its open token and the closer's flag's name. -/
structure BeLife (GF : BundledGFunctors) where
  O : Qp → IProp GF
  γc : GName

/-- **The closer's flag** (`Cleanup`'s): the backend not shut yet. -/
def beCloser (L : BeLife GF) : IProp GF := dghostVar L.γc (DFrac.own 1) false

/-- **The backend shut** (persistent): closed for good, and `s.stopping` closed. -/
def beShut (s : Loc) (L : BeLife GF) : IProp GF :=
  iprop(dghostVar L.γc DFrac.discard true ∗
    ∃ (ch : Loc) (γ : ChanNames), srvStoppingAddr s ↦□ ch ∗ ownStopChan ch γ iprop(True) .Done)

instance beShut_persistent (s : Loc) (L : BeLife GF) : Persistent (beShut s L) := by
  unfold beShut; infer_instance

/-- **`s.bemu`'s lock invariant at fraction `q`** (see the file header): half of `s.be` (scaled),
its contract, and a fraction of its open token unless shut. -/
def bemuP (s : Loc) (L : BeLife GF) (q : Qp) : IProp GF :=
  iprop(∃ b : GoInterface, srvBeAddr s ↦{DFrac.own q.half} b ∗ beLifeOk b L.O ∗
    (L.O q ∨ beShut s L))

/-- **A reader slot of `s.bemu`**. -/
def srvBemuReader (s : Loc) : IProp GF :=
  iprop(∃ L : BeLife GF, sync.ownRWMutex (srvBemuAddr s) (bemuP s L))

/-- A unit method's contract: returns (or the interface is nil). -/
def stopOk (v : GoInterface) (m : GoString) : IProp GF :=
  iprop(⌜v = GoInterface.nil⌝ ∨ ∃ vi : GoInterfaceOk, ⌜v = GoInterface.ok vi⌝ ∗
    □ ({{ True }} (App (Val #(methods vi.ty m vi.v)) (Val #())) {{ RET #(); True }}))

/-- An error-returning method's contract: returns (or the interface is nil). -/
def closeOk (v : GoInterface) (m : GoString) : IProp GF :=
  iprop(⌜v = GoInterface.nil⌝ ∨ ∃ vi : GoInterfaceOk, ⌜v = GoInterface.ok vi⌝ ∗
    □ ({{ True }} (App (Val #(methods vi.ty m vi.v)) (Val #())) {{ (err : GoInterface), RET #err; True }}))

instance stopOk_persistent (v : GoInterface) (m : GoString) : Persistent (stopOk (GF := GF) v m) := by
  unfold stopOk; infer_instance

instance closeOk_persistent (v : GoInterface) (m : GoString) :
    Persistent (closeOk (GF := GF) v m) := by
  unfold closeOk; infer_instance

/-- **What `Cleanup` needs but `stopping`'s done view** (not persistent; `run`'s shutdown's): a
reader slot of `bemu` (for its write lock), the closer's flag, the apply thread's half of `s.be`,
and the names-only fields' contracts (`lessor.Stop`, `kv.Close`, `authStore.Close`,
`compactor.Stop`: they return). -/
def srvCleanupRes (s : Loc) : IProp GF :=
  iprop(∃ (L : BeLife GF) (b : GoInterface),
    sync.ownRWMutex (srvBemuAddr s) (bemuP s L) ∗ beCloser L ∗
    srvBeAddr s ↦{DFrac.own (1 : Qp).half} b ∗
    (∃ l : GoInterface, structFieldRef EtcdServer go!"lessor" s ↦□ l ∗ stopOk l go!"Stop") ∗
    (∃ k : GoInterface, structFieldRef EtcdServer go!"kv" s ↦□ k ∗ closeOk k go!"Close") ∗
    (∃ a : GoInterface, structFieldRef EtcdServer go!"authStore" s ↦□ a ∗ closeOk a go!"Close") ∗
    (∃ c : GoInterface, structFieldRef EtcdServer go!"compactor" s ↦□ c ∗ stopOk c go!"Stop"))

/-- The closer's flag excludes the shut backend. -/
theorem beCloser_not_shut (s : Loc) (L : BeLife GF) :
    ⊢ beCloser L -∗ beShut s L -∗ False := by
  iintro Hc Hs
  iunfold beShut at Hs
  icases Hs with ⟨Hd, -⟩
  iunfold beCloser at Hc
  icombine Hc Hd gives %h
  cases h.2

/-- **Shutting the backend**: the closer's flag, set and discarded, with `stopping`'s done view. -/
theorem beCloser_shut (s : Loc) (L : BeLife GF) (ch : Loc) (γ : ChanNames) :
    ⊢ beCloser L -∗ srvStoppingAddr s ↦□ ch -∗ ownStopChan ch γ iprop(True) .Done ==∗
      beShut s L := by
  iintro Hc #Hch #Hd
  iunfold beCloser at Hc
  imod dghostVar_update true L.γc false $$ Hc with Hc
  imod dghostVar_persist L.γc 1 true $$ Hc with #Hc
  imodintro
  iunfold beShut
  iframe Hc
  iexists ch, γ
  iframe Hch Hd

end defs

end EtcdGrove
end Perennial
