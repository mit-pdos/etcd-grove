/-
The tester's invariant (`notes/mvcc-migration/mvccrand.md`, "The invariants"): the store's and the
stream's states with the history's lower bound and the published revision. Lean-first (no Rocq
counterpart).

**The world** (`worldInv`, in the invariant `worldN`, disjoint from mvcc's `mvccN`):

- the store's state `σ` (`mvccState`), and half of a ghost variable `γ.σ` at it: the writer holds
  the other half (`writerIdle`/its transaction's), being the only thread whose updates change `σ`
  (the readers' and the registrar's updates commit `σ` unchanged), so it knows `σ` exactly, and
  `End`'s update at its begin state (`⌜σ = σ₀⌝`) is the ghost variable's agreement;
- the stream's state `S` (`wsState`), open until `runChecks`' `ws.Close()` (half of `γ.cl` at
  `S.closed`, bundled with it; the registrar holds the other half at `false`, so its `Watch` sees an
  open stream, and gives it back to `runChecks` before the close), its watchers the registry
  (`γ.reg`, a ghost map from id to the tester's `*watcher` and its registration, `regOk`; its other
  half in `c.mu`'s lock: the registrar adds an id under `c.mu`, inside `Watch`'s update);
- the published revision `p` (`h.published`'s cell), at most `σ.rev`, with a monotone ghost
  counter `γ.pub` (a reader's floor, `Load`ed before its read, is a lower bound of the revision the
  read sees);
- a lower bound `Hl` of the history's revisions (`γ.h.l`) covering the notified history
  (`histOkM`: every revision the store or the stream shows is in the history, its state matched),
  so a reader's snapshot, taken after, has every revision it can read, each state the store's.

`σ.crev = -1` throughout (the tester never compacts: no `Compact`, no `Restore`), so the read
contract's outcome is `rangeOutcome`'s and the watch guarantee's condition `onceUpTo` is vacuous.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.History
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.MonoNat

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section model
variable [GooseExts]

/-- A change as a tuple (its tag, key, value, lease). -/
def encChange : Change → Bool × GoString × GoString × w64
  | .put k v l => (false, k, v, l)
  | .del k => (true, k, [], W64 0)

theorem encChange_inj : ∀ a b : Change, encChange a = encChange b → a = b
  | .put _ _ _, .put _ _ _, h => by simp only [encChange, Prod.mk.injEq] at h; obtain ⟨-, rfl, rfl, rfl⟩ := h; rfl
  | .del _, .del _, h => by simp only [encChange, Prod.mk.injEq] at h; obtain ⟨-, rfl, -⟩ := h; rfl
  | .put _ _ _, .del _, h => by simp [encChange] at h
  | .del _, .put _ _ _, h => by simp [encChange] at h

instance change_api_countable : Pos.Countable Change :=
  .ofInjective (fun c => Pos.Countable.encode (encChange c))
    (fun a b h => encChange_inj a b (Pos.encode_inj h))

instance mvccState_countable : Pos.Countable MvccState :=
  .ofInjective (fun σ => Pos.Countable.encode (σ.log, σ.crev, σ.pending))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1 h2 h3; rfl)

/-- **A revision `e` of the history `Hs` is the log `L`'s revision `r`**: its state is the store's
at `r`, and past revision `0` it is the tester's model (`pendOf`) of the log's changes of `r` from
the revision before (so its changes are what a watcher of the revision expects). -/
def revOk (L : Log) (Hs : List HRev) (r : Nat) (e : HRev) : Prop :=
  stMatch e.1 (stateAt L r) ∧
  (1 ≤ r → ∃ e', Hs[r - 1]? = some e' ∧
    e = ((pendOf e'.1 (W64 (r : Int)) (L.getD r [])).st, (pendOf e'.1 (W64 (r : Int)) (L.getD r [])).chs))

/-- **The history covers the notified history** (the store's and the stream's): every revision of
`σ.notifiedLog` is in `Hl`, the log's revision. -/
def histOkM (σ : MvccState) (Hl : List HRev) : Prop :=
  σ.notifiedLog.length ≤ Hl.length ∧
  ∀ r < σ.notifiedLog.length, ∃ e, Hl[r]? = some e ∧ revOk σ.notifiedLog Hl r e

/-- **A watcher's registration** (what `register` passed to `Watch`): its range's key and end, whether
the end is `nil`, its start revision. -/
abbrev RegInfo := GoString × GoString × Bool × w64

/-- **The stream's watchers are the registry's** (id to the `*watcher` and its registration): each
watcher of the registry a live watcher of the stream, of its registration's range, from its start
revision, unfiltered; any other watcher of the stream of an empty range (none: `Watch` registers
no empty range, but the update it is given must allow it). -/
def regOk (S : StreamState) (W : GMap w64 (Loc × RegInfo)) : Prop :=
  ∀ id, match W !! id with
    | none => ∀ wi, S.ws !! id = some wi → ∀ k, wi.rg.covers k = false
    | some (_, (kk, e, en, st)) => ∃ wi, S.ws !! id = some wi ∧
        wi.rg = ⟨kk, if en then none else some e, st, id⟩ ∧ wi.fs = [] ∧ wi.lo = sint.nat st ∧
        wi.live = true

end model

/-- The tester's ghost names. -/
structure RandNames where
  kv : MvccName
  ws : WsName
  h : HistNames
  /-- the store's state (the invariant's half, the writer's half) -/
  σ : GName
  /-- the published revision (monotone) -/
  pub : GName
  /-- the published revision's value (the invariant's half, the writer's half) -/
  pv : GName
  /-- the stream's watchers: id to the tester's `*watcher` and its registration (`RegInfo`; the
  invariant's half, `c.mu`'s) -/
  reg : GName
  /-- the responses the receiver has checked (`c.mu`'s half, the receiver's half) -/
  rcv : GName
  /-- whether the stream is closed (the invariant's half, at `S.closed`; the other half the
  registering goroutine's at `false`, then `runChecks`', which closes the stream) -/
  cl : GName

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The tester's invariant's namespace (disjoint from `mvccN` and `histN`). -/
def worldN : Namespace := (nroot .@ "mvccrand") .@ "world"

/-- **The tester's invariant** (see the file header). -/
def worldInv (h : Loc) (γ : RandNames) : IProp GF :=
  iprop(∃ (σ : MvccState) (S : StreamState) (p : w64) (Hl : List HRev) (W : GMap w64 (Loc × RegInfo)),
    mvccState γ.kv σ ∗ ghostVar γ.σ (1 : Qp).half σ ∗
    (wsState γ.ws S ∗ ghostVar γ.cl (1 : Qp).half S.closed) ∗ ghostMapAuth γ.reg (1 : Qp).half W ∗
    sync.atomic.ownInt64 (hPub h) (DFrac.own 1) p ∗ ghostVar γ.pv (1 : Qp).half p ∗
    monoNatAuthOwn γ.pub 1 (sint.nat p) ∗ monoListLbOwn γ.h.l Hl ∗
    ⌜σ.crev = -1 ∧ 1 ≤ sint.Z p ∧ sint.nat p ≤ σ.rev ∧ histOkM σ Hl ∧
      regOk S W⌝)

/-- **The writer between transactions** (exclusive): the store at `σ` (nothing pending), the
history's revisions `Hs` exactly its log's (`revOk`), `σ.rev` published. -/
def writerIdle (γ : RandNames) (σ : MvccState) (Hs : List HRev) : IProp GF :=
  iprop(ghostVar γ.σ (1 : Qp).half σ ∗ histW γ.h Hs ∗
    ghostVar γ.pv (1 : Qp).half (W64 (σ.rev : Int)) ∗
    ⌜σ.pending = none ∧ Hs.length = σ.log.length ∧ σ.log.length + 3 ≤ 2 ^ 63 ∧
      ∀ r < Hs.length, ∃ e, Hs[r]? = some e ∧ revOk σ.log Hs r e⌝)

/-- The last revision's state of `Hs`. -/
def lastSt (Hs : List HRev) : GMap GoString kvRec := (Hs[Hs.length - 1]?.map Prod.fst).getD ∅

end defs

end mvccrand
end EtcdGrove
end Perennial
