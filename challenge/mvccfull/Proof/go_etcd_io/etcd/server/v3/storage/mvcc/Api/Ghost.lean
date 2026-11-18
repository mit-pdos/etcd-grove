/-
**The API proof's store ghost state** (stage 1, 2026-11-03; `notes/mvcc-api-invariants.md` §1 and
§2, round 16). Lean-first (no Rocq counterpart). Imported by `InvStore` (2026-11-03, in-place slots: `StoreNames.api`, the slot
functions `slotX`/`slotY`/...; `notes/decisions.md`, "slots in place"), so it imports only the model.

* `γ.abs`: the client's view of the committed history and the compaction revision (`σ.log`,
  `σ.crev`), a ghost variable: ½ the client (`mvccState`), ¼ `s.revMu`'s resource, ¼ the writer's
  state.
* `γ.pnd`: the pending revision (`σ.pending`): ½ the client, the rest the writer's state and (a
  watchable store) `watchStoreBody`.
* `γ.crevLb`: a monotone lower bound of `σ.crev + 1`, its authority split ½ the client, ¼ the
  compaction right, ¼ `s.revMu`'s resource.
* `γ.tok`: the backend share token, of total 1 (round 16, the review's F2): `mvccBackend γ q`
  holds `q` of it, so the whole share excludes every step that changes the history.
* `γ.frz`: the writer's frozen flag (a `Bool` ghost variable): whole at `false` in the writer's
  invariant while not frozen, half at `true` there and half the freezer's while frozen
  (`Api/InvStoreX.lean`, `writerInvBodyX`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndex
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.DGhostVar
public import Perennial.Ghost.MonoNat
public import Perennial.Ghost.MonoList
public import Perennial.Proof.TokSet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI

/-- The API's ghost names of a store. -/
structure AbsNames where
  abs : GName
  pnd : GName
  crevLb : GName
  tok : GName
  frz : GName
  /-- the notified log (`σ.notifiedLog`), a monotone list: its authority whole in `mvccState`
  (stage 2, the watch chain, 2026-11-04: a send records a lower bound of it, which the client
  compares with its state in `wsRecv_ok.law`'s plain entailment) -/
  nl : GName
  /-- the store's location (`KV.Compact.contract`, 2026-11-06: a read-only ghost variable,
  `locIs`): the handle's (`isMvcc`) and the open token's (`mvccOpen`) agree on the store they are
  of (the inner store of a watchable one) -/
  loc : GName := 0
  /-- the compaction revision as `s.mu` and the writer's state see it (M4, track B, 2026-11-06: a
  ghost variable, half in `s.mu`'s resource at the lock's fraction, half in the writer's slot), so
  that a write transaction, holding `s.mu` shared and the writer's state, knows the writer's view
  of the compaction revision is the one its reads answer at; moved by `updateCompactRev` and
  `Restore`, which hold `s.mu` exclusively and the writer's state -/
  wcr : GName := 0
  /-- the client's reader tokens (`ownTokAuth`; the reader token carries the store's lock slots,
  2026-11-07, `notes/decisions.md`): `mvccReaders γ n` is `n` of them; the handle's readers' pool
  (`rdkPool`) holds the authority, with a reader's lock slots and ticket for each token out, so a
  token is the right to one reader of the store, without a thread token -/
  rdk : GName := 0

instance absNames_countable : Pos.Countable AbsNames :=
  countableOfLeftInverse
    (fun x : AbsNames => (x.abs, x.pnd, x.crevLb, x.tok, x.frz, x.nl, x.loc, x.wcr, x.rdk))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2⟩)
    (fun _ => rfl)

/-- A compaction revision as the lower bound's count (`-1` is `0`). -/
def crevN (c : Int) : Nat := (c + 1).toNat

section ghost
variable {GF : BundledGFunctors} [AllG GF]

/-- A share of the client's view of the history and compaction revision. -/
def absPart (γ : AbsNames) (q : Qp) (L : Log) (c : Int) : IProp GF := ghostVar γ.abs q (L, c)

/-- A share of the pending revision. -/
def pndPart (γ : AbsNames) (q : Qp) (p : Option (List Change)) : IProp GF := ghostVar γ.pnd q p

/-- A share of the compaction revision's authority. -/
def crevAuth (γ : AbsNames) (q : Qp) (c : Int) : IProp GF := monoNatAuthOwn γ.crevLb q (crevN c)

/-- The compaction revision is at least `c` (persistent). -/
def crevAtLeast (γ : AbsNames) (c : Int) : IProp GF := monoNatLbOwn γ.crevLb (crevN c)

/-- **A share `q` of the writer's and `s.mu`'s compaction revision** (`AbsNames.wcr`). -/
def wcrPart (γ : AbsNames) (q : Qp) (c : Int) : IProp GF := ghostVar γ.wcr q c

/-- A share `q` of the backend share token. -/
def shareTok (γ : AbsNames) (q : Qp) : IProp GF := dghostVar γ.tok (.own q) ()

/-- The notified log's authority, at `N`. -/
def nlAuth (γ : AbsNames) (q : Qp) (N : Log) : IProp GF := monoListAuthOwn γ.nl q N

/-- **The store is at `l`** (persistent; `AbsNames.loc`). -/
def locIs (γ : AbsNames) (l : Loc) : IProp GF := dghostVar γ.loc DFrac.discard l

/-- A lower bound of the notified log (persistent). -/
def nlLb (γ : AbsNames) (N : Log) : IProp GF := monoListLbOwn γ.nl N

/-- **`s.revMu`'s part of the API's ghost state** at fraction `q` (§1): a quarter of `q` of the
view at the lock's log and compaction revision, and of the compaction revision's authority. -/
def revMuAbs (a : AbsNames) (q : Qp) (L : Log) (c : Int) : IProp GF :=
  iprop(absPart a q.half.half L c ∗ crevAuth a q.half.half c)

end ghost

end api
end mvcc
end EtcdGrove
end Perennial
