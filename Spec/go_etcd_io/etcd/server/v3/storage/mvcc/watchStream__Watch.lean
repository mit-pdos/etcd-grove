/-
`watchStream.Watch` (watcher.go). Lean-first (no Rocq counterpart); see `InvWatchStream.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStream
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`ws.Watch(ctx, id, key, end, startRev, fcs...)`** with an id the stream assigns
(`AutoWatchID`, `0`; unit W-M2: an explicit id can be one reused after a cancel,
`issues/etcd-watch-id-reuse-stale-events.md`, and its watcher cannot be recorded in the channel's
id map; the verified server never passes one, `v3rpc.watchReqOk`): the range `key`/`end` (`end`
empty: a single key, or from `key` if `end` is non-nil: the store's business) and the filters
are handed to the store for good. It returns `nil` with the id it assigned only for a non-empty
range (`end` empty or `key < end`); otherwise `-1` with `ErrEmptyWatcherRange` (an empty range,
or the stream closed). The start revision is at least `0`; the caller's `P.R` is lent to the
store. On success it returns the watcher `w` the store registered (`P.IW`), what the store says
of it (`P.IWF`: its range `watchRangeOf k e endk startRev id'`, the filters, its first revision
`lo`), and that the stream assigned the id to `w` (`idAssigned`: such an id names one watcher of
the stream for good, `idAssigned_agree`; the channel's invariant knows it from the registration
on, `chanRegFact`), with its token (`idTok`: one per id, `idTok_excl`; the watch slice's unit
W-C), and (K1b) the channel it registered `w` on (`P.OC`), whose registration indices the stream
names (`γ.regi = γc.regi`). -/
abbrev mvcc.watchStream.Watch.spec : Prop :=
  ∀ (ws : Loc) (wa : GoInterface) (P : mvcc.WatchParams GF) (γ : mvcc.WsStreamNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (id : w64) (key endk fcs : GoSlice) (k e : List w8)
    (fs : List GoFunc) (startRev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchStream ws wa P γ ∗ context.isContext ctx cd ∗
      key ↦*□ k ∗ endk ↦*□ e ∗ fcs ↦*□ fs ∗ ([∗list] f ∈ fs, P.F f) ∗ P.R ∗ P.T ∗
      ⌜0 ≤ sint.Z startRev ∧ id = W64 0⌝ }}
    (App (App (App (App (App (App (Val (ws @!! go.GoType.PointerType watchStream.ty @!! go!"Watch"))
      (Val #(GoInterface.ok ctx))) (Val #id)) (Val #key)) (Val #endk)) (Val #startRev)) (Val #fcs))
  {{ (id' : w64) (err : GoInterface), RET (PairV #id' #err);
      ((⌜err = GoInterface.nil⌝ ∗ ⌜e = [] ∨ go.GoStringLt k e⌝ ∗
        ∃ (w : Loc) (lo : Nat), P.IW w ∗
          P.IWF w (mvcc.watchRangeOf k e endk startRev id') fcs lo ∗
          mvcc.idAssigned γ id' w ∗ mvcc.idTok γ id' ∗
          (∃ γc : mvcc.WatchChanNames, P.OC w γc ∗ ⌜γ.regi = γc.regi⌝) ∗ P.WS w) ∨
       (⌜id' = W64 (-1)⌝ ∗ globalAddr ErrEmptyWatcherRange ↦□ err)) ∗ P.R }}

/-- **Candidate** (round 8, 2026-11-02, `notes/mvcc-api-candidate.md`). `st.Watch(ctx, 0, key, end,
startRev, fcs...)`, with an id the stream chooses (`0`, `AutoWatchID`: a scope restriction, as etcd's
client asks), a positive start revision (2026-11-02, the proof: at `0` the first revision is the
state's at the registration, inside the store's `watch`; a negative one replays the history or gets
a compaction response at `-1`, against the documentation, `issues/etcd-mvcc-watch-negative-start-rev.md`;
v3rpc rejects it), filters implementing `fs`:
* an empty range (`end` not empty and not above `key`): `ErrEmptyWatcherRange`, id `-1`, the
  caller's update back;
* a closed stream (a holder of a share of its open token refutes it): the same;
* else a watcher of the range under a fresh id `id` (the stream's: the registrar's view is a map
  keyed by it, 2026-11-02), registered after the responses sent so far (`k`), live, from the start
  revision, by the caller's update at the store's state `σ` (unchanged) and the registrar's view `W`
  (extended); `nil`, the id. -/
abbrev mvcc.watchStream.Watch.specC : Prop :=
  ∀ (st : Loc) (γ : mvcc.MvccName) (ι : mvcc.WsName) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (key endk fcs : GoSlice) (kk e : List w8)
    (fs : List (mvcc.EvM → Bool)) (startRev : w64)
    (Q : mvcc.MvccState → GMap w64 mvcc.WInfo → w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isMvccWatchStream st γ ι ∗ threadTok ∗ context.isContext ctx cd ∗
      key ↦*□ kk ∗ endk ↦*□ e ∗ mvcc.filtersImpl fcs fs ∗ ⌜0 < sint.Z startRev⌝ ∗
      AU <{ ∃∃ (σ : mvcc.MvccState) (W : GMap w64 mvcc.WInfo), mvcc.mvccState γ σ ∗ mvcc.wsWatchers ι W }>
          @ ⊤ \ ↑mvcc.mvccN, ∅
        <{ ∀∀ (id : w64) (k : Nat), ⌜W !! id = none⌝ ∗ mvcc.mvccState γ σ ∗
              mvcc.wsWatchers ι (W.insert id ⟨mvcc.watchRangeOf kk e endk startRev id, fs,
                sint.nat startRev, k, true⟩), COMM Q σ W id }> }}
    (App (App (App (App (App (App (Val (st @!! go.GoType.PointerType watchStream.ty @!! go!"Watch"))
      (Val #(GoInterface.ok ctx))) (Val #(W64 0))) (Val #key)) (Val #endk)) (Val #startRev)) (Val #fcs))
  {{ (id : w64) (err : GoInterface), RET (PairV #id #err); threadTok ∗
      ((⌜err = GoInterface.nil ∧ (e = [] ∨ go.GoStringLt kk e)⌝ ∗
          ∃ (σ : mvcc.MvccState) (W : GMap w64 mvcc.WInfo), Q σ W id) ∨
       (⌜id = W64 (-1)⌝ ∗ globalAddr ErrEmptyWatcherRange ↦□ err ∗
          (⌜e ≠ [] ∧ ¬ go.GoStringLt kk e⌝ ∨ □ (∀ q : Qp, mvcc.wsOpen ι q ={⊤}=∗ False)) ∗
          AU <{ ∃∃ (σ : mvcc.MvccState) (W : GMap w64 mvcc.WInfo), mvcc.mvccState γ σ ∗ mvcc.wsWatchers ι W }>
              @ ⊤ \ ↑mvcc.mvccN, ∅
            <{ ∀∀ (id : w64) (k : Nat), ⌜W !! id = none⌝ ∗ mvcc.mvccState γ σ ∗
                  mvcc.wsWatchers ι (W.insert id ⟨mvcc.watchRangeOf kk e endk startRev id, fs,
                    sint.nat startRev, k, true⟩), COMM Q σ W id }>)) }}

end spec

end EtcdGrove
end Perennial
