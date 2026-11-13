/-
**The watch server over mvcc's API** (the mvcc API migration, strict M1, 2026-11-05): the part of
v3rpc's watch vocabulary that sees mvcc (only through its API, `Spec/.../mvcc/Api.lean`), and the
proof obligations the API introduces in v3rpc (the draft `notes/mvcc-api-clients/WatchSpecs.lean`,
§1, §3, §7, frozen). It imports mvcc's API and nothing of the server, so that it is checked on its
own.

* **The server's side** (`SrvW`, `srvPeek`, `srvWOk`, `srvOnce`; the draft's §1): what the server
  gives the watch path, as parameters and their laws.
* **One run's ghost state** (`RegInfo`, `regIs`, `idTok`, `rcvLb`, `closeTok`; the run's invariant
  `wsInvG` at `wsN`, the send loop's snapshot `rcvSnapG`; the draft's §3, §4): generic in the
  client's cancel requests `cq` (v3rpc's `cancelQ γs`), so that `InvWatch.lean`'s `wsInv r` and
  `rcvSnap r` are these at the run's names.
* **The obligations** (the draft's §7): the updates `recvLoop` passes to `Watch` (`watch_au`, O1),
  `Cancel` (`cancel_au`, O2) and `Rev` (`rev_au`), the one `close` passes to `Close` (`close_au`,
  O3), the send loop's snapshot after a receive (`snap_after_recv`, O4), and the drain's poll and
  its empty case (`drain_poll`, `drain_empty`, O5). The probe
  `notes/mvcc-api-probes/WatchClientProbe.lean` proved them on a model; these are at the run's
  definitions.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.DGhostVar
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.RangeModel
public import Proof.go_etcd_io.etcd.cache.v3.EtcdModel

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## The pure models (the draft's §2) -/

instance WResp.countable : Pos.Countable mvcc.api.WResp :=
  .ofInjective (fun r => Pos.Countable.encode (r.id, r.evs, r.rev, r.compactRev))
    (fun a b h => by
      have := Pos.encode_inj h
      cases a; cases b; simp_all)

/-- **A registry entry**: what v3rpc records of a watcher at `Watch`'s commit (the API's `WInfo`
but its filters, `[]` for every watcher of the server, and its liveness, which only `wsState`
has). -/
structure RegInfo where
  rg : mvcc.WatchRange
  lo : Nat
  k : Nat

instance RegInfo.countable : Pos.Countable RegInfo :=
  .ofInjective (fun r => Pos.Countable.encode (r.rg, r.lo, r.k))
    (fun a b h => by
      have := Pos.encode_inj h
      cases a; cases b; simp_all)

/-- A watcher's registry entry. -/
def regInfoOf (w : mvcc.api.WInfo) : RegInfo := ⟨w.rg, w.lo, w.k⟩

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The watchable store `wsl` as `mvcc.WatchableKV`. -/
abbrev wsIface (wsl : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty) #wsl

/-- The mvcc watch stream `wsp` as `mvcc.WatchStream`. -/
abbrev wspIface (wsp : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.mvcc.watchStream.ty) #wsp

end addrs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! ## What the server must give the watch path (the draft's §1) -/

/-- **The server's side of the watch path**: the store's handle the server's invariant holds (the
server draft's `E.kv`), the store's name, the namespace of the server's invariant holding
`mvccState`, the notified log's certified lower bound `histLb` (replacing `mvcc.evLog`:
`idxSealed ∗ certOk`), and the compaction revision's permit `crevOk` (replacing `mvcc.crevPermAt`
as the watch path reads it). -/
structure SrvW (GF : BundledGFunctors) where
  /-- the store's handle the server's invariant holds (the server draft's `E.kv`) -/
  kv : GoInterface
  γm : mvcc.api.MvccName
  N : Namespace
  histLb : mvcc.Log → IProp GF
  crevOk : Int → IProp GF

/-- **The server's peek** (persistent): at any mask containing its namespace, the store's state
`σ` (left unchanged), with the certified lower bound of its notified log and its compaction
revision's permit. What `Watch`'s and `Rev`'s updates and the send loop's snapshot open; all three
give `mvccState γ σ` back unchanged. -/
def srvPeek (W : SrvW GF) : IProp GF :=
  iprop(□ ∀ (E : CoPset), ⌜↑W.N ⊆ E⌝ -∗ |={E, E \ ↑W.N}=> ∃ σ : mvcc.api.MvccState,
    mvcc.api.mvccState W.γm σ ∗ W.histLb σ.notifiedLog ∗ W.crevOk σ.crev ∗
    (mvcc.api.mvccState W.γm σ ={E \ ↑W.N, E}=∗ True))

instance srvPeek_persistent (W : SrvW GF) : Persistent (srvPeek W) := by
  unfold srvPeek; infer_instance

/-- **What the server gives the watch path** (persistent): the store's handle, which is the
watchable store at `wsl` (`E.kv = wsIface wsl`, xreview §6c: `shapes.law`'s per-type conjunct then
gives `NewWatchStream`'s contract, which `isMvcc` alone does not), the peek, its namespace outside
`mvccN` (so it opens inside `Watch`'s update, at `⊤ \ ↑mvccN`) and outside v3rpc's (`wsN`), and the
laws of `histLb` (agreement, prefix closure; and, round 16, a certified log's model facts: well
formed and of fewer than `2 ^ 63` revisions, from `mvccState_reachable` at the state it was taken
of, small from the receipt `⧖ (logCh σ.notifiedLog)` the server keeps with it (the API's notify
steps give it) and `receiptBound GF ≤ 2 ^ 62`, its keys short from the server's request checks:
today's `idxSealed_pure`, `sealed_logOk`, `srvLogsSmall`, `srvKVCoreM_keys`) and of `crevOk` (no
permit, or a positive revision's, downward closed; `kvCmpPermit_le`'s use). The client's model laws
over `histLb` (today's `watchLaws_srv` over `evLog`) are the client's. -/
def srvWOk (W : SrvW GF) (wsl : Loc) (wsN : Namespace) : IProp GF :=
  iprop(⌜W.kv = wsIface wsl⌝ ∗ mvcc.api.isMvcc W.kv W.γm ∗ srvPeek W ∗
    ⌜(↑W.N : CoPset) ⊆ ⊤ \ ↑mvcc.api.mvccN ∧ (↑wsN : CoPset) ⊆ ⊤ \ ↑mvcc.api.mvccN ∧
      (↑wsN : CoPset) ⊆ ⊤ \ ↑W.N⌝ ∗
    (□ ∀ L, W.histLb L -∗ □ W.histLb L) ∗
    (□ ∀ L L', W.histLb L -∗ W.histLb L' -∗ ⌜L <+: L' ∨ L' <+: L⌝) ∗
    (□ ∀ L L', ⌜L' <+: L⌝ -∗ W.histLb L -∗ W.histLb L') ∗
    (□ ∀ L, W.histLb L -∗ ⌜mvcc.LogWf' L ∧ L.length < 2 ^ 63 ∧ txn.LogSmall L ∧
      mvcc.LogPutsLe etcdKeyMax L⌝) ∗
    (□ ∀ c, W.crevOk c -∗ □ W.crevOk c))

/-- **The watch condition, the client's premise** (replacing `mvcc.watchNoDup`, which no longer
goes through v3rpc: the API states the watch facts under `onceUpTo`, and v3rpc forwards them
conditionally): every certified log and permitted compaction revision meet `onceUpTo` at every
first revision. Holds of a server that never compacts (`crevOk c → c = -1`: vacuous) and of one
whose revisions change each key at most once (`srvNoDupKeys`). -/
def srvOnce (W : SrvW GF) : IProp GF :=
  iprop(□ ∀ (L : mvcc.Log) (c : Int) (lo : Nat), W.histLb L -∗ W.crevOk c ={⊤}=∗
    ⌜mvcc.api.onceUpTo L lo c⌝)

/-! ## One run's ghost state (the draft's §3) -/

/-- The registry's entry (persistent). -/
def regIs (γreg : GName) (id : w64) (i : RegInfo) : IProp GF :=
  ghostMapElem γreg id DFrac.discard i

instance regIs_persistent (γreg : GName) (id : w64) (i : RegInfo) :
    Persistent (regIs (GF := GF) γreg id i) := by
  unfold regIs; infer_instance

instance regIs_timeless (γreg : GName) (id : w64) (i : RegInfo) :
    Timeless (regIs (GF := GF) γreg id i) := by
  unfold regIs; infer_instance

/-- The id's token (exclusive; a stream announces an id once). -/
def idTok (γtok : GName) (id : w64) : IProp GF := ghostMapElem γtok id (DFrac.own 1) ()

/-- The send loop's received list has `l` first (persistent). -/
def rcvLb (γr : GName) (l : List mvcc.api.WResp) : IProp GF := monoListLbOwn γr l

instance rcvLb_persistent (γr : GName) (l : List mvcc.api.WResp) :
    Persistent (rcvLb (GF := GF) γr l) := by
  unfold rcvLb; infer_instance

/-- The close token (exclusive; `close`'s until it closes the stream). -/
def closeTok (γcl : GName) : IProp GF := dghostVar γcl (DFrac.own 1) ()

instance closeTok_timeless (γcl : GName) : Timeless (closeTok (GF := GF) γcl) := by
  unfold closeTok; infer_instance

theorem closeTok_excl (γcl : GName) : closeTok (GF := GF) γcl ∗ closeTok γcl ⊢ False := by
  unfold closeTok
  iintro ⟨H1, H2⟩
  ihave %H := dghostVar_valid_2 γcl () (DFrac.own 1) () (DFrac.own 1) $$ H1 H2
  exfalso
  exact absurd (DFrac.valid_op_own H.1) (by simp)

/-- The namespace of v3rpc's per-run invariant. -/
def wsN : Namespace := (nroot .@ "v3rpc") .@ "ws"

/-- **v3rpc's invariant of a run** (the draft's `wsInv`, at the run's names and its client's cancel
requests `cq`; `InvWatch.lean`'s `wsInv r`): the stream's state `S`; the registry agrees with `S`
(every watcher's `RegInfo`, its discarded entries kept, so the snapshot can copy them; the id
tokens minted for exactly `S`'s ids); every watcher unfiltered; every watcher not live was
cancelled at the client's request (`cq`); the stream open, or the close token deposited. -/
def wsInvG (ι : mvcc.api.WsName) (γreg γtok γcl : GName) (cq : w64 → IProp GF) : IProp GF :=
  iprop(∃ (S : mvcc.api.StreamState) (R : GMap w64 RegInfo) (T : GMap w64 Unit),
    mvcc.api.wsState ι S ∗ ghostMapAuth γreg 1 R ∗ ghostMapAuth γtok 1 T ∗
    ⌜∀ id, R !! id = (S.ws !! id).map regInfoOf ∧ ((T !! id).isSome ↔ (S.ws !! id).isSome)⌝ ∗
    ⌜∀ id w, S.ws !! id = some w → w.fs = []⌝ ∗
    □ ([∗map] id ↦ i ∈ R, regIs γreg id i) ∗
    ([∗map] id ↦ w ∈ S.ws, ⌜w.live = true⌝ ∨ cq id) ∗
    (⌜S.closed = false⌝ ∨ closeTok γcl))

/-- **The send loop's snapshot of the received responses `rs`** (the draft's `rcvSnap`, at the
server's side `W`, the registry `γreg` and the cancel requests `cq`; `InvWatch.lean`'s
`rcvSnap r`): the API's watch guarantee at some state `σ` and stream state `S` of a moment after the
receive of `rs`'s last, the notified log's certified lower bound and the compaction revision's
permit at it, each of `S`'s watchers registered (`regIs`) and live or cancelled at the client's
request. -/
def rcvSnapG (W : SrvW GF) (γreg : GName) (cq : w64 → IProp GF) (rs : List mvcc.api.WResp)
    (σ : mvcc.api.MvccState) (S : mvcc.api.StreamState) : IProp GF :=
  iprop(⌜mvcc.api.wsRecvOk σ S rs ∧ ∀ id w, S.ws !! id = some w → w.fs = []⌝ ∗
    W.histLb σ.notifiedLog ∗ W.crevOk σ.crev ∗
    □ ([∗map] id ↦ w ∈ S.ws, regIs γreg id (regInfoOf w) ∗ (⌜w.live = true⌝ ∨ cq id)))

/-- The update `Watch` commits for a fresh, unfiltered watcher (the draft's O1 `COMM`): on a
closed stream the id `-1`; on an open one its registry entry, its token, the stream's sent count
at its stamp, the certified log it starts after, nothing pending, its first revision and range. -/
def watchQ (W : SrvW GF) (ι : mvcc.api.WsName) (γreg γtok : GName) (kk e : List w8)
    (endk : GoSlice) (startRev : w64) (σ : mvcc.api.MvccState) (S : mvcc.api.StreamState)
    (id : w64) : IProp GF :=
  if S.closed then iprop(⌜id = W64 (-1)⌝) else
    iprop(∃ i : RegInfo, regIs γreg id i ∗ idTok γtok id ∗ mvcc.api.wsSentLb ι i.k ∗
      W.histLb σ.log ∗ ⌜σ.pending = none ∧ i.lo = mvcc.api.watchLo σ startRev ∧
        i.rg = mvcc.watchRangeOf kk e endk startRev id⌝)

/-! ## The laws as instances (from `persistent.law`) -/

/-- **A received response, read-only for good** (k8s 7f-3b): `wrespIs` with each event's `PrevKv`
field given up (`mvcc.evIs`, the store's form). What the send loop reads of a response until it
writes `PrevKv` (the v3rpc part of 7f-3b). -/
def wrespRO (v : go_etcd_io.etcd.server.v3.storage.mvcc.WatchResponse) (r : mvcc.api.WResp) :
    IProp GF :=
  iprop(⌜v.WatchID' = r.id ∧ v.Revision' = r.rev ∧ v.CompactRevision' = r.compactRev⌝ ∗
    ∃ ps : List Loc, v.Events' ↦*□ ps ∗ ⌜ps.length = r.evs.length⌝ ∗
      [∗list] x ∈ ps.zip r.evs, mvcc.evIs x.1 x.2)

instance wrespRO_persistent (v : go_etcd_io.etcd.server.v3.storage.mvcc.WatchResponse)
    (x : mvcc.api.WResp) : Persistent (wrespRO (GF := GF) v x) := by
  unfold wrespRO; infer_instance

/-- A received response's copies given up for good. -/
theorem wrespIs_ro (v : go_etcd_io.etcd.server.v3.storage.mvcc.WatchResponse) (x : mvcc.api.WResp) :
    mvcc.api.wrespIs (GF := GF) v x ⊢ |==> wrespRO v x := by
  unfold mvcc.api.wrespIs wrespRO
  iintro ⟨%Hf, %ps, #Hs, %Hl, Hevs⟩
  imod mvcc.evOwns_persist _ 1 $$ Hevs with #Hevs
  imodintro
  isplitr
  · ipureintro; exact Hf
  iexists ps
  iframe Hs Hevs
  ipureintro; exact Hl

theorem wsInvG_timeless (hP : mvcc.api.persistent.law (GF := GF)) (ι : mvcc.api.WsName)
    (γreg γtok γcl : GName) (cq : w64 → IProp GF) [∀ id, Timeless (cq id)] :
    Timeless (wsInvG ι γreg γtok γcl cq) := by
  have : ∀ ι S, Timeless (mvcc.api.wsState (GF := GF) ι S) := hP.2.2.2.2.2.2.1
  unfold wsInvG; infer_instance

theorem srvWOk_persistent (hP : mvcc.api.persistent.law (GF := GF)) (W : SrvW GF) (wsl : Loc)
    (wsN : Namespace) : Persistent (srvWOk W wsl wsN) := by
  have : ∀ kv γ, Persistent (mvcc.api.isMvcc (GF := GF) kv γ) := hP.1
  unfold srvWOk; infer_instance

/-- The masks of `srvWOk`: the server's namespace opens after v3rpc's, inside `⊤ \ ↑mvccN`. -/
theorem masks_nested {N wsN : Namespace} (h1 : (↑N : CoPset) ⊆ ⊤ \ ↑mvcc.api.mvccN)
    (h2 : (↑wsN : CoPset) ⊆ ⊤ \ ↑mvcc.api.mvccN) (h3 : (↑wsN : CoPset) ⊆ ⊤ \ ↑N) :
    (↑N : CoPset) ⊆ (⊤ \ ↑mvcc.api.mvccN) \ ↑wsN ∧ (↑N : CoPset) ⊆ ⊤ \ ↑wsN := by
  have hd : ∀ p, p ∈ (↑N : CoPset) → p ∉ (↑wsN : CoPset) := by
    intro p hp hw
    have := h3 p hw
    rw [Iris.Std.LawfulSet.mem_diff] at this
    exact this.2 hp
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · rw [Iris.Std.LawfulSet.mem_diff]
    exact ⟨h1 p hp, hd p hp⟩
  · rw [Iris.Std.LawfulSet.mem_diff]
    exact ⟨CoPset.mem_full, hd p hp⟩

variable (cq : w64 → IProp GF) [hcqP : ∀ id, Persistent (cq id)] [hcqT : ∀ id, Timeless (cq id)]

/-! ## The run's allocation (in `watchServer.Watch`) -/

/-- **The run's invariant from `NewWatchStream`'s stream state** (`wsState ι wsStart`): the
registry, the id tokens and the close token allocated, the stream open; the close token for
`close`. -/
theorem wsInvG_alloc (ι : mvcc.api.WsName) :
    mvcc.api.wsState (GF := GF) ι mvcc.api.wsStart ⊢
      |={⊤}=> ∃ γreg γtok γcl : GName, inv wsN (wsInvG ι γreg γtok γcl cq) ∗ closeTok γcl := by
  iintro HS
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := RegInfo) with ⟨%γreg, HR⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := Unit) with ⟨%γtok, HT⟩
  imod dghostVar_alloc (GF := GF) () with ⟨%γcl, Hcl⟩
  imod (inv_alloc wsN ⊤ (wsInvG ι γreg γtok γcl cq)) $$ [HS HR HT] with #Hinv
  · inext
    iunfold wsInvG
    iexists mvcc.api.wsStart, ∅, ∅
    iframe HS HR HT
    isplitr
    · ipureintro
      intro id
      simp [mvcc.api.wsStart, GMap.lookup_empty]
    isplitr
    · ipureintro
      intro id w h
      simp [mvcc.api.wsStart, GMap.lookup_empty] at h
    isplitr
    · iintro !>
      iapply BigSepM.bigSepM_empty.2
      iempintro
    isplitr
    · rw [show mvcc.api.wsStart.ws = (∅ : GMap w64 mvcc.api.WInfo) from rfl]
      iapply BigSepM.bigSepM_empty.2
      iempintro
    ileft; ipureintro; rfl
  imodintro
  iexists γreg, γtok, γcl
  iframe Hinv
  unfold closeTok
  iexact Hcl

/-! ## O1: the update `recvLoop` passes to `Watch` -/

/-- The registry's relation to the stream's state, after a fresh watcher registers. -/
theorem rel_register (S : mvcc.api.StreamState) (R : GMap w64 RegInfo) (T : GMap w64 Unit)
    (id : w64) (w : mvcc.api.WInfo) (hw : w.fs = [])
    (Hrel : ∀ x, R !! x = (S.ws !! x).map regInfoOf ∧ ((T !! x).isSome ↔ (S.ws !! x).isSome))
    (Hfs : ∀ x w, S.ws !! x = some w → w.fs = []) :
    (∀ x, (R.insert id (regInfoOf w)) !! x = ((S.register id w).ws !! x).map regInfoOf ∧
      (((T.insert id ()) !! x).isSome ↔ ((S.register id w).ws !! x).isSome)) ∧
    (∀ x w', (S.register id w).ws !! x = some w' → w'.fs = []) := by
  refine ⟨fun x => ?_, fun x w' hx => ?_⟩
  · by_cases hx : id = x
    · subst hx
      show (R.insert id _).lookup id = ((S.ws.insert id _).lookup id).map regInfoOf ∧
        (((T.insert id ()).lookup id).isSome ↔ ((S.ws.insert id _).lookup id).isSome)
      rw [GMap.lookup_insert, GMap.lookup_insert, GMap.lookup_insert]
      simp
    · show (R.insert id _).lookup x = ((S.ws.insert id _).lookup x).map regInfoOf ∧
        (((T.insert id ()).lookup x).isSome ↔ ((S.ws.insert id _).lookup x).isSome)
      rw [GMap.lookup_insert_ne _ _ hx, GMap.lookup_insert_ne _ _ hx, GMap.lookup_insert_ne _ _ hx]
      exact Hrel x
  · by_cases hix : id = x
    · subst hix
      have : (S.ws.insert id w).lookup id = some w' := hx
      rw [GMap.lookup_insert] at this
      cases this; exact hw
    · have : (S.ws.insert id w).lookup x = some w' := hx
      rw [GMap.lookup_insert_ne _ _ hix] at this
      exact Hfs x w' this

/-- **O1, `watch_au`**: the update `recvLoop` passes to `Watch` (unfiltered), from the run's
invariant and the server's peek, at `⊤ \ ↑mvccN`. At the commit on an open stream, the registry
and the id tokens get the fresh `id`, the watcher is live; on a closed one nothing changes. -/
theorem watch_au (hP : mvcc.api.persistent.law (GF := GF)) (W : SrvW GF) (wsl : Loc)
    (ι : mvcc.api.WsName) (γreg γtok γcl : GName) (kk e : List w8) (endk : GoSlice)
    (startRev : w64) :
    inv wsN (wsInvG ι γreg γtok γcl cq) ∗ srvWOk W wsl wsN ⊢
    AU <{ ∃∃ (σ : mvcc.api.MvccState) (S : mvcc.api.StreamState),
          mvcc.api.mvccState W.γm σ ∗ mvcc.api.wsState ι S }> @ ⊤ \ ↑mvcc.api.mvccN, ∅
      <{ ∀∀ (id : w64) (k : Nat), mvcc.api.mvccState W.γm σ ∗
          (if S.closed = true then ⌜id = W64 (-1)⌝ ∗ mvcc.api.wsState ι S
           else ⌜S.ws !! id = none ∧ id ≠ W64 (-1) ∧ σ.pending = none⌝ ∗ mvcc.api.wsSentLb ι k ∗
             mvcc.api.wsState ι (S.register id
               { rg := mvcc.watchRangeOf kk e endk startRev id, fs := [],
                 lo := mvcc.api.watchLo σ startRev, k := k, live := true })),
        COMM watchQ W ι γreg γtok kk e endk startRev σ S id }> := by
  have : ∀ γ σ, Timeless (mvcc.api.mvccState (GF := GF) γ σ) := hP.2.2.2.2.2.1
  have : ∀ ι S, Timeless (mvcc.api.wsState (GF := GF) ι S) := hP.2.2.2.2.2.2.1
  have : ∀ ι n, Persistent (mvcc.api.wsSentLb (GF := GF) ι n) := hP.2.2.1
  have := wsInvG_timeless hP ι γreg γtok γcl cq
  have := srvWOk_persistent hP W wsl wsN
  iintro ⟨#Hinv, #HW⟩
  iunfold srvWOk at HW
  icases HW with ⟨-, -, #Hpk, %Hm, #Hhp, -, -, -, -⟩
  obtain ⟨hN1, hN2⟩ := masks_nested Hm.1 Hm.2.1 Hm.2.2
  iauintro
  unfold atomic_acc
  iinv Hinv with > Hi Hclose
  iunfold wsInvG at Hi
  icases Hi with ⟨%S, %R, %T, HS, HR, HT, %Hrel, %Hfs, #Hreg, Hcq, Hcl⟩
  iunfold srvPeek at Hpk
  icases Hpk with #Hpk
  imod Hpk $$ %((⊤ \ ↑mvcc.api.mvccN) \ ↑wsN) %hN1 with ⟨%σ, Hσ, Hh, -, Hclose2⟩
  ihave #Hh := Hhp $$ Hh
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑mvcc.api.mvccN) \ ↑wsN) \ ↑W.N from
    Std.LawfulSet.empty_subset)
  iintro Hclose3
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ, S
  iframe Hσ HS
  isplit
  · -- abort
    iintro ⟨Hσ, HS⟩
    imod Hclose3 with -
    imod Hclose2 $$ Hσ with -
    imod Hclose $$ [HS HR HT Hcq Hcl] with -
    · inext; iunfold wsInvG; iexists S, R, T; iframe; iframe #; ipureintro; exact ⟨Hrel, Hfs⟩
    imodintro; iempintro
  · -- commit
    iintro %id %k ⟨Hσ, Hres⟩
    imod Hclose3 with -
    imod Hclose2 $$ Hσ with -
    unfold watchQ
    by_cases hcl : S.closed = true
    · simp only [ite_eq_left hcl]
      icases Hres with ⟨%Hid, HS⟩
      imod Hclose $$ [HS HR HT Hcq Hcl] with -
      · inext; iunfold wsInvG; iexists S, R, T; iframe HS HR HT Hreg Hcq Hcl
        isplitr
        · ipureintro; exact Hrel
        ipureintro; exact Hfs
      imodintro; ipureintro; exact Hid
    · simp only [ite_eq_right hcl]
      icases Hres with ⟨%Hfr, #Hk, HS⟩
      obtain ⟨hfresh, -, hpend⟩ := Hfr
      let w : mvcc.api.WInfo :=
        ⟨mvcc.watchRangeOf kk e endk startRev id, [], mvcc.api.watchLo σ startRev, k, true⟩
      have hR : R.lookup id = none := by rw [(Hrel id).1, hfresh]; rfl
      have hT : T.lookup id = none := by
        cases hc : T.lookup id with
        | none => rfl
        | some _ =>
          have := (Hrel id).2.1 (by show (T.lookup id).isSome; rw [hc]; rfl)
          rw [hfresh] at this; exact absurd this (by simp)
      imod ghost_map_insert_persist id (regInfoOf w) hR $$ HR with ⟨HR, #Hid0⟩
      ihave #Hid : regIs (GF := GF) γreg id (regInfoOf w) $$ []
      · iunfold regIs; iexact Hid0
      imod ghost_map_insert id () hT $$ HT with ⟨HT, Htok0⟩
      ihave Htok : idTok (GF := GF) γtok id $$ [Htok0]
      · iunfold idTok; iexact Htok0
      have Hrel' := rel_register S R T id w rfl Hrel Hfs
      imod Hclose $$ [HS HR HT Hcq Hcl] with -
      · inext
        iunfold wsInvG
        iexists S.register id w, R.insert id (regInfoOf w), T.insert id ()
        iframe HS HR HT
        isplitr
        · ipureintro; exact Hrel'.1
        isplitr
        · ipureintro; exact Hrel'.2
        isplitr
        · iintro !>
          iapply (BigSepM.bigSepM_insert (Φ := fun (id : w64) (i : RegInfo) => regIs (GF := GF) γreg id i) hR).2
          iframe Hid Hreg
        isplitl [Hcq]
        · rw [show (S.register id w).ws = Std.insert S.ws id w from rfl]
          iapply (BigSepM.bigSepM_insert
            (Φ := fun (id : w64) (w : mvcc.api.WInfo) => iprop(⌜w.live = true⌝ ∨ cq id))
            (show Std.get? S.ws id = none from hfresh)).2
          iframe Hcq
          ileft; ipureintro; rfl
        · icases Hcl with (%Hop | Hcl)
          · ileft; ipureintro; exact Hop
          · iright; iexact Hcl
      imodintro
      iexists regInfoOf w
      iframe Hid Htok
      isplitr
      · rw [show (regInfoOf w).k = k from rfl]; iexact Hk
      isplitr
      · have hlog : σ.notifiedLog = σ.log := by
          unfold mvcc.api.MvccState.notifiedLog; rw [hpend]
        rw [← hlog]
        iexact Hh
      ipureintro; exact ⟨hpend, rfl, rfl⟩

/-! ## O2: the update `recvLoop` passes to `Cancel` -/

/-- **O2, `cancel_au`**: the update `recvLoop` passes to `Cancel id`, with the client's cancel
request (`cq id`): the watcher, if any, not live, its cancel fact kept. -/
theorem cancel_au (hP : mvcc.api.persistent.law (GF := GF)) (ι : mvcc.api.WsName)
    (γreg γtok γcl : GName) (id : w64) :
    inv wsN (wsInvG ι γreg γtok γcl cq) ∗ cq id ⊢
    AU <{ ∃∃ (S : mvcc.api.StreamState), mvcc.api.wsState ι S }> @ ⊤ \ ↑mvcc.api.mvccN, ∅
      <{ mvcc.api.wsState ι (S.cancel id), COMM True }> := by
  have : ∀ ι S, Timeless (mvcc.api.wsState (GF := GF) ι S) := hP.2.2.2.2.2.2.1
  have := wsInvG_timeless hP ι γreg γtok γcl cq
  iintro ⟨#Hinv, #Hq⟩
  iauintro
  unfold atomic_acc
  iinv Hinv with > Hi Hclose
  · unfold wsN mvcc.api.mvccN; solve_ndisj
  iunfold wsInvG at Hi
  icases Hi with ⟨%S, %R, %T, HS, HR, HT, %Hrel, %Hfs, #Hreg, Hcq, Hcl⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvcc.api.mvccN) \ ↑wsN from
    Std.LawfulSet.empty_subset)
  iintro Hclose3
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists S
  iframe HS
  isplit
  · iintro HS
    imod Hclose3 with -
    imod Hclose $$ [HS HR HT Hcq Hcl] with -
    · inext; iunfold wsInvG; iexists S, R, T; iframe; iframe #; ipureintro; exact ⟨Hrel, Hfs⟩
    imodintro; iempintro
  · iintro HS
    imod Hclose3 with -
    cases hw : S.ws !! id with
    | none =>
      have hc : S.cancel id = S := by unfold mvcc.api.StreamState.cancel; rw [hw]
      rw [hc]
      imod Hclose $$ [HS HR HT Hcq Hcl] with -
      · inext; iunfold wsInvG; iexists S, R, T; iframe; iframe #; ipureintro; exact ⟨Hrel, Hfs⟩
      imodintro; itrivial
    | some w =>
      have hc : S.cancel id = { S with ws := S.ws.insert id { w with live := false } } := by
        unfold mvcc.api.StreamState.cancel; rw [hw]
      rw [hc]
      imod Hclose $$ [HS HR HT Hcq Hcl] with -
      · inext
        iunfold wsInvG
        iexists { S with ws := S.ws.insert id { w with live := false } }, R, T
        iframe HS HR HT Hcl
        isplitr
        · ipureintro
          intro x
          · by_cases hx : id = x
            · subst hx
              show R.lookup id = ((S.ws.insert id _).lookup id).map regInfoOf ∧
                ((T.lookup id).isSome ↔ ((S.ws.insert id _).lookup id).isSome)
              rw [GMap.lookup_insert]
              have h1 := Hrel id
              rw [hw] at h1
              exact ⟨h1.1, by simpa using h1.2⟩
            · show R.lookup x = ((S.ws.insert id _).lookup x).map regInfoOf ∧
                ((T.lookup x).isSome ↔ ((S.ws.insert id _).lookup x).isSome)
              rw [GMap.lookup_insert_ne _ _ hx]
              exact Hrel x
        isplitr
        · ipureintro
          intro x w' hx
          · by_cases hix : id = x
            · subst hix
              have : (S.ws.insert id { w with live := false }).lookup id = some w' := hx
              rw [GMap.lookup_insert] at this
              cases this; exact Hfs id w hw
            · have : (S.ws.insert id { w with live := false }).lookup x = some w' := hx
              rw [GMap.lookup_insert_ne _ _ hix] at this
              exact Hfs x w' this
        isplitr
        · iexact Hreg
        icases (BigSepM.bigSepM_delete
          (Φ := fun (id : w64) (w : mvcc.api.WInfo) => iprop(⌜w.live = true⌝ ∨ cq id))
          (show Std.get? S.ws id = some w from hw)).1 $$ Hcq with ⟨-, Hcq⟩
        rw [show ({ S with ws := S.ws.insert id { w with live := false } } : mvcc.api.StreamState).ws
          = Std.insert S.ws id { w with live := false } from rfl]
        iapply (BigSepM.bigSepM_insert_delete
          (Φ := fun (id : w64) (w : mvcc.api.WInfo) => iprop(⌜w.live = true⌝ ∨ cq id))).2
        iframe Hcq
        iright; iexact Hq
      imodintro; itrivial

/-! ## O3: the update `close` passes to `Close` -/

/-- **O3, `close_au`**: the update `close` passes to `Close`: the close token shows the stream
open, and is deposited. -/
theorem close_au (hP : mvcc.api.persistent.law (GF := GF)) (ι : mvcc.api.WsName)
    (γreg γtok γcl : GName) :
    inv wsN (wsInvG ι γreg γtok γcl cq) ∗ closeTok γcl ⊢
    AU <{ ∃∃ (S : mvcc.api.StreamState), mvcc.api.wsState ι S ∗ ⌜S.closed = false⌝ }>
        @ ⊤ \ ↑mvcc.api.mvccN, ∅
      <{ mvcc.api.wsState ι S.close, COMM True }> := by
  have : ∀ ι S, Timeless (mvcc.api.wsState (GF := GF) ι S) := hP.2.2.2.2.2.2.1
  have := wsInvG_timeless hP ι γreg γtok γcl cq
  iintro ⟨#Hinv, Htok⟩
  iauintro
  unfold atomic_acc
  iinv Hinv with > Hi Hclose
  · unfold wsN mvcc.api.mvccN; solve_ndisj
  iunfold wsInvG at Hi
  icases Hi with ⟨%S, %R, %T, HS, HR, HT, %Hrel, %Hfs, #Hreg, Hcq, Hcl⟩
  icases Hcl with (%Hop | Htok')
  rotate_left
  · iexfalso; iapply closeTok_excl γcl $$ [Htok Htok']; iframe
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvcc.api.mvccN) \ ↑wsN from
    Std.LawfulSet.empty_subset)
  iintro Hclose3
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists S
  iframe HS
  isplitr
  · ipureintro; exact Hop
  isplit
  · iintro ⟨HS, -⟩
    imod Hclose3 with -
    imod Hclose $$ [HS HR HT Hcq] with -
    · inext; iunfold wsInvG; iexists S, R, T; iframe HS HR HT Hreg Hcq
      isplitr
      · ipureintro; exact Hrel
      isplitr
      · ipureintro; exact Hfs
      ileft; ipureintro; exact Hop
    imodintro; iexact Htok
  · iintro HS
    imod Hclose3 with -
    imod Hclose $$ [HS HR HT Hcq Htok] with -
    · inext; iunfold wsInvG; iexists S.close, R, T; iframe HS HR HT Hreg
      isplitr
      · ipureintro; exact Hrel
      isplitr
      · ipureintro; exact Hfs
      isplitl [Hcq]
      · rw [show S.close.ws = S.ws from rfl]; iexact Hcq
      iright; iexact Htok
    imodintro; itrivial

/-! ## `Rev()`: the update for a header's revision -/

/-- **`rev_au`**: the peek as `Rev`'s update (nothing learned: no response's header revision is
constrained by `watchDn`). -/
theorem rev_au (hP : mvcc.api.persistent.law (GF := GF)) (W : SrvW GF) (wsl : Loc) :
    srvWOk W wsl wsN ⊢
    AU <{ ∃∃ (σ : mvcc.api.MvccState), mvcc.api.mvccState W.γm σ }> @ ⊤ \ ↑mvcc.api.mvccN, ∅
      <{ mvcc.api.mvccState W.γm σ, COMM True }> := by
  have := srvWOk_persistent hP W wsl wsN
  iintro #HW
  iunfold srvWOk at HW
  icases HW with ⟨-, -, #Hpk, %Hm, -⟩
  iauintro
  unfold atomic_acc
  iunfold srvPeek at Hpk
  icases Hpk with #Hpk
  imod Hpk $$ %(⊤ \ ↑mvcc.api.mvccN) %Hm.1 with ⟨%σ, Hσ, -, -, Hclose2⟩
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvcc.api.mvccN) \ ↑W.N from
    Std.LawfulSet.empty_subset)
  iintro Hclose3
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose3 with -
    imod Hclose2 $$ Hσ with -
    imodintro; iempintro
  · iintro Hσ
    imod Hclose3 with -
    imod Hclose2 $$ Hσ with -
    imodintro; itrivial

/-! ## O4: the send loop's snapshot after a receive -/

/-- **The snapshot is duplicable** (its `histLb` and `crevOk` by `srvWOk`'s laws). -/
theorem rcvSnapG_dup (hP : mvcc.api.persistent.law (GF := GF)) (W : SrvW GF) (wsl : Loc) (γreg : GName) (rs : List mvcc.api.WResp)
    (σ : mvcc.api.MvccState) (S : mvcc.api.StreamState) :
    srvWOk W wsl wsN ∗ rcvSnapG W γreg cq rs σ S ⊢ □ rcvSnapG W γreg cq rs σ S := by
  have := srvWOk_persistent hP W wsl wsN
  unfold rcvSnapG
  iintro ⟨#HW, ⟨%Hok, Hh, Hc, #Hreg⟩⟩
  iunfold srvWOk at HW
  icases HW with ⟨-, -, -, -, #Hhp, -, -, -, #Hcp⟩
  ihave #Hh := Hhp $$ Hh
  ihave #Hc := Hcp $$ Hc
  iintro !>
  iframe Hh Hc Hreg
  ipureintro; exact Hok

/-- The registry's entries of the stream's watchers, with their cancel facts (from the run's
invariant's registry, which agrees with the stream's state). -/
theorem regFacts_of (γreg : GName) (R : GMap w64 RegInfo) (S : mvcc.api.StreamState)
    (hrel : ∀ id, R !! id = (S.ws !! id).map regInfoOf) :
    iprop(□ (([∗map] id ↦ i ∈ R, regIs γreg id i) ∗
      ([∗map] id ↦ w ∈ S.ws, ⌜w.live = true⌝ ∨ cq id))) ⊢
    [∗map] id ↦ w ∈ S.ws, regIs (GF := GF) γreg id (regInfoOf w) ∗ (⌜w.live = true⌝ ∨ cq id) := by
  refine BigSepM.bigSepM_intro (fun {k v} h => ?_)
  have hR : Std.get? R k = some (regInfoOf v) := by
    show R.lookup k = _
    have := hrel k
    rw [show S.ws !! k = some v from h] at this
    exact this
  iintro #⟨H1, H2⟩
  isplit
  · iapply BigSepM.bigSepM_lookup (Φ := fun id i => regIs (GF := GF) γreg id i) hR $$ H1
  · iapply BigSepM.bigSepM_lookup (Φ := fun id w => iprop(⌜w.live = true⌝ ∨ cq id)) h $$ H2

/-- **O4, `snap_after_recv`**: holding `wsRecv ι rs` (right after a receive) and the registry
entries `M` of the ids the send loop cares about, a ghost step at `⊤` with no credit: open the
run's invariant and the server's peek (timeless), apply `wsRecv_ok.law`, close both unchanged. The
snapshot, and each id of `M` a watcher of the snapshot's `S` with that entry. -/
theorem snap_after_recv (hP : mvcc.api.persistent.law (GF := GF))
    (hok : mvcc.api.wsRecv_ok.law (GF := GF)) (W : SrvW GF) (wsl : Loc) (ws : GoInterface)
    (ι : mvcc.api.WsName) (γreg γtok γcl : GName) (rs : List mvcc.api.WResp)
    (M : GMap w64 RegInfo) :
    mvcc.api.isMvccWatchStream ws W.γm ι ∗ inv wsN (wsInvG ι γreg γtok γcl cq) ∗
      srvWOk W wsl wsN ∗ mvcc.api.wsRecv ι rs ∗ □ ([∗map] X ↦ i ∈ M, regIs γreg X i) ⊢
    |={⊤}=> mvcc.api.wsRecv ι rs ∗ ∃ (σ : mvcc.api.MvccState) (S : mvcc.api.StreamState),
      rcvSnapG W γreg cq rs σ S ∗
      ⌜∀ X i, M !! X = some i → ∃ w, S.ws !! X = some w ∧ regInfoOf w = i⌝ := by
  have : ∀ ws γ ι, Persistent (mvcc.api.isMvccWatchStream (GF := GF) ws γ ι) := hP.2.1
  have : ∀ γ σ, Timeless (mvcc.api.mvccState (GF := GF) γ σ) := hP.2.2.2.2.2.1
  have : ∀ ι S, Timeless (mvcc.api.wsState (GF := GF) ι S) := hP.2.2.2.2.2.2.1
  have := wsInvG_timeless hP ι γreg γtok γcl cq
  have := srvWOk_persistent hP W wsl wsN
  iintro ⟨#Hws, #Hinv, #HW, Hr, #HM⟩
  ihave #HW' := HW
  iunfold srvWOk at HW'
  icases HW' with ⟨-, -, #Hpk, %Hm, #Hhp, -, -, -, #Hcp⟩
  obtain ⟨-, hN2⟩ := masks_nested Hm.1 Hm.2.1 Hm.2.2
  iinv Hinv with > Hi Hclose
  iunfold wsInvG at Hi
  icases Hi with ⟨%S, %R, %T, HS, HR, HT, %Hrel, %Hfs, #Hreg, #Hcq, Hcl⟩
  iunfold srvPeek at Hpk
  icases Hpk with #Hpk
  imod Hpk $$ %(⊤ \ ↑wsN) %hN2 with ⟨%σ, Hσ, Hh, Hc, Hclose2⟩
  ihave #Hh := Hhp $$ Hh
  ihave #Hc := Hcp $$ Hc
  ihave %Hok := hok ws W.γm ι rs S σ $$ [Hr HS Hσ]
  · iframe ∗ #
  iunfold regIs at HM
  ihave %HMR := ghost_map_lookup_big M $$ HR HM
  -- the registry's entries of `S`'s watchers, with their cancel facts
  ihave #Hfacts : iprop([∗map] id ↦ w ∈ S.ws, regIs γreg id (regInfoOf w) ∗
      (⌜w.live = true⌝ ∨ cq id)) $$ []
  · iapply regFacts_of cq γreg R S (fun id => (Hrel id).1)
    iintro !>
    isplitl
    · iexact Hreg
    · iexact Hcq
  imod Hclose2 $$ Hσ with -
  imod Hclose $$ [HS HR HT Hcq Hcl] with -
  · inext; iunfold wsInvG; iexists S, R, T; iframe; iframe #; ipureintro; exact ⟨Hrel, Hfs⟩
  imodintro
  iframe Hr
  iexists σ, S
  unfold rcvSnapG
  iframe Hh Hc Hfacts
  ipureintro
  refine ⟨⟨Hok, Hfs⟩, fun X i hX => ?_⟩
  have h1 := (Hrel X).1
  rw [HMR X i hX] at h1
  cases hw : S.ws !! X with
  | none => rw [hw] at h1; simp at h1
  | some w =>
    rw [hw] at h1
    exact ⟨w, rfl, (Option.some.inj h1).symm⟩

/-! ## O5: the drain -/

/-- **The drain's poll** (O5, from `wsChan_recv.law`'s non-blocking receive): the stream's
channel, and for every poll at a stamp `k` (`wsSentLb ι k`), with the send loop's received list's
authority at `rs` framed through, the receive's arm (as the law's) or the empty arm with
`k ≤ |rs|` and the received list's lower bound at `rs`. -/
theorem drain_poll (hR : mvcc.api.wsChan_recv.law (GF := GF)) (ws : GoInterface)
    (γ : mvcc.api.MvccName) (ι : mvcc.api.WsName) :
    mvcc.api.isMvccWatchStream ws γ ι ⊢
      isChan (mvcc.api.wsChanOf ι) (mvcc.api.wsChanNames ι) WatchResponse ∗
      □ ∀ (rs : List mvcc.api.WResp) (k : Nat) (γr : GName)
          (Φ : WatchResponse → Bool → IProp GF) (Ψ : IProp GF),
        mvcc.api.wsRecv ι rs -∗ mvcc.api.wsSentLb ι k -∗ monoListAuthOwn γr 1 rs -∗
        ((∀ (v : WatchResponse) (ok : Bool),
            (if ok then ∃ r : mvcc.api.WResp, mvcc.api.wsRecv ι (rs ++ [r]) ∗ mvcc.api.wrespIs v r
             else mvcc.api.wsRecv ι rs) -∗
            monoListAuthOwn γr 1 rs -∗ Φ v ok) ∧
          (mvcc.api.wsRecv ι rs -∗ monoListAuthOwn γr 1 rs -∗ rcvLb γr rs -∗
            ⌜k ≤ rs.length⌝ -∗ Ψ)) -∗
        nonblockingRecvAuAlt (mvcc.api.wsChanNames ι) WatchResponse Φ Ψ := by
  unfold rcvLb
  iintro Hws
  icases hR ws γ ι $$ Hws with ⟨#Hch, -, #Hnb⟩
  isplitr
  · iexact Hch
  imodintro
  iintro %rs %k %γr %Φ %Ψ Hr Hk HA HK
  iapply Hnb $$ Hr Hk
  isplit
  · iintro %v %ok Hres
    icases HK with ⟨HK, -⟩
    iapply HK $$ Hres HA
  · iintro Hr %Hle
    icases HK with ⟨-, HK⟩
    ihave #Hlb := monoListLbOwn_get γr 1 rs $$ HA
    iapply HK $$ Hr HA Hlb
    ipureintro
    exact Hle

/-- **A blocking receive on the stream's channel** (`wsChan_recv.law`'s receive, as a `WP`: the
deferred drain's `range`). -/
theorem wp_ws_receive (hR : mvcc.api.wsChan_recv.law (GF := GF)) (ws : GoInterface)
    (γ : mvcc.api.MvccName) (ι : mvcc.api.WsName) (rs : List mvcc.api.WResp) :
    ⊢ ∀ Φ : val → IProp GF, mvcc.api.isMvccWatchStream ws γ ι -∗ mvcc.api.wsRecv ι rs -∗
      (∀ (v : WatchResponse) (ok : Bool),
        (if ok then ∃ r : mvcc.api.WResp, mvcc.api.wsRecv ι (rs ++ [r]) ∗ mvcc.api.wrespIs v r
         else mvcc.api.wsRecv ι rs) -∗ Φ (PairV #v #ok)) -∗
      WP (App (Val (chan.receive WatchResponse.ty)) (Val #(mvcc.api.wsChanOf ι))) {{ Φ }} := by
  iintro %Φ Hws Hr HΦ
  icases hR ws γ ι $$ Hws with ⟨#Hch, #Hb, -⟩
  iapply chan.wp_receive (mvcc.api.wsChanOf ι) (mvcc.api.wsChanNames ι) $$ Hch
  iintro -
  iapply Hb $$ Hr
  iexact HΦ

end defs

end v3rpc
end EtcdGrove
end Perennial
