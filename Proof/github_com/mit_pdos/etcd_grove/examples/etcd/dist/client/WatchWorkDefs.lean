/- Lean-first (no Rocq counterpart).

# The watch workload across machines: its vocabulary (#50 N10a, `notes/etcd-dist-plan.md` §24)

`RunWatch` (`examples/etcd/dist/client/watch.go`) is the single-process watch workload
(`partition.MainWatch`, `Proof/.../partition/MainWatch.lean`) with its watcher on the orchestrator and
its writers on client machines of their own. The argument is the single-process one, over the
cluster's KV `Γ.kv` instead of the members' server facts:

* **The adapter at the cluster's KV.** The orchestrator's share holds the cluster's client half
  `etcdKV Γ.kv σ₀` at the boot state (changes `[[]]`: revision `1`, nothing written), whole: the watch
  workload is its deployment's sole writer (`needsSoleWriter`, plan §23.4). After `GenAll` picks the
  writers' Puts `trs`, it allocates the clients' adapter (`client.kmInv_alloc`) with the plan's
  property `etcd_partition.wkW (trs.map pairOf)` (every revision from `2` one Put of the plan): the
  invariant is persistent, so the orchestrator hands it to every writer with its Puts.
* **The watcher** (`kvWatcherW w γk`): the triple of `Watch_dist` at the client's `*watcher` `w` and
  the KV `γk`, without the client facts (`kvWatcherW_of_dist`, from `watchClientAt` and the interim
  contract `Watch_dist` taken as a hypothesis). `isEtcdWatcher_of_kmW` is `client.isEtcdWatcher_of_km`
  over it (the same proof: the read update after the floor the caller knows, `km_read_au`, and each
  response the cache's etcd response at the adapter's model, `etcdWatchElem_of_km`), so that the
  single-process `Collect` plan (`etcdstart.wp_Collect_plan`, each response by
  `etcd_partition.resp_km`) applies unchanged. The single-process bridge is the same statement over
  `isKvWatcher` and the linked `watcher.wp_Watch` (`KMWatch.lean`, a linking module); both rest on
  `KMWatchDefs.lean`'s `etcdWatchElem_of_km`. (Not a corollary of this one: the single-process post
  is at the environment's KV names `V.kv` with the auth row in its elements.)
* **The writers.** Each Put of the plan has the adapter's write update after the start's changes
  (`km_put_au0`: `client.km_write_au` at `[[]]`, the plan's property kept, `wkW_put`), and a
  successful Put's reply gives `etcdstart.okFactKM` (`okFactKM_of_write`), which is
  `etcd_partition.okFactK` (`okFactK_of_KM`: the same definition), the fact the check reads.
* `wsInvT w OkF γt γn`: the writer machine's log's lock invariant, the log with its length at `γn`, or,
  after the call has read the log out of it, the token `γt` (`writerOp` returns the log it read under the lock, so it
  keeps the slice: the lock gets the token in its place).
* `checkOkK_of`: `Check`'s premise from what `Collect` returns and the Puts' facts
  (`partition/MainWatch.lean`'s, copied: that file is a proof module).
* `watchShare WS addrs ns`: the orchestrator's share (global, at `GooseGlobalGS`): a view `Γ` with auth off,
  every endpoint serving a member of it, the cluster's client half at a state with no change after the
  boot's, and the writer machines' share `WS Γ ns` (the remote writer service at their addresses:
  `remoteWriters.specWith`'s, plan §24).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.WatchDist
public import Proof.go_etcd_io.etcd.client.v3.KMWatchDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WatchWkKV
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WritesKM
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WritesF
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.CollectPlan
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.RespChan
public import Perennial.Ghost.Token

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3
  go_etcd_io.etcd.server.v3.etcdserver mvcc
open etcd_dist etcdstart

section pure
variable [GooseExts]

/-- **`RunWatch`'s options make a prefix watch of `wk/` from revision `1` that does not panic**
(`cache`'s `watchEvents_opts` at `wk/`; that lemma is in a proof module). -/
theorem wk_watch_opts :
    (opWatchModel etcd_partition.wkPfx [withPrefixM, withRevM (W64 1), withProgressNotifyM,
        withCreatedNotifyM]).isPrefixWatch etcd_partition.wkPfx (W64 1) = true ∧
      ¬ opWatchPanics etcd_partition.wkPfx [withPrefixM, withRevM (W64 1), withProgressNotifyM,
        withCreatedNotifyM] := by
  have h : etcd_partition.wkPfx ≠ [] := by decide
  simp [opWatchModel, opWatchPanics, OpFull.watchPanics, op_simps, OpFull.isPrefixWatch, h]

/-- The watch's keys, `GenAll`'s, are under the prefix `wk/`. -/
theorem wk_genKeys_pfx (trs : List wkv) (h : ∀ p ∈ trs, GenKv etcd_partition.genKeys p) :
    ∀ kv ∈ trs.map pairOf, etcd_partition.wkPfx <+: kv.1 := by
  intro kv hkv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hkv
  have hk := (h p hp).1
  simp only [pairOf]
  simp only [etcd_partition.genKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with h | h | h <;> rw [h] <;> decide

end pure

section watcher
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A watcher of the KV `γk`** (persistent; see the file header): `Watch_dist`'s triple at the
`*watcher` `w` and `γk`, the client facts and the packages' initializations dropped. -/
def kvWatcherW (w : Loc) (γk : KVNames) : IProp GF :=
  iprop(□ ∀ (ctx : GoInterfaceOk) (ctx_desc : context.ContextDesc (IProp GF)) (om : GrpcMd)
      (key : GoString) (opts_sl : GoSlice) (opts : List (OpFull → OpFull)) (rev : w64)
      (Q : KVState → IProp GF),
    {{ EtcdGrove.context.watchCtx ctx ctx_desc ∗ metadata.outMD ctx om ∗ optsAt opts_sl opts ∗
        ⌜(opWatchModel key opts).isRangeWatchP rev = true ∧ ¬ opWatchPanics key opts ∧
          1 ≤ sint.Z rev ∧ watchSizeOk (opWatchModel key opts)⌝ ∗
        □ (AU <{ ∃∃ (σ : KVState), etcdKV γk σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
          <{ etcdKV γk σ ∗ ⌜kvRoom σ⌝, COMM □ Q σ }>) }}
      (App (App (App (Val (w @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty @!!
          go!"Watch")) (Val #(GoInterface.ok ctx))) (Val #key)) (Val #opts_sl))
    {{ (ch : Loc) (γw : EtcdWatchNames), RET #ch;
        isSpsc γw.spsc ch (watchStateElemP γk γw (opWatchModel key opts).watchNorm Q iprop(True))
          (fun _ => iprop(True)) ∗
        spscConsumer γw.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
        monoListIdxOwn γw.cur 0 (rev - W64 1) }})

instance kvWatcherW_persistent (w : Loc) (γk : KVNames) :
    Persistent (kvWatcherW (GF := GF) w γk) := by
  unfold kvWatcherW; infer_instance

/-- **A watch client of the view watches the cluster's KV**, by the interim contract `Watch_dist`
(a hypothesis). -/
theorem kvWatcherW_of_dist (wp_Watch : Watch_dist.spec (GF := GF) (hG := hG)) [π : NetProtoGS]
    (cl w : Loc) (eps : List GoString) (V : WEnv GF) (Γ : DistView) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ watchClientAt cl w eps V Γ ⊢
    kvWatcherW w Γ.kv := by
  iintro ⟨#P1, #P2, #P3, #Hc⟩
  unfold kvWatcherW
  iintro !> %ctx %cd %om %key %sl %opts %rev %Q
  iintro !> %Φ ⟨#Hctx, #Hom, #Hopts, %Hp, #Hau⟩ HΦ
  iapply (wp_Watch cl w eps V Γ ctx cd om key sl opts rev Q) $$ [] [HΦ]
  · iframe #
    ipureintro; exact Hp
  iexact HΦ

/-- **A watcher of the adapter's KV meets the cache's watcher contract** at the adapter's model
(`client.isEtcdWatcher_of_km` over `kvWatcherW`; see the file header). -/
theorem isEtcdWatcher_of_kmW (w : Loc) (γ : KMNames) (pfx : GoString) (hp : pfx ≠ []) :
    kvWatcherW (GF := GF) w γ.kv ∗ kmInv γ ⊢
    isEtcdWatcher (EM := etcdModelOfKV γ) (watcherIfaceOf w) pfx := by
  iintro ⟨#Hw, #Hinv⟩
  unfold isEtcdWatcher
  iintro !> %ctx %cs %key %sl %gs %rev %Φ !> ⟨#Hctx, #HctxO, #Hopts, %Hpre, #Hrd⟩ HΦ
  obtain ⟨hpw, hnp, hrev, hsz⟩ := Hpre
  unfold OpFull.isPrefixWatch at hpw
  simp only [decide_eq_true_eq, hp, if_false] at hpw
  obtain ⟨ht, hr, -, -, hpk, hfr, hfp, hfd, hkey, hend⟩ := hpw
  ihave #Hreach := etcdRead_reached (EM := etcdModelOfKV γ) (rev - W64 1) $$ Hrd
  imod km_reached_lb γ (rev - W64 1) $$ Hreach with ⟨%l0, #Hl0, -⟩
  ihave #Hau := km_read_au γ l0 $$ [$Hinv $Hl0]
  ihave #HctxO' := HctxO
  iunfold metadata.outgoingCtxOkC at HctxO'
  icases HctxO' with ⟨%om, #Hom⟩
  iunfold kvWatcherW at Hw
  ihave #HW := Hw $$ %ctx %cs %om %key %sl %gs %rev %(kmSeenQ γ l0)
  iapply HW $$ [] [HΦ]
  · isplitr
    · iapply EtcdGrove.context.watchCtx_of_isContext; isplitl [] <;> iassumption
    iframe #
    isplitr
    · ipureintro
      refine ⟨?_, hnp, by omega, ?_⟩
      · refine OpFull.isRangeWatchP_of ?_
        unfold OpFull.isRangeWatch; simp only [decide_eq_true_eq]
        exact ⟨ht, hr, hpk, hfr, hfp, hfd⟩
      · exact hsz
    iunfold kvReadAu at Hau
    iunfold kvAu at Hau
    iexact Hau
  inext
  rw [OpFull.watchNorm_of_ne _ (by rw [hkey]; exact hp)]
  iintro %ch %γw ⟨#Hs, Hc, Hi⟩
  iapply HΦ
  isplitr
  · unfold isEtcdWatchChan
    iexists watchStateElemP _ γw (opWatchModel key gs) (kmSeenQ γ l0) _
    iframe Hs
    iintro !> %i %v H
    ihave H := watchStateElemP_elem _ γw (opWatchModel key gs) (kmSeenQ γ l0) _ i v $$ H
    imodintro
    iapply etcdWatchElem_of_km γ l0 pfx hp (opWatchModel key gs) rev hkey hend hr _ γw _ i v
      $$ [Hreach H]
    iframe Hreach H
  unfold etcdWatchConsumer
  iexists []
  iframe Hc Hi
  ipureintro; rfl

end watcher

section writes
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The writer machine's log's lock invariant** (`Writer_dist`'s): the log with its records' facts and
its length in the ghost variable `γn` (half; `Writer` holds the other half while it runs, so its caller
learns a bound on the log), or, once the call's owner of the token `γt` has taken the log out
(`writerOp` returns the log it read after the lock), only the field and the token. `Writer` holds the
token while it runs, so it always finds the log. -/
def wsInvT (w : Loc) (OkF : wrec → IProp GF) (γt γn : GName) : IProp GF :=
  iprop((∃ (sl : GoSlice) (oks : List wrec),
      structFieldRef github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writes go!"Ok" w ↦ sl ∗
      sl ↦* oks ∗ ownSliceCap wrec sl (DFrac.own 1) ∗ (□ [∗list] p ∈ oks, OkF p) ∗
      ghostVar γn (1 : Qp).half oks.length) ∨
    ∃ sl : GoSlice,
      structFieldRef github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Writes go!"Ok" w ↦ sl ∗
      token γt)

/-- **A writer's update for the put of `k ↦ v` of the plan**, after the start's changes `[[]]`
(`etcd_partition.km_put_au` at the start's lower bound: what `okFactKM_of_write` reads). -/
theorem km_put_au0 (γ : KMNames) (P : List (GoString × GoString))
    (hW : γ.W = etcd_partition.wkW P) (k v : GoString) (hkv : (k, v) ∈ P) :
    kmInv (GF := GF) γ ∗ monoListLbOwn γ.ch ([[]] : List (List Change)) ⊢
      kvOpAu1 γ.kv (.put (putKeyOp k v)) (kmWriteQ γ [[]] (.put (putKeyOp k v))) :=
  km_write_au γ [[]] _ (fun σ h => by
    rw [hW] at h ⊢; exact etcd_partition.wkW_put P k v hkv σ h)

/-- **A logged Put's fact at the client's model is the check's** (`okFactKM` and `okFactK` are one
definition). -/
theorem okFactK_of_KM (γ : KMNames) (p : wrec) :
    okFactKM (GF := GF) γ p ⊢ etcd_partition.okFactK γ p := by
  unfold okFactKM etcd_partition.okFactK kmRevAt etcd_partition.revAtK
  exact .rfl

/-- **The check's premise** (`CheckOk`; `partition/MainWatch.lean`'s `checkOkK_of`, copied): each
successful put's revision is a watched event's, whose key and value are the put's. -/
theorem checkOkK_of (γ : KMNames) (trs : List wkv) (upTo : w64) (evs : List wev)
    (oks : List wrec) (hup : ∀ p ∈ oks, sint.Z p.Rev' ≤ sint.Z upTo) :
    etcdstart.collectOk (GF := GF) (etcd_partition.revAtK γ) (trs.map pairOf) upTo evs ∗
        □ ([∗list] p ∈ oks, etcd_partition.okFactK γ p) ⊢
      ⌜CheckOk evs trs oks⌝ := by
  iintro ⟨Hco, #Hoks⟩
  icases etcdstart.collectOk_elim $$ Hco with ⟨%Hc, #Hrevs⟩
  obtain ⟨hup0, hlen, hevs⟩ := Hc
  ihave %H : ⌜∀ p, p ∈ oks → 2 ≤ sint.Z p.Rev' ∧ ∃ e, evs[(sint.Z p.Rev' - 2).toNat]? = some e ∧
      e.Key' = p.Key' ∧ e.Val' = p.Val'⌝ $$ []
  · iapply BI.pure_forall.2
    iintro %p
    by_cases hp : p ∈ oks
    · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hp
      ihave Hf := BigSepL.bigSepL_lookup
        (Φ := fun _ p => etcd_partition.okFactK (GF := GF) γ p) hk $$ Hoks
      iunfold etcd_partition.okFactK at Hf
      icases Hf with ⟨%h2, #Hra⟩
      have hle := hup p hp
      have hlt : (sint.Z p.Rev' - 2).toNat < evs.length := by
        rcases hup0 with h0 | h0
        · rw [h0] at hle; simp at hle; omega
        · omega
      obtain ⟨e, he⟩ : ∃ e, evs[(sint.Z p.Rev' - 2).toNat]? = some e :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      have hidx : 2 + (sint.Z p.Rev' - 2).toNat = (sint.Z p.Rev').toNat := by omega
      ihave #He : etcd_partition.revAtK γ (sint.Z p.Rev').toNat e.Key' e.Val' $$ []
      · rw [← hidx]; iapply Hrevs; ipureintro; exact he
      ihave %Hag := etcd_partition.revAtK_agree γ (sint.Z p.Rev').toNat e.Key' e.Val' p.Key' p.Val'
        $$ [He Hra]
      · iframe #
      ipureintro; intro _; exact ⟨h2, e, he, Hag.1, Hag.2⟩
    · ipureintro; intro h; exact absurd h hp
  ipureintro
  exact ⟨hlen, hevs, H⟩

end writes

/-! ## The orchestrator's share (global) -/

section shares
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- **The watch workload's orchestrator share** at the endpoints `addrs` and the writer machines
`ns` (see the file header): a view `Γ` of the cluster with auth off (stage B′: the client's KV calls need
etcd's KV entries, which the table has for an auth-off view), every endpoint serving a member of it, the
cluster's client half at a state with no change after the boot's, and the writer machines' share
`WS Γ ns`. -/
def watchShare (WS : DistView → List GoString → IProp GF) (addrs ns : List GoString) : IProp GF :=
  iprop(∃ (Γ : DistView) (σ₀ : KVState), ⌜σ₀.changes = [[]]⌝ ∗ ⌜Γ.auth = false⌝ ∗ membersAt addrs Γ ∗
    etcdKV Γ.kv σ₀ ∗ WS Γ ns)

end shares

end etcd_dist_client
end EtcdGrove
end Perennial

end
