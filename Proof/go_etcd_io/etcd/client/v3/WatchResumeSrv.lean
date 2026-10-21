/-
**A response's resume fact from the server's facts** (D25, `notes/decisions.md`): what `run`
proves of each response it dispatches (`resumeF`, `InvWatch.lean`): a create from just past the
response's position is a start-read one, from the released length mvcc's deliveries carry
(`mvcc.relLb`, an event's revision) or the notified log an event-less response's revision is the
last of (`mvcc.respRev`). Lean-first, no Rocq counterpart.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.WatchResume
public import Proof.go_etcd_io.etcd.client.v3.WatchContent

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.client.v3
open go_etcd_io.etcd.cache.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **An event-less response the cache's contract accepts reaches its revision** (when the
watch promises completeness): a progress notification's case says so; any other has revision
`0`. -/
theorem recvCmpl_reached (V : WEnv GF) (P : WsPrm GF) (k : Int)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel)
    (hr : r.events = [] ∧ r.created = false ∧ r.canceled = false ∧ r.compactRev = W64 0)
    (hv : v.closeErr' = GoInterface.nil ∧ v.CompactRevision' = r.compactRev ∧
      v.Canceled' = r.canceled) :
    recvCmpl V P k v r ⊢ ⌜P.γ.cpl = false⌝ ∨ etcdReached (EM := V.EM) r.hdrRev := by
  unfold recvCmpl
  iintro (%H | ⟨%h2B, %h2A, -, -, #Hok⟩)
  · ileft; ipureintro; exact H
  iright
  have hnoerr : ¬ watchErr v := by
    unfold watchErr; rw [hv.1, hv.2.1, hv.2.2, hr.2.2.2, hr.2.2.1]; simp
  iunfold watchRespOk at Hok
  icases Hok with (⟨%H, -⟩ | %H | ⟨-, -, #Hre⟩ | ⟨%H, -⟩)
  · exact absurd H.1 hnoerr
  · have hh0 : r.hdrRev = W64 0 := by
      refine Classical.byContradiction fun hn => ?_
      have hp := H.2.2.1
      simp [RespModel.isProgressNotify, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2] at hp
      exact hn hp
    rw [hh0]; iapply (etcdReached_zero (EM := V.EM))
  · iexact Hre
  · exact absurd hr.1 H.2.1

/-- **An event-less mvcc response's revision is a notified log's last** (`mvcc.respRev`, kept by
the stream's facts `mvccOk`). -/
theorem mvccOk_revLb (γs : StreamNames) (γ : mvcc.WsNames) (j : Nat) (m : v3rpc.WatchRespM)
    (ρ : mvcc.RespM) (hsrc : m.src = some ρ) (hev : ρ.evs = []) :
    v3rpc.mvccOk (GF := GF) γs γ j m ⊢
      ∃ L : mvcc.Log, mvcc.notifiedLb γ L ∗ ⌜sint.Z m.hdr.revision + 1 = (L.length : Int)⌝ := by
  iunfold v3rpc.mvccOk
  iintro ⟨%r, %rs, %L, %Hm, -, -, -, -, #Hcov, -⟩
  have hr : r = ρ := by
    have := congrArg v3rpc.WatchRespM.src Hm.1
    simp only [v3rpc.mvccResp] at this
    rw [hsrc] at this; exact (Option.some.inj this).symm
  subst hr
  iunfold v3rpc.mvccCov at Hcov
  icases Hcov with ⟨%γc, %pre, %γo, %γa, -, -, -, -, #Hrc, -⟩
  ihave #Hlb := mvcc.respCov_rev _ _ _ _ $$ Hrc
  iunfold mvcc.revLbOf at Hlb
  icases Hlb with (%H | ⟨%L', #HL', %HL'⟩)
  · exact absurd hev H
  iexists L'
  iframe HL'
  ipureintro; rw [Hm.2.1]; exact HL'

/-- **The resume fact of an event-less response** at a notified log's last revision. -/
theorem resumeF_evless (V : WEnv GF) (P : WsPrm GF) (r : RespModel) (L : mvcc.Log)
    (hr : r.events = []) (hL : sint.Z r.hdrRev + 1 = (L.length : Int)) :
    mvcc.notifiedLb V.R.γ L ∗ (⌜P.γ.cpl = false⌝ ∨ etcdReached (EM := V.EM) r.hdrRev) ⊢
      resumeF V P r := by
  iintro ⟨#HL, #Hre⟩
  unfold resumeF
  icases Hre with (%Hc | #Hre)
  · ileft; ipureintro; exact Hc
  iright
  have hp : resumePos r = r.hdrRev := by simp [resumePos, hr]
  rw [hp]
  unfold startOk mvcc.startRead
  isplitl
  · iright; iright; ileft
    iexists L
    iframe HL
    ipureintro
    have : sint.Z (r.hdrRev + W64 1) ≤ sint.Z r.hdrRev + 1 := by word
    omega
  · iright
    iapply etcdReached_mono (EM := V.EM) r.hdrRev (r.hdrRev + W64 1 - W64 1) (by word) $$ Hre

/-- **The resume fact of a response with events**, the last at a revision `j` of a delivered
log (released: `relLb`, the log's length). -/
theorem resumeF_events (V : WEnv GF) (P : WsPrm GF) (r : RespModel) (e : EvModel) (n j : Nat)
    (hlast : r.events.getLast? = some e) (he : e.rev = W64 (j : Int)) (hj : j < n)
    (hn : n < 2 ^ 63) :
    mvcc.relLb V.R.γ n ∗ etcdReached (EM := V.EM) e.rev ⊢ resumeF V P r := by
  iintro ⟨#Hn, #Hre⟩
  unfold resumeF
  iright
  have hp : resumePos r = e.rev := by simp [resumePos, hlast]
  rw [hp]
  unfold startOk mvcc.startRead
  isplitl
  · iright; iright; iright
    iexists n
    iframe Hn
    ipureintro
    rw [he]
    have : sint.Z (W64 (j : Int) + W64 1) = (j : Int) + 1 := by word
    omega
  · iright
    iapply etcdReached_mono (EM := V.EM) e.rev (e.rev + W64 1 - W64 1) (by word) $$ Hre

/-- **The resume fact of a response with events, delivered**: the events (`r.events`, made of the
mvcc events `evs`) end the watcher's delivered events of a delivered log `L` (released,
`relLb`), so the last is at a revision of it. -/
theorem resumeF_delivered (V : WEnv GF) (P : WsPrm GF) (r : RespModel) (evs : List mvcc.EvM)
    (kvs : List Loc) (pre : List mvcc.EvM) (L : mvcc.Log) (rg : mvcc.WatchRange) (lo d : Nat)
    (c c' : w64) (hes : r.events = List.zipWith evModelOf evs kvs) (hlen : kvs.length = evs.length)
    (hne : evs ≠ []) (h2 : pre ++ evs = mvcc.watchEvents L rg lo d) :
    mvcc.evLog V.R.γ.st L ∗ mvcc.relLb V.R.γ L.length ∗
      rangeWatchRespOk (EM := V.EM) V.pfx P.o P.rev c c' r ⊢ resumeF V P r := by
  iintro ⟨#HL, #Hrl, #Hok⟩
  ihave #Hs := mvcc.evLog_sealed _ _ $$ HL
  ihave %Hsp := mvcc.idxSealed_pure _ _ $$ Hs
  obtain ⟨ev, hev⟩ : ∃ ev, evs.getLast? = some ev := by
    cases h : evs.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 h) hne
    | some x => exact ⟨x, rfl⟩
  have hn : evs.length - 1 < evs.length := by
    have : evs.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
    omega
  have hev' : evs[evs.length - 1]? = some ev := by rw [← List.getLast?_eq_getElem?]; exact hev
  obtain ⟨kv, hkv⟩ : ∃ kv, kvs[evs.length - 1]? = some kv :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hrl : r.events.getLast? = some (evModelOf ev kv) := by
    rw [List.getLast?_eq_getElem?, hes, List.getElem?_zipWith]
    simp only [List.length_zipWith, hlen, Nat.min_self, hev', hkv]
    try rfl
  have hmem : ev ∈ mvcc.watchEvents L rg lo d := by
    rw [← h2]; exact List.mem_append_right _ (List.mem_of_getLast? hev)
  obtain ⟨j, -, -, hj, hm⟩ := mvcc.watchEvents_rev_ge L rg lo d ev hmem
  ihave #Hre : etcdReached (EM := V.EM) (evModelOf ev kv).rev $$ []
  · iunfold rangeWatchRespOk at Hok
    icases Hok with ⟨-, #Hevs⟩
    obtain ⟨i, hi⟩ := List.getElem?_of_mem (List.mem_of_getLast? hrl)
    ihave #He := Hevs $$ %i %(evModelOf ev kv) %hi
    iunfold rangeWatchEvOk at He
    icases He with ⟨-, #Hr, -⟩
    iexact Hr
  iapply resumeF_events V P r (evModelOf ev kv) L.length j hrl (by simp [evModelOf, hm]) hj Hsp.2.1
  iframe Hrl Hre

end lemmas

end client
end EtcdGrove
end Perennial
