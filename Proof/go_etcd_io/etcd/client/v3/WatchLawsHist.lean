/-
**The watch laws of a client of the cluster** (W4c of `notes/watch-cut-plan.md`, 2026-10-22).
Lean-first, no Rocq counterpart.

`watchLaws V` at the cluster's history (`V.WM = etcdModelOfHistory γ γk`, `V.WL = histWL γ γk`,
the prefixes of history logs), at a member `V.R` whose KV invariants are at `γ` and at KV names
agreeing with `γk` (`memberOf`), the start log `[[], []]`: laws 1–3 are `histWL`'s
(`histWL_reached`, `histWL_state`, `histWL_step`); law 4 turns the member's watched log into a
history log's prefix (`histWL_of_sealed`), with the start log the member's store sealed, which its
watch server holds (`isWatchServer_start`: `isStore`'s `NewStore` certificate).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.HistoryModel

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.client.v3
open go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.server.v3.etcdserver

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The watch laws at the cluster's history** (see the file header; strict M1: a watched log is
a certified lower bound of the member's notified log, `V.W.histLb`, at the server's tie `W.histLb =
srvApi.histLb γr false E.γs`: a log of the member's history, `v3rpc.srvLog_of_histLb` with its model
facts from `srvWLaws`, so of the cluster's, `v3rpc.histWL_of_srv`; until M1 mvcc's `evLog` over
`srvKVInvs` and the watch server's sealed start log). -/
theorem watchLaws_hist (V : WEnv GF) (γ : ServerRaftNames) (γk : KVNames) (γr : ReadNames)
    (hWM : V.WM = v3rpc.etcdModelOfHistory γ γk) (hWL : V.WL = v3rpc.histWL γ γk)
    (hm : v3rpc.memberOf γ γk γr) (hH : V.W.histLb = srvApi.histLb γr false V.R.E.γs) :
    srvWLaws V.W ⊢ watchLaws V := by
  obtain ⟨R, addr, ics, conn, wc, pfx, lg, WM, WL, mem, nm, kst, W, memW⟩ := V
  simp only at hWM hWL hH ⊢
  subst hWM hWL
  iintro #Hl
  iunfold watchLaws
  simp only
  isplitr
  · iintro !> %L %r #HL %h
    iapply v3rpc.histWL_reached γ γk L r h $$ HL
  isplitr
  · iintro !> %L %r %pfx #HL %h
    imodintro
    rw [v3rpc.etcdModelOfHistory_etcdState]
    iapply v3rpc.histWL_state γ γk L r pfx h $$ HL
  isplitr
  · iintro !> %L %r0 %r1 %pfx %evs #HL %h
    rw [v3rpc.etcdModelOfHistory_EtcdStep]
    iapply v3rpc.histWL_step γ γk L r0 r1 pfx evs h $$ HL
  · iintro !> %L HL
    ihave #HL' : iprop(□ W.histLb L) $$ [HL]
    · iunfold srvWLaws at Hl
      icases Hl with ⟨#H1, -⟩
      iapply H1 $$ HL
    ihave %Hm := srvWLaws_model W L $$ [$Hl $HL']
    ihave #Hs : iprop(v3rpc.srvLog γr false L) $$ []
    · iapply v3rpc.srvLog_of_histLb γr false R.E.γs L Hm.2.1 Hm.2.2.1 Hm.2.2.2
      rw [← hH]
      iexact HL'
    imodintro
    imodintro
    iapply v3rpc.histWL_of_srv γ γk γr hm L $$ Hs

end laws

end client
end EtcdGrove
end Perennial
