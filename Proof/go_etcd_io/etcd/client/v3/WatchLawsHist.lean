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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **A watch server's store sealed the start log** (`NewStore`'s certificate of `[[], []]`, which
`isStore` keeps), and its store's names are its environment's. -/
theorem isWatchServer_start (p : Loc) (R : v3rpc.WSrv GF) :
    v3rpc.isWatchServer p R ⊢ ⌜R.γ.st = R.E.γ⌝ ∗ mvcc.idxSealed R.γ.st.idx [[], []] := by
  iintro #H
  iunfold v3rpc.isWatchServer at H
  icases H with ⟨-, -, -, -, -, -, -, -, #Hok⟩
  iunfold v3rpc.watchSrvOk at Hok
  icases Hok with ⟨#Hws, %hst, -⟩
  iunfold mvcc.isWatchableStore at Hws
  iNamed Hws
  iunfold mvcc.isStore at Hs
  iNamed Hs
  isplitr
  · ipureintro; exact hst
  iapply mvcc.idxCert_sealed $$ Hc0

/-- **The watch laws at the cluster's history** (see the file header). -/
theorem watchLaws_hist (V : WEnv GF) (γ : ServerRaftNames) (γk : KVNames) (γr : ReadNames)
    (pw : Loc) (hWM : V.WM = v3rpc.etcdModelOfHistory γ γk) (hWL : V.WL = v3rpc.histWL γ γk)
    (hm : v3rpc.memberOf γ γk γr) (hlog0 : γk.log0 = [[], []]) :
    srvKVInvs V.R.E γr ∗ v3rpc.isWatchServer pw V.R ⊢ watchLaws V := by
  obtain ⟨R, addr, ics, conn, wc, pfx, lg, WM, WL, mem, nm⟩ := V
  simp only at hWM hWL ⊢
  subst hWM hWL
  iintro ⟨#Hinvs, #Hws⟩
  ihave ⟨%hst, #H0⟩ := isWatchServer_start pw R $$ Hws
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
  · iintro !> %L #He %Hs
    ihave #Hsl := mvcc.evLog_sealed _ _ $$ He
    ihave #Hc := mvcc.evLog_certOk _ _ $$ He
    irevert Hsl Hc H0; rw [hst]; iintro #Hsl #Hc #H0
    imod v3rpc.histWL_of_sealed γ γk R.E γr hm hlog0 ⊤ (fun _ _ => CoPset.mem_full) L Hs
      $$ Hinvs H0 Hsl Hc with #Hw
    imodintro
    imodintro
    iexact Hw

end laws

end client
end EtcdGrove
end Perennial
