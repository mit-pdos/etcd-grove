/-
**A watcher's environment at a list of members** (k8s 7f-6 E, 2026-11-17; cluster3's
`WatchEnv.lean` for any number of members). Lean-first (no Rocq counterpart).

`watchEnvL m0 ms γr pfx`: the members `ms` (each its address, watch server and server watch facts,
in order; `m0` the value read past the end), the watch contract at the cluster's committed history
(`etcdModelOfHistory`, at the read names `γr`), the KV names `γr.kv`. `watchEnvL_conn`: the members'
`Watch` streams at their addresses and each member's facts (`watchMemberFacts`) give the watcher's
facts at every connection to the addresses (`watchConnFacts_of_members`), what
`isNewClient_watcher_of` takes; the addresses distinct.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.HistoryModel

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- A member of a watcher's environment: its address, watch server and server watch facts. -/
abbrev WMem (GF : BundledGFunctors) := GoString × v3rpc.WSrv GF × v3rpc.SrvW GF

/-- **The watcher's environment at the members `ms`** (see the file header). -/
def watchEnvL (m0 : WMem GF) (ms : List (WMem GF)) (γr : ReadNames) (pfx : GoString) :
    client.WEnv GF :=
  ⟨(ms.getD 0 m0).2.1, (ms.getD 0 m0).1, [], null, null, pfx, null,
    v3rpc.etcdModelOfHistory γr.raft γr.kv, v3rpc.histWL γr.raft γr.kv,
    fun i => ((ms.getD i m0).1, (ms.getD i m0).2.1), ms.length, γr.kv, (ms.getD 0 m0).2.2,
    fun i => (ms.getD i m0).2.2⟩

theorem watchEnvL_addrs (m0 : WMem GF) (ms : List (WMem GF)) (γr : ReadNames) (pfx : GoString) :
    (watchEnvL m0 ms γr pfx).addrs = ms.map (·.1) := by
  unfold client.WEnv.addrs watchEnvL
  apply List.ext_getElem
  · simp
  · intro i _ h2; simp [List.getElem?_eq_getElem (by simpa using h2)]

theorem getD_of_lt {α : Type} {l : List α} {d : α} {i : Nat} (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- With distinct addresses, the member at member `i`'s address is `i`. -/
theorem watchEnvL_idxOf (m0 : WMem GF) (ms : List (WMem GF)) (γr : ReadNames) (pfx : GoString)
    (hnd : (ms.map (·.1)).Nodup) (i : Nat) (hi : i < ms.length) :
    (watchEnvL m0 ms γr pfx).idxOf (ms.getD i m0).1 = i := by
  unfold client.WEnv.idxOf
  have hfind : (List.range (watchEnvL m0 ms γr pfx).nm).find?
      (fun j => decide (((watchEnvL m0 ms γr pfx).mem j).1 = (ms.getD i m0).1)) = some i := by
    rw [List.find?_range_eq_some]
    refine ⟨by simp [watchEnvL], by simpa [watchEnvL] using hi, fun j hj => ?_⟩
    simp only [watchEnvL, Bool.not_eq_eq_eq_not, Bool.not_true]
    apply decide_eq_false
    intro he
    have hj' : j < ms.length := by omega
    rw [getD_of_lt hj', getD_of_lt hi] at he
    have h1 : (ms.map (·.1))[j]'(by simpa using hj') = (ms.map (·.1))[i]'(by simpa using hi) := by
      simpa using he
    have := (List.Nodup.getElem_inj hnd).1 h1
    omega
  rw [hfind]; rfl

/-- The registrations of a list, one by one, are `isGrpcStreamsMd`'s. -/
theorem isGrpcStreamsMd_of_big {Req Rep : StreamMsg GF} (name : GoString)
    (Up : GoString → Nat → Req.M → IProp GF) (Spec : GoString → GrpcMd → StreamSpec Rep) :
    ∀ l : List GoString, ([∗list] a ∈ l, isGrpcStreamMd a name (Up a) (Spec a)) ⊢
      isGrpcStreamsMd l name Up Spec
  | [] => by iintro _; simp only [isGrpcStreamsMd]; itrivial
  | [a] => by
    iintro H
    ihave ⟨H, -⟩ := BigSepL.bigSepL_cons.1 $$ H
    simp only [isGrpcStreamsMd]; iexact H
  | a :: b :: rest => by
    iintro H
    ihave ⟨Ha, H⟩ := BigSepL.bigSepL_cons.1 $$ H
    simp only [isGrpcStreamsMd]
    iframe Ha
    iapply (isGrpcStreamsMd_of_big name Up Spec (b :: rest)) $$ H

/-- **The watcher's facts at every connection to the members' addresses** (see the file header). -/
theorem watchEnvL_conn [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (m0 : WMem GF) (ms : List (WMem GF)) (γr : ReadNames) (pfx : GoString) (hp : pfx ≠ [])
    (hne : ms ≠ []) (hnd : (ms.map (·.1)).Nodup) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ client.eofOk ∗
      (□ [∗list] m ∈ ms, isGrpcStreamMd (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse)
        m.1 go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp m.2.1)
        (fun md => v3rpc.watchSpec m.2.1 m.2.2 (auth.mdTokenOf md))) ∗
      (□ ∀ i : Nat, ⌜i < ms.length⌝ -∗ client.watchMemberFacts ((watchEnvL m0 ms γr pfx).atIdx i)) ⊢
      □ ∀ (conn : Loc) (ics : List GoFunc),
        etcdWatchConn (GF := GF) conn (ms.map (·.1)) ics -∗
          client.watchConnFacts { watchEnvL m0 ms γr pfx with conn := conn, ics := ics } := by
  iintro ⟨#P1, #P2, #P3, #Heof, #Hs, #Hm⟩
  iintro !> %conn %ics #Hc
  iapply watchConnFacts_of_members wp_ErrAny hAs (watchEnvL m0 ms γr pfx) conn ics
  rw [watchEnvL_addrs]
  iframe #
  isplitr
  · iapply (isGrpcStreamsMd_of_big (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse)
      go!"/etcdserverpb.Watch/Watch")
    rw [BigSepL.bigSepL_map]
    iapply (BigSepL.bigSepL_impl (PROP := IProp GF)) $$ Hs
    iintro !> %i %m %hm H
    have hi : i < ms.length := (List.getElem?_eq_some_iff.1 hm).1
    have hm' : ms.getD i m0 = m := by
      rw [getD_of_lt hi]; exact (List.getElem?_eq_some_iff.1 hm).2
    have hidx := watchEnvL_idxOf m0 ms γr pfx hnd i hi
    rw [hm'] at hidx
    simp only [client.WEnv.memOf, client.WEnv.memWOf]
    rw [hidx]
    simp only [watchEnvL]
    rw [hm']
    iexact H
  isplitr
  · imodintro
    iintro %i %hi'
    iapply Hm
    ipureintro; exact hi'
  ipureintro
  refine ⟨hp, hnd, 0, ?_, rfl, rfl⟩
  show 0 < ms.length
  cases ms with
  | nil => exact absurd rfl hne
  | cons _ _ => simp

end defs

end etcdstart
end EtcdGrove
end Perennial
