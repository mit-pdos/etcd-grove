/-
**The kubernetes client's watcher over the cluster's KV** (stage E of k8s 7f-6, plan §3 step 7(iii)-(iv)).
Lean-first (no Rocq counterpart).

`clientWatchOk_of_regs`: the client `New` made over the addresses `eps` of the members `svs` (its
watch environment `watchEnvL m0 (wmemsOf svs ws) γrc wpfx`, `clusterUp`'s), each member's watch
registration at its address with its read view (`watchRegAt`, `isServerRead`), the members' names
those of one history (`memberOf`, at `γrc`), their KV names the cluster's `γk`, and the read update
`kvReadAu γk OneChange` (the instance's invariant's, `one_read_au`) give the client's watcher over
`γk` (`k8s.clientWatchOk`). Each member's watch facts are `cluster3.memberWatch`'s, its watch
condition `srvOnce` from the read update (`etcdstart.srvOnce_of_plan`: no revision changes a key
twice), so its `watchMemberFacts` (`cluster3.memberWatch_facts`); with the members' `Watch` streams,
`etcdstart.watchEnvL_conn` gives the watcher's facts at every connection to `eps`, and
`isNewClient_watcher_of` the watcher. One lemma for the `k` bridges and for `Main`'s one address.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ClusterN
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Inv
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.WatchEnv
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.OnceUpTo
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3N

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The members' registrations, the one at `i`. -/
theorem regs_lookup (svs : List (EtcdGrove.client.SrvAt GF)) (ws : List (Loc × v3rpc.WSrv GF))
    (i : Nat) (sv : EtcdGrove.client.SrvAt GF) (w : Loc × v3rpc.WSrv GF)
    (h1 : svs[i]? = some sv) (h2 : ws[i]? = some w) :
    ([∗list] sv; w ∈ svs; ws, etcdstart.watchRegAt sv.addr w.1 sv.E sv.γr w.2 ∗
      isServerRead w.1 sv.E sv.γr) ⊢
      etcdstart.watchRegAt sv.addr w.1 sv.E sv.γr w.2 ∗ isServerRead w.1 sv.E sv.γr :=
  BigSepL2.bigSepL2_lookup (Φ := fun _ sv w => iprop(etcdstart.watchRegAt sv.addr w.1 sv.E sv.γr w.2 ∗
      isServerRead w.1 sv.E sv.γr)) h1 h2

/-- **A member's watch facts** (`cluster3.memberWatch`, at the read names `γrc`): from its
registration, its read view, its names the history's and the read update of one change per
revision (its watch condition). -/
theorem memberWatch_of_reg (γrc : ReadNames) (γk : KVNames) (sv : EtcdGrove.client.SrvAt GF)
    (w : Loc × v3rpc.WSrv GF) (hm : v3rpc.memberOf γrc.raft γrc.kv sv.γr)
    (hsv : kvSame sv.γr.kv γk) (hs : kvSame γrc.kv γk) (hlog : γrc.kv.log0 = [[], []])
    (hrb : receiptBound GF ≤ 2 ^ 62) :
    etcdstart.watchRegAt sv.addr w.1 sv.E sv.γr w.2 ∗ isServerRead w.1 sv.E sv.γr ∗
      kvReadAu γk (fun σ => iprop(⌜k8s_etcd3.OneChange σ⌝)) ⊢
      cluster3.memberWatch γrc w.1 sv.E ⟨sv.γr.kv.st, sv.γr⟩ w.2 := by
  unfold k8s_etcd3.OneChange
  iintro ⟨#Hreg, #Hrd, #Hau⟩
  iunfold etcdstart.watchRegAt at Hreg
  icases Hreg with ⟨-, #Hws, #Hwl, %hR⟩
  obtain ⟨-, hE⟩ := hR
  iunfold cluster3.memberWatch
  iframe Hrd Hws Hwl
  isplitr
  · ipureintro
    exact ⟨hE, hm, kvSame_trans hsv (kvSame_symm hs)⟩
  have hlog' : sv.γr.kv.log0 = [[], []] := by rw [hm.2.2.2, hlog]
  iapply (etcdstart.srvOnce_of_plan
    (client.srvWEnv w.2 (etcdstart.srvWOf sv.E sv.γr false) sv.γr go!"" [] null null go!"" null γk)
    γk rfl (fun ch => ∀ cs ∈ ch, cs.length ≤ 1) (fun _ h cs hcs => by
      have := h cs hcs
      match cs, this with
      | [], _ => simp
      | [_], _ => simp))
  isplitr
  · iapply client.srvKVFacts_of_off
      (client.srvWEnv w.2 (etcdstart.srvWOf sv.E sv.γr false) sv.γr go!"" [] null null go!"" null γk)
      sv.γr hsv hlog' hrb (by rw [← hE]; rfl) rfl
    rw [show (client.srvWEnv w.2 (etcdstart.srvWOf sv.E sv.γr false) sv.γr go!"" [] null null go!""
      null γk).R.E = sv.E from hE]
    iapply srvKVInvs_of_read w.1 sv.E sv.γr $$ Hrd
  iexact Hau

/-- The members' addresses in the watcher's list are theirs. -/
theorem wmemsOf_addrs : ∀ (svs : List (EtcdGrove.client.SrvAt GF)) (ws : List (Loc × v3rpc.WSrv GF)),
    svs.length = ws.length → (wmemsOf svs ws).map (·.1) = svs.map EtcdGrove.client.SrvAt.addr
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | sv :: svs, w :: ws, h => by
    rw [show wmemsOf (sv :: svs) (w :: ws) =
      (sv.addr, w.2, etcdstart.srvWOf sv.E sv.γr false) :: wmemsOf svs ws from rfl,
      List.map_cons, List.map_cons, wmemsOf_addrs svs ws (by simpa using h)]

theorem wmemsOf_length (svs : List (EtcdGrove.client.SrvAt GF)) (ws : List (Loc × v3rpc.WSrv GF))
    (h : svs.length = ws.length) : (wmemsOf svs ws).length = svs.length := by
  simp [wmemsOf, List.length_zipWith, h]

theorem wmemsOf_getD (svs : List (EtcdGrove.client.SrvAt GF)) (ws : List (Loc × v3rpc.WSrv GF))
    (m0 : etcdstart.WMem GF) (i : Nat) (sv : EtcdGrove.client.SrvAt GF) (w : Loc × v3rpc.WSrv GF)
    (h1 : svs[i]? = some sv) (h2 : ws[i]? = some w) :
    (wmemsOf svs ws).getD i m0 = (sv.addr, w.2, etcdstart.srvWOf sv.E sv.γr false) := by
  simp [wmemsOf, List.getD_eq_getElem?_getD, List.getElem?_zipWith, h1, h2]

/-- The members' `Watch` streams at their addresses, from their registrations. -/
theorem streams_of_regs : ∀ (svs : List (EtcdGrove.client.SrvAt GF)) (ws : List (Loc × v3rpc.WSrv GF)),
    ([∗list] sv; w ∈ svs; ws, etcdstart.watchRegAt sv.addr w.1 sv.E sv.γr w.2 ∗
      isServerRead w.1 sv.E sv.γr) ⊢
      [∗list] m ∈ wmemsOf svs ws, isGrpcStreamMd (Req := v3rpc.pbWatchRequest)
        (Rep := v3rpc.pbWatchResponse) m.1 go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp m.2.1)
        (fun md => v3rpc.watchSpec m.2.1 m.2.2 (auth.mdTokenOf md))
  | [], _ => by
    simp only [wmemsOf, List.zipWith_nil_left]
    iintro -
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | _ :: _, [] => by
    simp only [wmemsOf, List.zipWith_nil_right]
    iintro -
    iapply BigSepL.bigSepL_nil.2
    itrivial
  | sv :: svs, w :: ws => by
    iintro H
    ihave ⟨⟨Hr, -⟩, H⟩ := BigSepL2.bigSepL2_cons.1 $$ H
    rw [show wmemsOf (sv :: svs) (w :: ws) =
      (sv.addr, w.2, etcdstart.srvWOf sv.E sv.γr false) :: wmemsOf svs ws from rfl]
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hr]
    · iunfold etcdstart.watchRegAt at Hr
      icases Hr with ⟨Hs, -⟩
      iexact Hs
    · iapply streams_of_regs svs ws $$ H

/-- **The client's watcher over the cluster's KV** (see the file header). -/
theorem clientWatchOk_of_regs [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (cl : Loc) (V : EtcdGrove.client.WEnv GF) (svs : List (EtcdGrove.client.SrvAt GF))
    (ws : List (Loc × v3rpc.WSrv GF)) (γrc : ReadNames) (m0 : etcdstart.WMem GF) (γk : KVNames)
    (hV : V = etcdstart.watchEnvL m0 (wmemsOf svs ws) γrc wpfx)
    (hnd : (svs.map EtcdGrove.client.SrvAt.addr).Nodup) (hne : svs ≠ [])
    (hm : ∀ sv ∈ svs, v3rpc.memberOf γrc.raft γrc.kv sv.γr) (hsv : ∀ sv ∈ svs, kvSame sv.γr.kv γk)
    (hs : kvSame γrc.kv γk) (hlog : γrc.kv.log0 = [[], []]) (hrb : receiptBound GF ≤ 2 ^ 62) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb ∗
      isPkgInit (PROP := IProp GF) pkg_id.context ∗ client.eofOk ∗
      isNewClient cl (svs.map EtcdGrove.client.SrvAt.addr) V ∗
      ([∗list] sv; w ∈ svs; ws, etcdstart.watchRegAt sv.addr w.1 sv.E sv.γr w.2 ∗
        isServerRead w.1 sv.E sv.γr) ∗
      kvReadAu γk (fun σ => iprop(⌜k8s_etcd3.OneChange σ⌝)) ⊢
      k8s.clientWatchOk cl γk := by
  subst hV
  iintro ⟨#P1, #P2, #P3, #Heo, #Hnc, #Hregs, #Hau⟩
  ihave %hlen := BigSepL2.bigSepL2_length $$ Hregs
  have haddr := wmemsOf_addrs svs ws hlen
  have hmlen := wmemsOf_length svs ws hlen
  have hne' : wmemsOf svs ws ≠ [] := by
    intro h; apply hne; rw [← List.length_eq_zero_iff, ← hmlen, h]; rfl
  ihave #Hs := streams_of_regs svs ws $$ Hregs
  ihave #Hm : □ ∀ i : Nat, ⌜i < (wmemsOf svs ws).length⌝ -∗
      client.watchMemberFacts ((etcdstart.watchEnvL m0 (wmemsOf svs ws) γrc wpfx).atIdx i) $$ []
  · imodintro
    iintro %i %hi
    rw [hmlen] at hi
    have h1 : svs[i]? = some svs[i] := List.getElem?_eq_getElem hi
    have h2 : ws[i]? = some ws[i] := List.getElem?_eq_getElem (by omega)
    have hmem : svs[i] ∈ svs := List.getElem_mem hi
    ihave #Hr := regs_lookup svs ws i svs[i] ws[i] h1 h2 $$ Hregs
    ihave #Hr' := Hr
    iunfold etcdstart.watchRegAt at Hr'
    icases Hr' with ⟨⟨-, -, -, %hR⟩, -⟩
    icases Hr with ⟨#Hreg, #Hrd⟩
    ihave #Hmw := memberWatch_of_reg γrc γk svs[i] ws[i] (hm _ hmem) (hsv _ hmem) hs hlog hrb
      $$ [Hreg Hrd Hau]
    · iframe #
    have hg := wmemsOf_getD svs ws m0 i svs[i] ws[i] h1 h2
    have hRi : ((etcdstart.watchEnvL m0 (wmemsOf svs ws) γrc wpfx).atIdx i).R = ws[i].2 := by
      simp only [client.WEnv.atIdx, etcdstart.watchEnvL]; rw [hg]
    have hW : ((etcdstart.watchEnvL m0 (wmemsOf svs ws) γrc wpfx).atIdx i).W =
        etcdstart.srvWOf ((etcdstart.watchEnvL m0 (wmemsOf svs ws) γrc wpfx).atIdx i).R.E
          (⟨svs[i].γr.kv.st, svs[i].γr⟩ : ReqNames).rd false := by
      rw [hRi, hR.2]
      simp only [client.WEnv.atIdx, etcdstart.watchEnvL]; rw [hg]
    iapply (cluster3.memberWatch_facts _ γrc ws[i].1 svs[i].E ⟨svs[i].γr.kv.st, svs[i].γr⟩ rfl rfl
      (kvSame_refl _) hW hlog hrb)
    rw [hRi]
    iexact Hmw
  ihave #Hconn := etcdstart.watchEnvL_conn wp_ErrAny hAs m0 (wmemsOf svs ws) γrc wpfx (by decide)
    hne' (by rw [haddr]; exact hnd) $$ [P1 P2 P3 Heo Hs Hm]
  · iframe #
  rw [haddr] at *
  ihave ⟨%w, %conn, %wc, %lg, %ics, #HWf, #Hcw⟩ := isNewClient_watcher_of cl _ _ $$ [Hnc Hconn]
  · iframe #
  iunfold k8s.clientWatchOk
  iexists w, _
  iframe #
  ipureintro
  exact hs.1

end proof

end k8s_etcd3N
end EtcdGrove
end Perennial
