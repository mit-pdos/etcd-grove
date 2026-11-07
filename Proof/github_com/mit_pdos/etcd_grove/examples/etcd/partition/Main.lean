/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/partition/Main.lean` (the partition plan's
S3b, 2026-10-20). Lean-first (no Rocq counterpart).

linkv3's `Main` (`Proof/.../linkv3/Main.lean`) at linkv3p's configuration, with every member
served: the logger; the cluster (`startCluster`, since W4 of
`notes/watch-cut-plan.md` (2026-10-22) its own function, until then inline here: `clusterUp`, its
clients at a watch environment `Main` never uses); the partitioner forked on the schedule (every
member's `srvNetMember`, every bridge owned and not blackholed); the instance's invariant at the
cluster's start store (linkvtxn's `linkvInv_alloc_boot`, at the first member's names, the others'
by `linkvInv_congr`), so each client has linkvtxn's `Apply.spec`'s premises (`clientOk`: the three
members at their bridges' addresses, each member's registrations through `cluster3.isGrpcRpc_forwards`);
`Check(clis, clients, ops, 0)`, which returns `Ok` (`timeout = 0`), so the panic on `Illegal` is
not taken. A failed start ends `Main` with `Unknown`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.partition.startCluster
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Alloc
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Partitioner
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Check
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Boot
public import Spec.go_uber_org.zap.NewNop

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_partition

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver
open etcd_putget3 (httpURL commonPremises)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.partition.Assumptions]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_startCluster : startCluster.spec (GF := GF) (hG := hG))
    (wp_partitioner : cluster3.Partitioner.spec (GF := GF) (hG := hG))
    (wp_Check : Check.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC N id₁ id₂ id₃ ps ctxs boot clients ops sched steps Hbf Htb Hrb48 HrbN HwbN Hck Haf Hbuq
    Hrf Hdbo Hms hAs H0 H31 Hops Hmul
  wp_start as ⟨Hstart, #Hsched, Htok, #Hprem⟩
  -- `context`'s `closedchan`, from its package's facts
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  -- the imports' package facts
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_NewNop as %lg #Hlgz
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hlgz
  (try wp_auto)
  -- the cluster, its clients' watch environment unused
  wp_apply (wp_startCluster N id₁ id₂ id₃ ps ctxs boot lg [] Hbf
      Htb Hrb48 HrbN HwbN Hck Haf Hbuq Hrf Hdbo Hms)
    $$ [Hstart Htok] as %srvs %brs %clis %ok Hup
  · iframe; iframe #
  icases Hup with (%Hok | ⟨%Hok, Htok, Hup⟩)
  · subst Hok
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hok
  wp_auto
  iunfold clusterUp at Hup
  icases Hup with ⟨%γ, %γn, %ρ₁, %ρ₂, %ρ₃, %E₁', %E₂', %E₃', %cid₁, %cid₂, %cid₃, %mid₁, %mid₂,
    %mid₃, %R₁, %R₂, %R₃, %s₁, %s₂, %s₃, %cl₁, %cl₂, %cl₃, %br₁, %br₂, %br₃, Hcl, #Hclis,
    #Hnc₁, #Hnc₂, #Hnc₃⟩
  iunfold cluster3.clusterAt at Hcl
  icases Hcl with ⟨#Hsrvs, #Hbrs, #Hm₁, #Hm₂, #Hm₃, Hctl₁, Hctl₂, Hctl₃, Hob₁, Hob₂, Hob₃, Hetcd,
    %Hal⟩
  obtain ⟨hst₂, hst₃, -, -⟩ := Hal
  isimp only [cluster3.memberAt_none] at Hm₁ Hm₂ Hm₃
  icases Hm₁ with ⟨#Hfw₁, -, #HPut₁, #HRange₁, #HDel₁, #HTxn₁, #HCmp₁, %Hnr₁, -, -, -, %Hp₁⟩
  icases Hm₂ with ⟨#Hfw₂, -, #HPut₂, #HRange₂, #HDel₂, #HTxn₂, #HCmp₂, %Hnr₂, -, -, -, -⟩
  icases Hm₃ with ⟨#Hfw₃, -, #HPut₃, #HRange₃, #HDel₃, #HTxn₃, #HCmp₃, %Hnr₃, -, -, -, -⟩
  obtain ⟨-, -, -, hlog₁, -⟩ := Hp₁
  -- `go cluster3.Partitioner(srvs, brs, sched)`: every member's place in the network
  ihave Hmem : ([∗list] s ∈ [s₁, s₂, s₃], ∃ id : w64, etcdstart.srvPeerCtl γn s id) $$ [Hctl₁ Hctl₂ Hctl₃]
  · iapply (BigSepL.bigSepL_cons
      (Φ := fun _ s => iprop(∃ id : w64, etcdstart.srvPeerCtl (GF := GF) γn s id))).2
    isplitl [Hctl₁]
    · iexists id₁; iexact Hctl₁
    iapply (BigSepL.bigSepL_cons
      (Φ := fun _ s => iprop(∃ id : w64, etcdstart.srvPeerCtl (GF := GF) γn s id))).2
    isplitl [Hctl₂]
    · iexists id₂; iexact Hctl₂
    iapply (BigSepL.bigSepL_cons
      (Φ := fun _ s => iprop(∃ id : w64, etcdstart.srvPeerCtl (GF := GF) γn s id))).2
    isplitl [Hctl₃]
    · iexists id₃; iexact Hctl₃
    iapply BigSepL.bigSepL_nil.2
    itrivial
  -- every bridge owned, not blackholed
  ihave Hobs : ([∗list] br ∈ [br₁, br₂, br₃], ∃ addr : GoString, bridge.ownBridge br addr false)
    $$ [Hob₁ Hob₂ Hob₃]
  · iapply (BigSepL.bigSepL_cons
      (Φ := fun _ br => iprop(∃ addr : GoString, bridge.ownBridge (GF := GF) br addr false))).2
    isplitl [Hob₁]
    · iexists clientAddr₁; iexact Hob₁
    iapply (BigSepL.bigSepL_cons
      (Φ := fun _ br => iprop(∃ addr : GoString, bridge.ownBridge (GF := GF) br addr false))).2
    isplitl [Hob₂]
    · iexists clientAddr₂; iexact Hob₂
    iapply (BigSepL.bigSepL_cons
      (Φ := fun _ br => iprop(∃ addr : GoString, bridge.ownBridge (GF := GF) br addr false))).2
    isplitl [Hob₃]
    · iexists clientAddr₃; iexact Hob₃
    iapply BigSepL.bigSepL_nil.2
    itrivial
  wp_apply wp_fork $$ [Hobs Hmem]
  · wp_apply (wp_partitioner inferInstance γn _ _ sched [s₁, s₂, s₃] [br₁, br₂, br₃] steps) $$ [Hobs Hmem]
    all_goals (try (iframe #))
    all_goals (try iframe)
    ipureintro; exact isPanic_intoVal ()
  (try wp_auto)
  -- the instance's invariant, at the cluster's start store (empty), for every member's names
  imod (etcd_txnlin.linkvInv_alloc_boot ρ₁.rd.kv hlog₁ (fun _ _ => True) ps
      (LogEntry.toEntries boot 0) (srvBootLogOk_of_BootLog _ _ _ Hbf.boot) ⊤) $$ Hetcd
    with ⟨%γl, #Hlinv, Hst⟩
  ihave #Hlinv₂ : etcd_txnlin.linkvInv γl ρ₂.rd.kv $$ []
  · rw [linkvInv_congr γl ρ₂.rd.kv ρ₁.rd.kv hst₂.1]; iexact Hlinv
  ihave #Hlinv₃ : etcd_txnlin.linkvInv γl ρ₃.rd.kv $$ []
  · rw [linkvInv_congr γl ρ₃.rd.kv ρ₁.rd.kv hst₃.1]; iexact Hlinv
  -- every client's members: the three, at their bridges' addresses
  let ms : List (EtcdGrove.client.SrvAt GF) :=
    [⟨bridgeAddr₁, E₁', ρ₁.rd, cid₁, mid₁⟩, ⟨bridgeAddr₂, E₂', ρ₂.rd, cid₂, mid₂⟩,
      ⟨bridgeAddr₃, E₃', ρ₃.rd, cid₃, mid₃⟩]
  have hms : ms.map EtcdGrove.client.SrvAt.addr = [bridgeAddr₁, bridgeAddr₂, bridgeAddr₃] := rfl
  ihave #Hregs : ([∗list] sv ∈ ms, EtcdGrove.client.kvRegsAt sv) $$ []
  · iapply BigSepL.bigSepL_cons.2
    isplitr
    · iunfold EtcdGrove.client.kvRegsAt
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₁ HPut₁]; iframe #
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₁ HRange₁]; iframe #
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₁ HDel₁]; iframe #
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₁ HTxn₁]; iframe #
      iapply cluster3.isGrpcRpc_forwards $$ [Hfw₁ HCmp₁]; iframe #
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iunfold EtcdGrove.client.kvRegsAt
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₂ HPut₂]; iframe #
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₂ HRange₂]; iframe #
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₂ HDel₂]; iframe #
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₂ HTxn₂]; iframe #
      iapply cluster3.isGrpcRpc_forwards $$ [Hfw₂ HCmp₂]; iframe #
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iunfold EtcdGrove.client.kvRegsAt
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₃ HPut₃]; iframe #
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₃ HRange₃]; iframe #
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₃ HDel₃]; iframe #
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₃ HTxn₃]; iframe #
      iapply cluster3.isGrpcRpc_forwards $$ [Hfw₃ HCmp₃]; iframe #
    iapply BigSepL.bigSepL_nil.2
    itrivial
  ihave #Hinvs : ([∗list] sv ∈ ms, etcd_txnlin.linkvInv γl sv.γr.kv) $$ []
  · iapply BigSepL.bigSepL_cons.2
    iframe Hlinv
    iapply BigSepL.bigSepL_cons.2
    iframe Hlinv₂
    iapply BigSepL.bigSepL_cons.2
    iframe Hlinv₃
    iapply BigSepL.bigSepL_nil.2
    itrivial
  -- (D29) the bridges' addresses are refusal-free, as their members' are: every client's writes
  -- are sent at most once, whatever its retry bound
  ihave %Hb₁ : ⌜noRefusalAt bridgeAddr₁⌝ $$ []
  · iunfold cluster3.forwards at Hfw₁; icases Hfw₁ with ⟨-, %Hf, -⟩; ipureintro; exact Hf Hnr₁
  ihave %Hb₂ : ⌜noRefusalAt bridgeAddr₂⌝ $$ []
  · iunfold cluster3.forwards at Hfw₂; icases Hfw₂ with ⟨-, %Hf, -⟩; ipureintro; exact Hf Hnr₂
  ihave %Hb₃ : ⌜noRefusalAt bridgeAddr₃⌝ $$ []
  · iunfold cluster3.forwards at Hfw₃; icases Hfw₃ with ⟨-, %Hf, -⟩; ipureintro; exact Hf Hnr₃
  have hnr : ∀ a ∈ [bridgeAddr₁, bridgeAddr₂, bridgeAddr₃], noRefusalAt a := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact Hb₁
    · exact Hb₂
    · exact Hb₃
  ihave #Hwo₁ : EtcdGrove.client.clientWriteOnce (GF := GF) cl₁
      [bridgeAddr₁, bridgeAddr₂, bridgeAddr₃] $$ []
  · iunfold EtcdGrove.client.clientWriteOnce; ipureintro; exact hnr
  ihave #Hwo₂ : EtcdGrove.client.clientWriteOnce (GF := GF) cl₂
      [bridgeAddr₁, bridgeAddr₂, bridgeAddr₃] $$ []
  · iunfold EtcdGrove.client.clientWriteOnce; ipureintro; exact hnr
  ihave #Hwo₃ : EtcdGrove.client.clientWriteOnce (GF := GF) cl₃
      [bridgeAddr₁, bridgeAddr₂, bridgeAddr₃] $$ []
  · iunfold EtcdGrove.client.clientWriteOnce; ipureintro; exact hnr
  ihave #Hok : ([∗list] cl ∈ [cl₁, cl₂, cl₃], clientOk γl cl) $$ []
  · iapply (BigSepL.bigSepL_cons (Φ := fun _ cl => clientOk (GF := GF) γl cl)).2
    isplitr
    · iunfold clientOk
      iexists ms, cluster3.watchEnv clusterCfg R₁ R₂ R₃ ρ₁.rd []
      rw [hms]
      iframe #
      ipureintro; simp [ms]
    iapply (BigSepL.bigSepL_cons (Φ := fun _ cl => clientOk (GF := GF) γl cl)).2
    isplitr
    · iunfold clientOk
      iexists ms, cluster3.watchEnv clusterCfg R₁ R₂ R₃ ρ₁.rd []
      rw [hms]
      iframe #
      ipureintro; simp [ms]
    iapply (BigSepL.bigSepL_cons (Φ := fun _ cl => clientOk (GF := GF) γl cl)).2
    isplitr
    · iunfold clientOk
      iexists ms, cluster3.watchEnv clusterCfg R₁ R₂ R₃ ρ₁.rd []
      rw [hms]
      iframe #
      ipureintro; simp [ms]
    iapply BigSepL.bigSepL_nil.2
    itrivial
  -- `Check(clis, clients, ops, 0)`
  wp_apply (wp_Check γl _ [cl₁, cl₂, cl₃] clients ops (W64 0) hAs (by omega) (by simp) H0 H31 Hops
      Hmul) $$ [Hst] as %r %Hr
  · iframe; iframe #
  obtain ⟨-, Hok⟩ := Hr
  have Hok : r = go!"Ok" := Hok (by decide)
  subst Hok
  wp_auto
  iapply HΦ; ipureintro; left; rfl

end proof

end etcd_partition
end EtcdGrove
end Perennial
