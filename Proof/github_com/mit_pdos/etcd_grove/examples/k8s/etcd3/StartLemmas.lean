/-
**The k-member start's lemmas** (moved out of `startCluster.lean`, the k8s etcd3 driver's
`startCluster.wp_proof`, unchanged but `memberPres_of`'s compaction mode, 2026-11-20,
`notes/k8s-compactor-n-plan.md`: the compactor driver's k-member `startCluster` uses them too, and a
proof does not import a proof). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ClusterN
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AllocN
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Defs

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3N

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver etcdstart

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem startOf_peers (ms : List GMember) : (startOf ms).map (·.2.1) = ms.map (·.Peer') := by
  simp [startOf, Function.comp_def]

/-- **Every member's client address's listen right, out of its fresh bundle** (each member's
`memberFreshRes_client`). -/
theorem freshRes_split (ms : List GMember) (γn : NetNames GF) :
    ([∗list] m ∈ startOf ms, memberFreshRes (GF := GF) m.1 ⟨some m.2.1, m.2.2⟩ γn) ⊢
      ([∗list] m ∈ ms, netAddrFree (GF := GF) m.Client') ∗
        [∗list] m ∈ ms, memberFreshRes m.Name' ⟨some m.Peer', none⟩ γn := by
  unfold startOf
  rw [BigSepL.bigSepL_map]
  refine (BigSepL.bigSepL_mono fun {_ m} _ =>
    memberFreshRes_client (GF := GF) m.Name' ⟨some m.Peer', some m.Client'⟩ γn m.Client' rfl).trans ?_
  exact BigSepL.bigSepL_sep_eqv.1

/-- **Each member with its ghost names and its premises** (putgetN's `memberPres_of`), in the
compaction mode `cmp` (`false` but for the compactor's cluster). -/
theorem memberPres_of (N : Nat) (tok : GoString) (ms0 : List GMember) (ps : List w64)
    (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF) (lm : lease.Mode)
    (ms : List GMember) (gs : List (MemberG GF)) (ids : List w64)
    (hids : gs.map (·.id) = ids) (hlen : ms.length = gs.length) (cmp : Bool := false) :
    ⊢ ([∗list] m; id ∈ ms; ids,
        etcdstart.bootPremise N ps bootLog ctxs dir tok m.Name' (urlsN ms0 m) id) -∗
      (□ ∀ lid : w64, netHttpOk γn lid) -∗
      ([∗list] g ∈ gs, memberBoot g.γ ctxs g.ρ g.E Φs g.id cmp lm) -∗
      ([∗list] m ∈ ms, memberFreshRes m.Name' ⟨some m.Peer', none⟩ γn) -∗
      [∗list] x ∈ ms.zip gs, memberPre N tok ms0 ps bootLog ctxs dir Φs γn lm x cmp := by
  induction ms generalizing gs ids with
  | nil =>
    iintro _ _ _ _
    simp only [List.zip_nil_left]
    iempintro
  | cons m ms ih =>
    cases gs with
    | nil => simp at hlen
    | cons g gs =>
      subst hids
      simp only [List.map_cons]
      iintro Hbp #Hnet Hb Hf
      ihave Hbp := BigSepL2.bigSepL2_cons.1 $$ Hbp
      ihave Hb := BigSepL.bigSepL_cons.1 $$ Hb
      ihave Hf := BigSepL.bigSepL_cons.1 $$ Hf
      icases Hbp with ⟨Hbp1, Hbp⟩
      icases Hb with ⟨Hb1, Hb⟩
      icases Hf with ⟨Hf1, Hf⟩
      rw [List.zip_cons_cons]
      iapply BigSepL.bigSepL_cons.2
      isplitl [Hbp1 Hb1 Hf1]
      · iunfold memberPre
        iframe
        iapply Hnet
      iapply (ih gs (gs.map (·.id)) rfl (by simpa using hlen)) $$ Hbp Hnet Hb Hf

/-- A member's raft read names are its boot names' (`memberBoot`'s first fact). -/
theorem memberBoot_raft (γ : SrvRaft) (ctxs : List (List w8)) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (id : w64) (cmp : Bool) (m : lease.Mode) :
    memberBoot γ ctxs ρ E₀ Φs id cmp m ⊢
      ⌜ρ.rd.raft = ⟨γ, [], W64 0⟩⌝ ∗ memberBoot γ ctxs ρ E₀ Φs id cmp m := by
  unfold memberBoot
  iintro ⟨%h, H⟩
  isplitr
  · ipureintro; exact h.1
  iframe H
  ipureintro; exact h

/-- **Every member's raft read names are its boot names'** (`memberBoot_raft` over the list). -/
theorem memberBoots_raft (ctxs : List (List w8)) (Φs : w64 → w64 → List w8 → GName → IProp GF)
    (cmp : Bool) (m : lease.Mode) :
    ∀ gs : List (MemberG GF), ([∗list] g ∈ gs, memberBoot g.γ ctxs g.ρ g.E Φs g.id cmp m) ⊢
      ⌜∀ g ∈ gs, g.ρ.rd.raft = ⟨g.γ, [], W64 0⟩⌝ ∗
        [∗list] g ∈ gs, memberBoot g.γ ctxs g.ρ g.E Φs g.id cmp m
  | [] => by
    iintro H
    isplitr
    · ipureintro; simp
    iexact H
  | g :: gs => by
    iintro H
    ihave ⟨Hg, H⟩ := BigSepL.bigSepL_cons.1 $$ H
    ihave ⟨%h, Hg⟩ := memberBoot_raft g.γ ctxs g.ρ g.E Φs g.id cmp m $$ Hg
    ihave ⟨%hs, H⟩ := memberBoots_raft ctxs Φs cmp m gs $$ H
    isplitr
    · ipureintro
      intro g' hg'
      rcases List.mem_cons.1 hg' with rfl | hg'
      · exact h
      · exact hs g' hg'
    iapply BigSepL.bigSepL_cons.2
    iframe

/-- **Two members of one cluster are of one history** (`memberOf`): their raft read names are
their boot names', which are the cluster's but the storage registry (`memberGOk`). -/
theorem memberOf_of_gOk (γ : SrvRaft) (γk : KVNames) (g g0 : MemberG GF)
    (h : memberGOk γ γk g) (h0 : memberGOk γ γk g0)
    (hr : g.ρ.rd.raft = ⟨g.γ, [], W64 0⟩) (hr0 : g0.ρ.rd.raft = ⟨g0.γ, [], W64 0⟩) :
    v3rpc.memberOf g0.ρ.rd.raft g0.ρ.rd.kv g.ρ.rd := by
  obtain ⟨⟨r, hg⟩, -, hc, hch, hlog, -⟩ := h
  obtain ⟨⟨r0, hg0⟩, -, hc0, hch0, hlog0, -⟩ := h0
  refine ⟨?_, by rw [hc, hc0], by rw [hch, hch0], by rw [hlog, hlog0]⟩
  rw [hr, hr0, hg, hg0]

/-! (Phase 7's switch, SW1, 2026-11-24) `watchRegAt_forwards` and `kvRegs_forwards` are gone with
`cluster3.forwards`: a bridge serves what its member serves at the member's table
(`etcdstart.tableAt`, `cluster3.StartBridge`). -/

end lemmas

end k8s_etcd3N
end EtcdGrove
end Perennial
