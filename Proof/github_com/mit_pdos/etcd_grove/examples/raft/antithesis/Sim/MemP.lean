/-
Lean-first (no Rocq counterpart).

# Parity B2: `mem`, `-parallel` (`antSim_memP_in`, #33 parity B2, Sim round 17)

A `-parallel` leader's reported `Ready`, with no write queued and no split write in progress: after
`GC` (`ldCtxD_of`), `Mem` (B 450-459) with `InMemory`'s result for the `Ready`'s kind (a win, a
proposal, a commit: `memOk_win`, `memOk_prop`, `memOk_cmt`), its write queued (every leader kind
writes: a win and a proposal append, a commit moves the commit), the relation after it
(`mem_relD`) from the node's part (`memNode_lead`, the kind-dependent premises from `MemKinds` and
`MemLead`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MemLead
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.MemEval

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap go_etcd_io.raft.v3 AntCheck

section memP
variable [GooseExts]

variable {R : RunCfg} {dec : CCDec} {V : Fin R.N → NodeView} {net : List Msg}
  {xnet : List XMsg} {G : RaftFacts} {n : Fin R.N} {r₁ : RState} {rd : ReadyD}

/-- **The `mem` step** from `InMemory`'s result `r` and its `MemOk`, and the node part's
kind-dependent premises. -/
theorem memP_step {msk : SimMask} (hmsk : msk ≤ mskB2) {Adm : List EntryM → CCState → Prop}
    {S S1 : State} {evs : List Event}
    (hin : InMask msk R net xnet) (hp : Prefix R.cfg evs S) (hgc : gcLoop (gcFuel S) S = .ok (S1, none))
    (hs1 : AntSimD R dec S1 V net xnet) (hgo1 : GlobalOk R S1 net G) (hl : RaftLaws G)
    (hx : LdCtx R.syncOff dec V net xnet G n r₁ rd S1)
    (ha : R.md.async = false) (hpar : R.drv.parallel = true)
    (hm : (V n).mems = []) (hpar0 : (V n).parts = []) (htold : Told (V n))
    (hr : ReachIn msk R dec Adm net xnet n (V n) r₁) (hrl : rd.role = .leader) {r : MemResult}
    (hev : S1.inMemory n.val (evReady (nodeId n) (V n).byE (roleStr rd.pre rd.role) rd.term rd.vote
      rd.commit rd.ents) = .ok r)
    (hok1 : r.ok = true) (hok : MemOk R dec S1 V G n r (uint.Z rd.commit))
    (hlog : (V n).ps.log <+: r₁.p.log) (hec : rd.ents = [] ∨ rd.commit = (V n).dur.commit)
    (hpfx : (V n).delivered ++ rd.ce <+: (V n).dur.log) (hlt : LogTermsLe r₁.p)
    (hLP : ∀ (it : QItem) (i : Int), LeaderPartD (memQ S1 r n.val it i) n
      (memView (V n) r₁ rd (rd.msgs.filter isReqM ++ rd.msgs.filter (fun q => !isReqM q))))
    (hMC : ∀ (it : QItem) (i : Int), MemCommitOk (memQ S1 r n.val it i)
      (memView (V n) r₁ rd (rd.msgs.filter isReqM ++ rd.msgs.filter (fun q => !isReqM q)))) :
    SimStepD R dec evs G
      (evMem (nodeId n) (V n).byE (roleStr rd.pre rd.role) rd.term rd.vote rd.commit rd.ents none true)
      (setV V n (memView (V n) r₁ rd (rd.msgs.filter isReqM ++ rd.msgs.filter (fun q => !isReqM q))))
      net xnet := by
  have hc : S1.cfg = R.cfg := hs1.1.1
  have hrl1 : r₁.p.role = .leader := hx.hro.1.symm.trans hrl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ht15, -, hx17, -⟩ := hs1.2.2.2.2 n
  have hit : (⟨evMem (nodeId n) (V n).byE (roleStr rd.pre rd.role) rd.term rd.vote rd.commit rd.ents
      none true, if (V n).byE == go!"recv" then S1.pending[n.val]! else []⟩ : QItem) =
      MemRec.item (nodeId n) (rd.memRec (V n)) := by
    have h := memItem_eq (S := S1) (rd := rd) htold ht15 hx17
    rw [hx.hsn] at h; exact h
  have hstep : S1.step (evMem (nodeId n) (V n).byE (roleStr rd.pre rd.role) rd.term rd.vote rd.commit
      rd.ents none true) =
      .ok (some (memQ S1 r n.val (MemRec.item (nodeId n) (rd.memRec (V n))) (S1.i + 1))) := by
    rw [step_evMem n hc, mem_of _ _ _ _ _ _ _ _ _ hev hok1, ← hit]; rfl
  have hnode := memNode_lead hmsk hin hs1 hok hx ha hpar hm hpar0 htold hr hrl hlog hec hpfx
    (memLead_term hx hrl1) hlt (hLP _ (S1.i + 1)) (memLead_qs hx hrl1 hpar0) (hMC _ (S1.i + 1))
  obtain ⟨hrel, hgo2⟩ := mem_relD hs1 hgo1 hok (by rw [← hit]; rfl) ha hnode
  have hv2 : (memQ S1 r n.val (MemRec.item (nodeId n) (rd.memRec (V n))) (S1.i + 1)).viol = [] := by
    show r.viol = []; rw [hok.hviol]; exact hs1.2.1.1.1
  exact ⟨_, Prefix.snoc hp hgc hstep (violated_nil hv2 hl hgo2), hrel, hgo2⟩

/-- **`mem`, `-parallel`** (B 450-459; `antSim_memP_in.stmt`): a leader's reported sync `Ready`, with
no write queued and no split write in progress, is a `Mem` step keeping the relation; it writes
(`w = true`: every leader kind does). -/
theorem antSim_memP_in : antSim_memP_in.stmt := by
  intro msk hmsk R dec S V net xnet evs G n r₁ rd w Adm hin hpre ha hbat hpar hr hro hrl hsn hrep hw
    htold hrf htb hm hpar0
  obtain ⟨S1, hgc, hs1, hgo1, hx⟩ := ldCtxD_of hmsk hin hpre ha hbat hm hpar0 hr hro hrep htold hrf htb
  have hrl1 : r₁.p.role = .leader := hro.1.symm.trans hrl
  have hpre0 : rd.pre = false := by
    cases h : rd.pre
    · rfl
    · have := hx.hpre h; rw [hrl1] at this; cases this
  have hro' := hro
  obtain ⟨-, -, hT, hVt, hC, -⟩ := hro'
  have hrs : roleStr rd.pre rd.role = roleOf .leader := by rw [hpre0, hrl]; rfl
  have hA := afterOk_loc (SimMask.b1Of_le hmsk) hin.syncOff hx.hnet (nodeOk_liftC hx.hq0 hx.hv)
    hr.syncOff hro
  have hnormF : EntsNormal r₁.full := (hA.facts.conf0 hx.hcc).2.1
  have hfD : NodeFactsD R n (V n) := (hs1.2.2.2.2 n).2.2.2.2.2.2.2.1
  have hlt0 : LogTermsLe (V n).ps := hfD.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcl0 := LdCtx.commit_le hx
  have hdc : (V n).dur.commit = (V n).ps.commit := by rw [hx.hdn]; rfl
  have hev_of : ∀ {r : MemResult}, S1.inMemory n.val (evReady (nodeId n) (V n).byE (roleOf .leader)
      r₁.p.term r₁.p.vote r₁.p.commit rd.ents) = .ok r →
      S1.inMemory n.val (evReady (nodeId n) (V n).byE (roleStr rd.pre rd.role) rd.term rd.vote
        rd.commit rd.ents) = .ok r := fun h => by rw [hrs, hT, hVt, hC]; exact h
  have hfin : Writes (V n) rd → (∀ {r : MemResult},
      S1.inMemory n.val (evReady (nodeId n) (V n).byE (roleStr rd.pre rd.role) rd.term rd.vote
        rd.commit rd.ents) = .ok r → r.ok = true → MemOk R dec S1 V G n r (uint.Z rd.commit) →
      (V n).ps.log <+: r₁.p.log → (rd.ents = [] ∨ rd.commit = (V n).dur.commit) →
      (V n).delivered ++ rd.ce <+: (V n).dur.log → LogTermsLe r₁.p →
      (∀ (it : QItem) (i : Int), LeaderPartD (memQ S1 r n.val it i) n
        (memView (V n) r₁ rd (rd.msgs.filter isReqM ++ rd.msgs.filter (fun q => !isReqM q)))) →
      (∀ (it : QItem) (i : Int), MemCommitOk (memQ S1 r n.val it i)
        (memView (V n) r₁ rd (rd.msgs.filter isReqM ++ rd.msgs.filter (fun q => !isReqM q)))) →
      SimStepD R dec evs G
        (evMem (nodeId n) (V n).byE (roleStr rd.pre rd.role) rd.term rd.vote rd.commit rd.ents none w)
        (setV V n { ((V n).drainOf r₁ rd) with
          pend := rd.msgs.filter isReqM ++ rd.msgs.filter (fun q => !isReqM q),
          mems := if w then (V n).mems ++ [rd.memRec (V n)] else (V n).mems }) net xnet) := by
    intro hwr r hev hok1 hok hlog hec hpfx hlt hLP hMC
    obtain rfl : w = true := hw.mpr hwr
    rw [if_pos rfl, hm, List.nil_append]
    exact memP_step hmsk hin hpre.1 hgc hs1 hgo1 hpre.2.2.1 hx ha hpar hm hpar0 htold hr hrl hev hok1 hok
      hlog hec hpfx hlt hLP hMC
  have hk := hx.hk
  cases hk with
  | camp _ _ hr' => cases hrl1.symm.trans hr'
  | grant _ _ _ _ _ _ _ hr' => cases hrl1.symm.trans hr'
  | adopt _ _ _ _ _ hr' => cases hrl1.symm.trans hr'
  | follow hr' => cases hrl1.symm.trans hr'
  | store _ _ _ _ _ hr' => cases hrl1.symm.trans hr'
  | hb _ _ _ _ _ hr' => cases hrl1.symm.trans hr'
  | adoptX _ _ _ _ _ _ _ _ hr' => cases hrl1.symm.trans hr'
  | win src rej mt hvc hsrc hq hlm hL hents hpc =>
    obtain ⟨r, hev, hok1, hok, hrll, hplog, hmo, hct, hT0, hpt⟩ :=
      memOk_win hs1 hx hnormF src rej mt hvc hsrc hq hlm hL hents hpc
    have hok' : MemOk R dec S1 V G n r (uint.Z rd.commit) := by rw [hC]; exact hok
    have hlog : (V n).ps.log <+: r₁.p.log := ⟨_, hplog.symm⟩
    refine hfin (.inr (.inr (.inr (.inl (by rw [hents]; exact List.cons_ne_nil _ _))))) (hev_of hev) hok1
      hok' hlog (.inr (by rw [hC, hpc, hdc])) (memLead_pfx hx hlog (by rw [hpc]; exact hcl0)) ?_
      (fun it i => memLead_lpWin hs1 hok' hx hvc hrll hplog hmo hct hT0 hpt)
      (fun it i => memLead_mcKeep hs1 hok' hx hrl1 hpar0 hlog hpc)
    intro e he
    rw [hplog] at he
    rcases List.mem_append.mp he with he | he
    · rw [hpt]; exact hlt0 e he
    · rw [List.mem_singleton.mp he, hpt]; exact Int.le_refl _
  | prop es hby hvl hne hents hplog hpl hpt hpv hpc =>
    have hnorm : ∀ x ∈ rd.ents, x.Type' = W32 0 := fun x hxe =>
      hnormF x (by rw [hx.hfl, hplog]; exact List.mem_append_right _ hxe)
    obtain ⟨r, hev, hok1, hok, hrll, hmt⟩ :=
      memOk_prop hs1 hx hnorm es hby hvl hne hents hplog hpl hpt hpv hpc
    have hok' : MemOk R dec S1 V G n r (uint.Z rd.commit) := by rw [hC]; exact hok
    have hlog : (V n).ps.log <+: r₁.p.log := ⟨_, hplog.symm⟩
    have hEne : rd.ents ≠ [] := by
      rw [hents]; intro h; exact hne (List.mapIdx_eq_nil_iff.mp h)
    refine hfin (.inr (.inr (.inr (.inl hEne)))) (hev_of hev) hok1
      hok' hlog (.inr (by rw [hC, hpc, hdc])) (memLead_pfx hx hlog (by rw [hpc]; exact hcl0)) ?_
      (fun it i => memLead_lpProp hs1 hok' hx hvl hrll hmt hplog hpt)
      (fun it i => memLead_mcKeep hs1 hok' hx hrl1 hpar0 hlog hpc)
    intro e he
    rw [hplog] at he
    rcases List.mem_append.mp he with he | he
    · rw [hpt]; exact hlt0 e he
    · rw [hents] at he
      obtain ⟨j, hj, rfl⟩ := List.mem_mapIdx.mp he
      rw [hpt]; exact Int.le_refl _
  | cmt hvl hpl hpt hpv hplog hents hlt hcm hns =>
    obtain ⟨r, hev, hok1, hok, hlead, hrll, hc1, hc2, hc3⟩ :=
      memOk_cmt hs1 hx hvl hpl hpt hpv hplog hents hlt hcm hns
    have hok' : MemOk R dec S1 V G n r (uint.Z rd.commit) := by rw [hC]; exact hok
    have hcL : uint.Z r₁.p.commit ≤ (V n).ps.log.length := by
      have := nat_commit_le hx.hrf; rw [hx.hfl, hplog] at this; exact this
    have hwr : Writes (V n) rd := .inr (.inr (.inl fun h => by
      rw [hC, hdc] at h; rw [h] at hlt; exact Int.lt_irrefl _ hlt))
    rw [← hents] at hev
    refine hfin hwr (hev_of hev) hok1 hok' ⟨[], by rw [hplog, List.append_nil]⟩ (.inl hents)
      (memLead_pfx hx ⟨[], by rw [hplog, List.append_nil]⟩ hcL)
      (fun e he => by rw [hpt]; rw [hplog] at he; exact hlt0 e he)
      (fun it i => memLead_lpCmt hs1 hx ha hbat hm hpar0 hvl hpl hpt hplog hlead hrll)
      (fun it i => memCommitOk_of hc1
        (by
          show r.chain.take (uint.Z r₁.p.commit).toNat = (logOf r₁.full).take (uint.Z r₁.p.commit).toNat
          rw [hx.hfl]; exact hc2) (.inr hc3))

end memP

end AntSim
end EtcdGrove
end Perennial
