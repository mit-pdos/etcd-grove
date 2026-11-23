/-
`Inv = Inv0 ∧ InvAux` for the finished steps: `Inv0` by the earlier proofs, `InvAux` at the start
directly and under the frame steps, `lose`, `bcast`, `execSCC`, `execBump` by `aux_congr`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.AuxFrame
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Exec
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Bcast
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.PMBcast

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace AuxProof

theorem peer_init (r : Nat) (hr : r < nR) :
    ((RState.init r).peerOrder.take (nR - 1)).Nodup ∧
      ∀ p ∈ (RState.init r).peerOrder.take (nR - 1), p < nR ∧ p ≠ r := by
  simp only [nR] at hr
  have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> decide

theorem aux_init : InvAux Sys.init := by
  have hev : ∀ r e, ¬ Sys.init.ev r e := InitProof.ev_init
  have hmsgs : ∀ fr to, Sys.init.msgs fr to = [] := InitProof.msgs_init
  have hinst : ∀ r x w, ¬ (Sys.init.rep r).inst x = some w := by
    intro r x w h; simp [Sys.init, RState.init] at h
  have hcnt : ∀ fr to p, Sys.init.cnt fr to p = 0 := by
    intro fr to p; simp [Sys.cnt, hmsgs]
  have hcrt : ∀ q, zz ((Sys.init.rep q).crtInstance q) = -1 := by
    intro q; simp only [Sys.init, RState.init, zz]; decide
  have hi : ∀ (P : InstRec → Prop) r x w, (Sys.init.rep r).inst x = some w → P w :=
    fun P r x w h => absurd h (hinst _ _ _)
  refine ⟨fun r _ x w h => absurd h (hinst _ _ _), fun r _ x w h => absurd h (hinst _ _ _),
    fun r _ x w h => absurd h (hinst _ _ _), fun r _ x w h => absurd h (hinst _ _ _), fun r _ x w h => absurd h (hinst _ _ _),
    fun r _ x w h => absurd h (hinst _ _ _), fun r _ x w h => absurd h (hinst _ _ _), fun r _ x w h => absurd h (hinst _ _ _),
    fun r x b v _ h => absurd h (hev _ _), fun r x v h => absurd h (hev _ _),
    fun r x b _ h => absurd h (hev _ _), fun r _ x w lb h => absurd h (hinst _ _ _),
    fun r hr => peer_init r hr, ?_, fun r _ x w h => absurd h (hinst _ _ _),
    fun fr to m x hm => by simp [hmsgs] at hm, fun r e x he => absurd he (hev _ _), ?_,
    fun r _ x w lb h => absurd h (hinst _ _ _), fun r _ x w lb h => absurd h (hinst _ _ _),
    fun r _ x w lb h => absurd h (hinst _ _ _), fun fr to x b => by rw [hcnt]; omega,
    fun fr to x b => by rw [hcnt]; omega, fun r x b st v _ h => absurd h (hev _ _),
    fun a r x b h => by rw [hcnt] at h; omega, fun a r m hm => by simp [hmsgs] at hm,
    fun a r x b h => by rw [hcnt] at h; omega, fun fr to m hm => by simp [hmsgs] at hm,
    fun r to m h => absurd h (hev _ _), fun r _ e x cx he => absurd he (hev _ _),
    fun r _ q _ => by simp only [Sys.init, RState.init, zz]; decide,
    fun r _ e x cx he => absurd he (hev _ _),
    fun r x b st v _ h => absurd h (hev _ _),
    fun r x b v h => by rcases h with h | h <;> exact absurd h (hev _ _),
    ⟨fun fr to m hm => by simp [hmsgs] at hm, fun r _ x w cs h => absurd h (hinst _ _ _),
      fun r _ x w lb cs h => absurd h (hinst _ _ _), fun fr to m hm => by simp [hmsgs] at hm,
      fun r m h => absurd h (hev _ _), fun r x b v h => by rcases h with h | h <;> exact absurd h (hev _ _)⟩,
    fun fr to m hm => by simp [hmsgs] at hm, fun r m h => absurd h (hev _ _),
    fun r m h => absurd h (hev _ _),
    { arOk := fun a r m hm => by simp [hmsgs] at hm
      commitProp := fun r x c u h => absurd h (hev _ _)
      commitMsgProp := fun fr to m hm => by simp [hmsgs] at hm
      lbProp := fun r _ x w lb h => absurd h (hinst _ _ _)
      parCom := fun a r m hm => by simp [hmsgs] at hm
      parSt := fun a r m hm => by simp [hmsgs] at hm
      paFresh := fun r _ x w lb h => absurd h (hinst _ _ _)
      paCmds := fun r _ x w lb h => absurd h (hinst _ _ _)
      paSent := fun x w lb _ h => absurd h (hinst _ _ _)
      pendPA := fun r b h => by simp [Sys.init] at h
      paVoteMsg := fun r x st v _ _ h => absurd h (hev _ _)
      parNoPA := fun a r m hm => by simp [hmsgs] at hm
      aeF := fun r _ x w lb h => absurd h (hinst _ _ _)
      repLead := fun r m e h => absurd h.1 (hev _ _)
      paGe := fun r x b st v l v0 _ h => absurd h (hev _ _)
      phAttrs := fun l x b v0 h => absurd h (hev _ _)
      accWit := fun r x b v h => absurd h (hev _ _)
      accVote := fun r x b v h => absurd h (hev _ _)
      cmdSafe := fun l x n v h => absurd h (hev _ _)
      accSup := fun r x c v h => absurd h (hev _ _) },
    fun x ps h => by simp [Sys.init] at h, fun r _ q _ => by
      simp only [Sys.init, RState.init, zz]; decide, ExecOrd.invExec_init⟩
  · intro r _ q _; exact Int.le_refl _
  · intro q _ j hj; rw [hcrt] at hj; omega

/-- The frame of a step that keeps the records, `crtInstance`, the peer order, the history, the
messages and the deliveries. -/
theorem frame_same (S S' : Sys) (hinst : ∀ r, (S'.rep r).inst = (S.rep r).inst)
    (hcrt : ∀ r, (S'.rep r).crtInstance = (S.rep r).crtInstance)
    (hpo : ∀ r, (S'.rep r).peerOrder = (S.rep r).peerOrder) (hhist : S'.hist = S.hist)
    (hmsgs : S'.msgs = S.msgs) (hdel : ∀ d, d ∈ S.delivered → d ∈ S'.delivered)
    (hconf : ∀ r, (S'.rep r).conflicts = (S.rep r).conflicts) (howner : S'.owner = S.owner)
    (hA : InvAux S)
    (hcls : ∀ r, (S'.rep r).lastScan = (S.rep r).lastScan ∧ (S'.rep r).lastPut = (S.rep r).lastPut) :
    AuxFrame S S' := by
  refine ⟨fun r x w' h => ⟨w', by rw [← hinst]; exact h, CoreEq.refl _⟩,
    fun r x w h => ⟨w, by rw [hinst]; exact h, CoreEq.refl _⟩, hcrt,
    fun r hr => by rw [hpo]; exact hA.peerOk r hr, fun r e _ => by simp only [Sys.ev, hhist],
    fun fr to => by rw [hmsgs]; exact List.Sublist.refl _, fun fr to n m h => ⟨n, by rw [← hmsgs]; exact h, Or.inl rfl⟩,
    hdel, fun r to m h => by simpa [Sys.ev, hhist] using h,
    fun r e r' e' _ h => by simpa [Sys.evBefore, hhist] using h, hconf, howner,
    fun r e h => by simpa [Sys.ev, hhist] using h, hcls⟩

end AuxProof

open AuxProof

theorem inv_init' : Inv Sys.init := ⟨inv0_init', aux_init⟩

theorem inv_step_clientPropose' (S : Sys) (i : Nat) (p : Proposal) (hS : Inv S)
    (hp : p.cid ∉ S.ops.map (·.2.cid)) :
    Inv { S with ops := S.ops ++ [(i, p)],
                 proposeChan := upd S.proposeChan i (S.proposeChan i ++ [p]) } :=
  ⟨inv0_step_clientPropose' S i p hS.1 hp, aux_congr S _ hS.2 hS.1.1.2.2.2.2.2.2.1
    (frame_same S _ (fun r => rfl) (fun r => rfl) (fun r => rfl) rfl rfl (fun d h => h)
      (fun r => rfl) rfl hS.2 (fun r => ⟨rfl, rfl⟩))
    (PMProof.pm_same hS.2.pm (fun r => rfl) rfl rfl (fun _ _ _ h => h) rfl (fun _ _ _ h => h))
    (ExecOrd.invExec_clientPropose S i p hS.1 hS.2.exec hp)
    (execLo_of_eq hS.2.execLo (fun r _ => rfl))⟩

theorem inv_step_peerOrder' (S : Sys) (i : Nat) (o : List Nat) (hS : Inv S)
    (ho : Sys.peerOrderOk i o) :
    Inv { S with rep := upd S.rep i { S.rep i with peerOrder := o } } := by
  have h0' := inv0_step_peerOrder' S i o hS.1
  refine ⟨h0', aux_congr S _ hS.2 hS.1.1.2.2.2.2.2.2.1 ?_
    (PMProof.pm_same hS.2.pm (fun r => by by_cases hr : r = i <;> simp [upd_apply, hr]) rfl rfl
      (fun _ _ _ h => h) rfl (fun _ _ _ h => h))
    (ExecOrd.invExec_same hS.1 hS.2.exec (fun r => by by_cases hr : r = i <;> simp [upd_apply, hr])
      (fun r e h => h) (ExecOrd.I0.agr h0') rfl rfl rfl rfl rfl rfl rfl)
    (execLo_upd hS.2.execLo rfl rfl)⟩
  refine ⟨fun r x w' h => ⟨w', ?_, CoreEq.refl _⟩, fun r x w h => ⟨w, ?_, CoreEq.refl _⟩,
    fun r => ?_, fun r hr => ?_, fun r e _ => Iff.rfl, fun fr to => List.Sublist.refl _,
    fun fr to n m h => ⟨n, h, Or.inl rfl⟩, fun d h => h, fun r to m h => h,
    fun r e r' e' _ h => h, fun r => ?_, rfl, fun r e h => h, fun r => ?_⟩
  · by_cases hr : r = i
    · subst hr; simp only [upd_same] at h; exact h
    · simp only [upd_other _ _ _ _ hr] at h; exact h
  · by_cases hr : r = i
    · subst hr; simp only [upd_same]; exact h
    · simp only [upd_other _ _ _ _ hr]; exact h
  · by_cases hr : r = i
    · subst hr; simp only [upd_same]
    · simp only [upd_other _ _ _ _ hr]
  · by_cases hri : r = i
    · subst hri; simp only [upd_same]
      obtain ⟨-, hperm⟩ := ho
      refine ⟨hperm.nodup_iff.mpr (List.nodup_range.filter _), fun p hp => ?_⟩
      have := hperm.subset hp
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at this
      exact this
    · simp only [upd_other _ _ _ _ hri]; exact hS.2.peerOk r hr
  · by_cases hr : r = i
    · subst hr; simp only [upd_same]
    · simp only [upd_other _ _ _ _ hr]
  · constructor <;>
    · by_cases hr : r = i
      · subst hr; simp only [upd_same]
      · simp only [upd_other _ _ _ _ hr]

theorem inv_step_beTheLeader' (S : Sys) (i : Nat) (hS : Inv S) :
    Inv { S with rep := upd S.rep i (hBeTheLeader (S.rep i)) } := by
  have h0' := inv0_step_beTheLeader' S i hS.1
  refine ⟨h0', aux_congr S _ hS.2 hS.1.1.2.2.2.2.2.2.1
    (frame_same S _ (fun r => ?_) (fun r => ?_) (fun r => ?_) rfl rfl (fun d h => h)
      (fun r => ?_) rfl hS.2 (fun r => ⟨?_, ?_⟩))
    (PMProof.pm_same hS.2.pm (fun r => ?_) rfl rfl (fun _ _ _ h => h) rfl (fun _ _ _ h => h))
    (ExecOrd.invExec_same hS.1 hS.2.exec (fun r => ?_)
      (fun r e h => h) (ExecOrd.I0.agr h0') rfl rfl rfl rfl rfl rfl rfl)
    (execLo_upd hS.2.execLo rfl (by simp only [hBeTheLeader]))⟩ <;>
  · by_cases hr : r = i
    · subst hr; simp only [upd_same, hBeTheLeader]
    · simp only [upd_other _ _ _ _ hr]

theorem inv_step_flush' (S : Sys) (i to : Nat) (m : Msg) (rest : List Msg) (hS : Inv S)
    (h : S.outbox i to = m :: rest) :
    Inv { S with sent := upd S.sent i (upd (S.sent i) to (S.sent i to ++ [m])),
                 outbox := upd S.outbox i (upd (S.outbox i) to rest) } := by
  have h0' := inv0_step_flush' S i to m rest hS.1 h
  have hmF : ({ S with sent := upd S.sent i (upd (S.sent i) to (S.sent i to ++ [m])), outbox := upd S.outbox i (upd (S.outbox i) to rest) } : Sys).msgs = S.msgs := by
    funext fr to'
    simp only [Sys.msgs, Sys.intended]
    by_cases h1 : fr = i
    · subst h1; by_cases h2 : to' = to
      · subst h2; simp [h]
      · simp [upd_apply, h2]
    · simp [upd_apply, h1]
  refine ⟨h0', aux_congr S _ hS.2 hS.1.1.2.2.2.2.2.2.1
    (frame_same S _ (fun r => rfl) (fun r => rfl) (fun r => rfl) rfl hmF (fun d h => h)
      (fun r => rfl) rfl hS.2 (fun r => ⟨rfl, rfl⟩))
    (PMProof.pm_same hS.2.pm (fun r => rfl) rfl hmF (fun fr to' m' hm' => ?_) rfl
      (fun fr to' m' hm' => ?_))
    (ExecOrd.invExec_same hS.1 hS.2.exec (fun r => rfl)
      (fun r e h => h) (ExecOrd.I0.agr h0') rfl rfl rfl rfl rfl rfl rfl)
    (execLo_of_eq hS.2.execLo (fun r _ => rfl))⟩
  · by_cases h1 : fr = i
    · subst h1; by_cases h2 : to' = to
      · subst h2; simp [hm']
      · simp [upd_apply, h2, hm']
    · simp [upd_apply, h1, hm']
  · by_cases h1 : fr = i
    · subst h1; by_cases h2 : to' = to
      · subst h2
        simp only [upd_same, h, List.mem_append, List.mem_cons, List.mem_singleton] at hm' ⊢
        rcases hm' with (h3 | h3 | h3) | h3
        · exact Or.inl h3
        · exact Or.inr (Or.inl h3)
        · simp at h3
        · exact Or.inr (Or.inr h3)
      · simpa [upd_apply, h2] using hm'
    · simpa [upd_apply, h1] using hm'

theorem inv_step_lose' (S : Sys) (i to : Nat) (m : Msg) (rest : List Msg) (hS : Inv S)
    (h : S.outbox i to = m :: rest) :
    Inv { S with outbox := upd S.outbox i (upd (S.outbox i) to rest) } := by
  have h0' := inv0_step_lose' S i to m rest hS.1 h
  refine ⟨h0', aux_congr S _ hS.2 hS.1.1.2.2.2.2.2.2.1 ?_ ?_
    (ExecOrd.invExec_same hS.1 hS.2.exec (fun r => rfl)
      (fun r e h => h) (ExecOrd.I0.agr h0') rfl rfl rfl rfl rfl rfl rfl)
    (execLo_of_eq hS.2.execLo (fun r _ => rfl))⟩
  have hm : ∀ fr to', ({ S with outbox := upd S.outbox i (upd (S.outbox i) to rest) } : Sys).msgs
      fr to' = if fr = i ∧ to' = to then S.sent i to ++ rest ++ S.intended i to
        else S.msgs fr to' := by
    intro fr to'
    simp only [Sys.msgs, Sys.intended]
    by_cases h1 : fr = i
    · subst h1; by_cases h2 : to' = to
      · subst h2; simp
      · simp [upd_apply, h2]
    · simp [upd_apply, h1]
  refine ⟨fun r x w' h => ⟨w', h, CoreEq.refl _⟩, fun r x w h => ⟨w, h, CoreEq.refl _⟩,
    fun r => rfl, fun r hr => hS.2.peerOk r hr, fun r e _ => Iff.rfl, fun fr to' => ?_,
    fun fr to' n m' hn => ?_, fun d h => h, fun r to m h => h, fun r e r' e' _ h => h,
    fun r => rfl, rfl, fun r e h => h, fun r => ⟨rfl, rfl⟩⟩
  · rw [hm]; split
    · rename_i hc; obtain ⟨rfl, rfl⟩ := hc
      simp only [Sys.msgs, h]
      exact List.Sublist.append (List.Sublist.append (List.Sublist.refl _)
        (List.sublist_cons_self _ _)) (List.Sublist.refl _)
    · exact List.Sublist.refl _
  · rw [hm] at hn; split at hn
    · rename_i hc; obtain ⟨rfl, rfl⟩ := hc
      simp only [Sys.msgs, h]
      by_cases hlt : n < (S.sent fr to').length
      · refine ⟨n, ?_, Or.inl rfl⟩
        rw [List.append_assoc, List.getElem?_append_left hlt] at hn ⊢; exact hn
      · refine ⟨n + 1, ?_, Or.inr (by omega)⟩
        rw [List.append_assoc] at hn ⊢
        rw [List.getElem?_append_right (by omega)] at hn ⊢
        rw [show n + 1 - (S.sent fr to').length = (n - (S.sent fr to').length) + 1 by omega]
        simpa using hn
    · exact ⟨n, hn, Or.inl rfl⟩
  · have hm : ∀ fr to', ({ S with outbox := upd S.outbox i (upd (S.outbox i) to rest) } : Sys).msgs
        fr to' = if fr = i ∧ to' = to then S.sent i to ++ rest ++ S.intended i to
          else S.msgs fr to' := by
      intro fr to'
      simp only [Sys.msgs, Sys.intended]
      by_cases h1 : fr = i
      · subst h1; by_cases h2 : to' = to
        · subst h2; simp
        · simp [upd_apply, h2]
      · simp [upd_apply, h1]
    refine PMProof.pm_sub hS.2.pm (fun r => rfl) rfl (fun fr to' m' hm' => ?_) (fun y u hu => ?_)
      (fun _ _ _ h => h) rfl (fun fr to' m' hm' => ?_)
    · rw [hm] at hm'; split at hm'
      · rename_i hc; obtain ⟨rfl, rfl⟩ := hc
        simp only [Sys.msgs, h, List.mem_append, List.mem_cons] at hm' ⊢
        rcases hm' with (h1 | h1) | h1
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr (Or.inr h1))
        · exact Or.inr h1
      · exact hm'
    · have hcm' := h0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      rw [LoseProof.committedVal_ev _ hcm']
      exact (LoseProof.committedVal_ev _ hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 y u).mp hu
    · by_cases h1 : fr = i
      · subst h1; by_cases h2 : to' = to
        · subst h2
          simp only [upd_same, h, List.mem_append, List.mem_cons] at hm' ⊢
          rcases hm' with h3 | h3
          · exact Or.inl h3
          · exact Or.inr (Or.inr h3)
        · simpa [upd_apply, h2] using hm'
      · simpa [upd_apply, h1] using hm'

theorem inv_step_execSCC' (S : Sys) (i : Nat) (C : List InstId) (hS : Inv S) (hi : i < nR)
    (hidle : S.idle i) (hC : sccReady (S.rep i) C) : Inv (S.startSCC i C) :=
  ⟨inv0_step_execSCC' S i C hS.1 hi hidle hC, aux_congr S _ hS.2 hS.1.1.2.2.2.2.2.2.1
    (frame_same S _ (fun r => rfl) (fun r => rfl) (fun r => rfl) rfl
      (by funext fr to; rfl) (fun d h => h) (fun r => rfl) rfl hS.2 (fun r => ⟨rfl, rfl⟩))
    (PMProof.pm_same hS.2.pm (fun r => rfl) rfl (by funext fr to; rfl) (fun _ _ _ h => h) rfl
      (fun _ _ _ h => h))
    (ExecOrd.invExec_execSCC S i C hS.1 hS.2.exec hi hidle hC)
    (execLo_of_eq hS.2.execLo (fun r _ => rfl))⟩

/-- (p-exec) `ExecLo` under `execBump`: `ExecedUpTo[q] + 1` does not overflow (if `ExecedUpTo[q] ≥ 0`
it is an executed instance's index, in range by `Inv.wf`). -/
theorem execLo_bump {S : Sys} {i q : Nat} (h0 : Inv0 S) (h : ExecLo S) (hq : q < nR)
    (he : (S.rep i).executed ⟨q, toN ((S.rep i).execedUpTo q + 1)⟩) :
    ExecLo { S with rep := upd S.rep i (execBump (S.rep i) q) } := by
  intro r hr q' hq'
  by_cases hri : r = i
  · subst hri
    simp only [upd_same, execBump]
    by_cases hqq : q' = q
    · subst hqq
      simp only [upd_same]
      have hlo := h r hr q' hq'
      rcases ExecProof.zz_succ ((S.rep r).execedUpTo q') with h1 | h1
      · rw [h1]; omega
      · exfalso
        -- overflow: `ExecedUpTo[q] = 2^31 - 1`, an executed (so in range) index
        have hbig : zz ((S.rep r).execedUpTo q') = 2 ^ 31 - 1 := by
          have := BitVec.toInt_lt (x := (S.rep r).execedUpTo q')
          simp only [zz, sint.Z, BitVec.toInt_add, Int.bmod] at h1 hlo this ⊢
          simp at h1 hlo this ⊢
          split at h1 <;> omega
        have hn : ((toN ((S.rep r).execedUpTo q') : Nat) : Int) ≤ zz ((S.rep r).execedUpTo q') := by
          have hbig' : sint.Z ((S.rep r).execedUpTo q') = 2 ^ 31 - 1 := hbig
          simp [toN, hbig']
        obtain ⟨w, hw, -⟩ := h0.1.2.2.2.2.1 r hr q' hq' _ hn
        obtain ⟨-, -, hlt, -⟩ := h0.1.2.1 r hr _ w hw
        have hbig' : sint.Z ((S.rep r).execedUpTo q') = 2 ^ 31 - 1 := hbig
        simp [toN, hbig', MAX_INSTANCE] at hlt
    · simp only [upd_other _ _ _ _ hqq]; exact h r hr q' hq'
  · simp only [upd_other _ _ _ _ hri]; exact h r hr q' hq'

theorem inv_step_execBump' (S : Sys) (i q : Nat) (hS : Inv S) (hq : q < nR)
    (he : (S.rep i).executed ⟨q, toN ((S.rep i).execedUpTo q + 1)⟩) :
    Inv { S with rep := upd S.rep i (execBump (S.rep i) q) } := by
  have h0' := inv0_step_execBump' S i q hS.1 hq he
  refine ⟨h0', aux_congr S _ hS.2 hS.1.1.2.2.2.2.2.2.1
    (frame_same S _ (fun r => ?_) (fun r => ?_) (fun r => ?_) rfl rfl (fun d h => h)
      (fun r => ?_) rfl hS.2 (fun r => ⟨?_, ?_⟩))
    (PMProof.pm_same hS.2.pm (fun r => ?_) rfl rfl (fun _ _ _ h => h) rfl (fun _ _ _ h => h))
    (ExecOrd.invExec_same hS.1 hS.2.exec (fun r => ?_)
      (fun r e h => h) (ExecOrd.I0.agr h0') rfl rfl rfl rfl rfl rfl rfl)
    (execLo_bump hS.1 hS.2.execLo hq he)⟩ <;>
  · by_cases hr : r = i
    · subst hr; simp only [upd_same, execBump]
    · simp only [upd_other _ _ _ _ hr]

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs AuxProof BcastProof

theorem bcastRep_peerOrder (σ : RState) (b : Bcast) (a : Bool) :
    (bcastRep σ b a).peerOrder = σ.peerOrder := by
  unfold bcastRep
  split
  · unfold setPreAcceptsSent; split
    · split <;> rfl
    · rfl
  · rfl

theorem BcastProof.PasRel.core {w w' : InstRec} (h : PasRel w w') : CoreEq w w' := by
  rcases h with rfl | ⟨lb, n, hlb, rfl⟩
  · exact CoreEq.refl _
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun lb' h => ⟨lb, hlb, ?_⟩, fun lb0 h => ?_⟩
    · simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [hlb] at h; cases h; exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem bcast_msgs_prefix (S : Sys) (i : Nat) (b : Bcast) (a : Bool) (hb : S.pending i = some b)
    (p : Nat) (ps : List Nat) (hpe : b.peers = p :: ps) (hnd : b.peers.Nodup) (fr to : Nat) :
    (S.bcastStep i b a).msgs fr to <+: S.msgs fr to := by
  have hob : (S.bcastStep i b a).outbox fr to =
      S.outbox fr to ++ (if a = true ∧ fr = i ∧ to = p then [b.m] else []) := by
    simp only [Sys.bcastStep, hpe]
    cases a
    · simp
    · simp only [Sys.emit, upd_apply]
      by_cases h1 : fr = i
      · subst h1; by_cases h2 : to = p
        · subst h2; simp
        · simp [h2]
      · simp [h1]
  have hsent : (S.bcastStep i b a).sent = S.sent := by
    simp only [Sys.bcastStep, hpe]; cases a <;> rfl
  have hpend : (S.bcastStep i b a).pending = upd S.pending i (b.next a) := by
    simp only [Sys.bcastStep, hpe]; cases a <;> rfl
  simp only [Sys.msgs, Sys.intended, hob, hsent, hpend]
  by_cases h1 : fr = i
  · subst h1
    simp only [upd_same, hb]
    have hint : ∀ b', b.next a = some b' → to ∈ b'.peers → to ∈ b.peers ∧ to ≠ p := by
      intro b' hn ht
      obtain ⟨-, -, e3, -⟩ := next_some b b' a hn
      rw [e3, hpe] at ht; simp only [List.tail_cons] at ht
      rw [hpe] at hnd ⊢
      refine ⟨List.mem_cons_of_mem _ ht, fun h => ?_⟩
      subst h; exact (List.nodup_cons.mp hnd).1 ht
    have hpm : p ∈ b.peers := by rw [hpe]; exact List.mem_cons_self
    cases hn : b.next a with
    | none =>
      simp only [List.append_nil]
      by_cases hc : a = true ∧ to = p
      · obtain ⟨rfl, rfl⟩ := hc
        simp only [and_self, if_true, hpm, List.append_assoc]
        exact List.prefix_refl _
      · rw [if_neg (by simpa using hc)]
        simp only [List.append_nil]
        exact List.prefix_append _ _
    | some b' =>
      obtain ⟨e1, -⟩ := next_some b b' a hn
      simp only
      by_cases hc : a = true ∧ to = p
      · obtain ⟨rfl, rfl⟩ := hc
        have : to ∉ b'.peers := fun ht => (hint b' hn ht).2 rfl
        simp only [and_self, if_true, hpm, this, if_false, List.append_nil, List.append_assoc]
        exact List.prefix_refl _
      · rw [if_neg (by simpa using hc), List.append_nil]
        by_cases ht : to ∈ b'.peers
        · rw [if_pos ht, if_pos (hint b' hn ht).1, e1]; exact List.prefix_refl _
        · rw [if_neg ht, List.append_nil]; exact List.prefix_append _ _
  · simp only [upd_other _ _ _ _ h1, h1, false_and, and_false, if_false, List.append_nil]
    exact List.prefix_refl _

theorem inv_step_bcast' (S : Sys) (i : Nat) (b : Bcast) (a : Bool) (hS : Inv S)
    (hb : S.pending i = some b) (hp : b.peers ≠ []) : Inv (S.bcastStep i b a) := by
  have h0' := inv0_step_bcast' S i b a hS.1 hb hp
  obtain ⟨p, ps, hpe⟩ : ∃ p ps, b.peers = p :: ps := by
    cases h : b.peers with
    | nil => exact absurd h hp
    | cons p ps => exact ⟨p, ps, rfl⟩
  have hnd : b.peers.Nodup := (hS.1.1.2.2.2.2.2.2.2 i b hb).2.2.2.2.1
  have hkind : b.m.isBcast = true := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 i b hb
  have hrep : (S.bcastStep i b a).rep = upd S.rep i (bcastRep (S.rep i) b a) := by
    simp only [Sys.bcastStep, hpe]; cases a <;> rfl
  have hext : BSExt S (S.bcastStep i b a) := by
    simp only [Sys.bcastStep, hpe]
    cases a
    · exact ⟨[], by simp, by simp⟩
    · exact ⟨[(i, .sent p b.m)], rfl, by
        intro x hx; simp only [List.mem_singleton] at hx; exact ⟨i, p, b.m, hx, hkind⟩⟩
  have hdel : (S.bcastStep i b a).delivered = S.delivered := by
    simp only [Sys.bcastStep, hpe]; cases a <;> rfl
  have hsent : (S.bcastStep i b a).sent = S.sent := by
    simp only [Sys.bcastStep, hpe]; cases a <;> rfl
  have hpre := bcast_msgs_prefix S i b a hb p ps hpe hnd
  have hcm : ∀ r y, ExecOrd.cmdsAt ((S.bcastStep i b a).rep r) y = ExecOrd.cmdsAt (S.rep r) y := by
    intro r y; rw [hrep]
    by_cases hr : r = i
    · subst hr; simp only [upd_same, ExecOrd.cmdsAt]
      cases h : (bcastRep (S.rep r) b a).inst y with
      | none =>
        cases h' : (S.rep r).inst y with
        | none => rfl
        | some w => obtain ⟨w', hw', -⟩ := (bcastRep_inst _ _ _ _).2 w h'; rw [h] at hw'; cases hw'
      | some w' =>
        obtain ⟨w, hw, hrel⟩ := (bcastRep_inst _ _ _ _).1 w' h
        rw [hw]; simp [(PasRel.fields hrel).1]
    · simp only [upd_other _ _ _ _ hr]
  have hX' : InvExec (S.bcastStep i b a) := by
    refine ExecOrd.invExec_step hS.1 hS.2.exec (fun r e h => ev_mono hext r e h) (ExecOrd.I0.agr h0')
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ (fun r _ y _ => hcm r y) (fun r _ _ y => hcm r y) ?_
    any_goals (simp only [Sys.bcastStep, hpe]; cases a <;> rfl)
    intro x w' lb' hw' hlb' hne
    rw [hrep] at hw'
    by_cases hr : x.q = i
    · rw [hr] at hw' ⊢; simp only [upd_same] at hw'
      obtain ⟨w, hw, hrel⟩ := (bcastRep_inst _ _ _ _).1 w' hw'
      obtain ⟨lb, hlb, hlb'⟩ := (PasRel.fields hrel).2.2.2.2.2.2.2.2 lb' hlb'
      refine ⟨w, lb, hw, hlb, ?_⟩
      rcases hlb' with e | ⟨n, e⟩ <;> subst e <;> exact hne
    · simp only [upd_other _ _ _ _ hr] at hw'; exact ⟨w', lb', hw', hlb', hne⟩
  have hpm' : InvPM (S.bcastStep i b a) := by
    refine PMProof.pm_bcast S i b a hS.2.pm hb hp (hS.1.1.2.2.2.2.2.2.2 i b hb).2.2.2.1 hkind
      (fun fr to m h => (hpre fr to).subset h) (fun y u hu => ?_)
    rw [LoseProof.committedVal_ev _ h0'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    obtain ⟨r, c, hc⟩ :=
      (LoseProof.committedVal_ev _ hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 y u).mp hu
    exact ⟨r, c, ev_mono hext r _ hc⟩
  refine ⟨h0', aux_congr S _ hS.2 hS.1.1.2.2.2.2.2.2.1 ?_ hpm' hX'
    (execLo_upd hS.2.execLo hrep (bcastRep_eq _ _ _).2.2.2.1)⟩
  refine ⟨fun r x w' h => ?_, fun r x w h => ?_, fun r => ?_, fun r hr => ?_, fun r e he => ?_,
    fun fr to => (hpre fr to).sublist, fun fr to n m h => ?_, fun d h => by rw [hdel]; exact h,
    fun r to m h => (ev_iff hext _ _ (fun to' m' h' => by cases h'; rfl)).mp h,
    fun r e r' e' he' h => evBefore_back hext _ _ _ _ he' h, fun r => ?_, ?_,
    fun r e h => ev_mono hext r e h, fun r => ?_⟩
  · rw [hrep] at h
    by_cases hr : r = i
    · subst hr; simp only [upd_same] at h
      obtain ⟨w, hw, hrel⟩ := (bcastRep_inst _ _ _ _).1 w' h
      exact ⟨w, hw, BcastProof.PasRel.core hrel⟩
    · simp only [upd_other _ _ _ _ hr] at h; exact ⟨w', h, CoreEq.refl _⟩
  · rw [hrep]
    by_cases hr : r = i
    · subst hr; simp only [upd_same]
      obtain ⟨w', hw', hrel⟩ := (bcastRep_inst _ _ _ _).2 w h
      exact ⟨w', hw', BcastProof.PasRel.core hrel⟩
    · simp only [upd_other _ _ _ _ hr]; exact ⟨w, h, CoreEq.refl _⟩
  · rw [hrep]
    by_cases hr : r = i
    · subst hr; simp only [upd_same]; exact (bcastRep_eq _ _ _).2.1
    · simp only [upd_other _ _ _ _ hr]
  · rw [hrep]
    by_cases hri : r = i
    · subst hri; simp only [upd_same, bcastRep_peerOrder]; exact hS.2.peerOk r hr
    · simp only [upd_other _ _ _ _ hri]; exact hS.2.peerOk r hr
  · refine ev_iff hext r e ?_
    intro to m h; exact absurd h (he to m)
  · obtain ⟨t, ht⟩ := hpre fr to
    refine ⟨n, ?_, Or.inl rfl⟩
    rw [← ht, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1, h]
  · rw [hrep]
    by_cases hr : r = i
    · subst hr; simp only [upd_same]; exact (bcastRep_eq _ _ _).2.2.1
    · simp only [upd_other _ _ _ _ hr]
  · simp only [Sys.bcastStep, hpe]; cases a <;> rfl
  · rw [hrep]
    by_cases hr : r = i
    · subst hr; simp only [upd_same]
      unfold bcastRep; split
      · unfold setPreAcceptsSent; split
        · split <;> exact ⟨rfl, rfl⟩
        · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    · simp only [upd_other _ _ _ _ hr]; exact ⟨trivial, trivial⟩

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

/-- (MODEL-REQUEST epaxos-2) A sent Commit, Accept or PreAccept carries a non-empty command
list. -/
theorem Inv.commit_cmds_ne {S : Sys} (hS : Inv S) {fr to : Nat} {m : Commit}
    (h : Msg.commit m ∈ S.msgs fr to) : m.command ≠ [] :=
  hS.2.cmdsNe.1 fr to _ h m.command rfl

theorem Inv.accept_cmds_ne {S : Sys} (hS : Inv S) {fr to : Nat} {m : Accept}
    (h : Msg.accept m ∈ S.msgs fr to) : m.command ≠ [] :=
  hS.2.cmdsNe.1 fr to _ h m.command rfl

theorem Inv.preAccept_cmds_ne {S : Sys} (hS : Inv S) {fr to : Nat} {m : PreAccept}
    (h : Msg.preAccept m ∈ S.msgs fr to) : m.command ≠ [] :=
  hS.2.cmdsNe.1 fr to _ h m.command rfl

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
