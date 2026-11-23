/-
`InvExec` (p-modelexec) under `handleCommit`: a Commit of a single NONE command at the leader
re-proposes the batch its bookkeeping holds and drops it (`commit_reprop`); the batch's ops move
from the instance (now released: `Sys.propDead`) to the leader's channel (`invExec_commit`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.HCommit
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.ExecHS

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs HLocal CommitProof HStepProof

namespace ExecOrd

theorem commit_reprop (σ : RState) (m : Commit) :
    (hCommit σ m).2.filterMap Out.reprop = [] ∨
    ∃ w lb ps c, σ.inst ⟨toN m.replica, toN m.inst⟩ = some w ∧ w.lb = some lb ∧
      lb.clientProposals = some ps ∧ toN m.replica = σ.id ∧ m.command = [c] ∧ c.op = opNONE ∧
      (hCommit σ m).2.filterMap Out.reprop = ps ∧
      (((hCommit σ m).1.inst ⟨toN m.replica, toN m.inst⟩).bind (·.lb)) =
        some { lb with clientProposals := none } ∧
      Out.ev (.commit ⟨toN m.replica, toN m.inst⟩ m.ballot ⟨m.command, m.seq, m.deps⟩) ∈
        (hCommit σ m).2 := by
  unfold hCommit
  simp only [getOrDefault_eq]
  have hr : ∀ σ0 : RState, σ0.inst = σ.inst → recOr σ0 ⟨toN m.replica, toN m.inst⟩ = recOr σ ⟨toN m.replica, toN m.inst⟩ := by
    intro σ0 h; simp [recOr, h]
  rw [hr _ (by simp)]
  split
  · left; rfl
  split
  · left; rfl
  have hid : ((bumpRecvBallot (bumpCrt σ (toN m.replica) m.inst) m.ballot).setInst
      ⟨toN m.replica, toN m.inst⟩ (recOr σ ⟨toN m.replica, toN m.inst⟩)).id = σ.id := by
    simp only [RState.setInst, bumpRB_id, bumpCrt_id]
  rw [hid]
  generalize hw0 : recOr σ ⟨toN m.replica, toN m.inst⟩ = w0
  by_cases hc : toN m.replica = σ.id ∧ m.command.length = 1 ∧ Option.map (fun x => x.op) m.command.head? = some opNONE
  · rw [if_pos hc]
    cases hl : w0.lb with
    | none => left; simp [Out.reprop]
    | some lb =>
      cases hp : lb.clientProposals with
      | none => left; simp [Out.reprop, hp]
      | some ps =>
        right
        have hw : σ.inst ⟨toN m.replica, toN m.inst⟩ = some w0 := by
          rcases recOr_of σ ⟨toN m.replica, toN m.inst⟩ with h | ⟨-, h⟩
          · rw [h, hw0]
          · rw [hw0] at h; subst h; simp [newInstanceDefault] at hl
        obtain ⟨c, hcm⟩ : ∃ c, m.command = [c] := by
          match h : m.command, hc.2.1 with
          | [c], _ => exact ⟨c, rfl⟩
        have hcop : c.op = opNONE := by have := hc.2.2; rw [hcm] at this; simpa using this
        refine ⟨w0, lb, ps, c, hw, hl, hp, hc.1, hcm, hcop, ?_, ?_, ?_⟩
        · simp [Out.reprop, List.filterMap_map, hp, Function.comp_def]
        · simp [updateCommitted_inst, (uc_fields _ _ _ _ _).1, RState.setInst, hp]
        · simp [hp]
  · rw [if_neg hc]
    left; simp [Out.reprop]

theorem pos_append {α : Type} {l t : List α} {n : Nat} {a : α} (h : (l ++ t)[n]? = some a) :
    l[n]? = some a ∨ ∃ k, n = l.length + k ∧ t[k]? = some a := by
  by_cases hn : n < l.length
  · rw [List.getElem?_append_left hn] at h; exact Or.inl h
  · rw [List.getElem?_append_right (by omega)] at h
    exact Or.inr ⟨n - l.length, by omega, h⟩

/-- **`handleCommit` keeps `InvExec`.** -/
theorem invExec_commit (S : Sys) (fr i n : Nat) (hS : Inv S) (hi : i < nR) (hidle : S.idle i)
    (p : Commit) (hm : (S.sent fr i)[n]? = some (.commit p))
    (h0' : Inv0 (S.deliver fr i n (.commit p))) : InvExec (S.deliver fr i n (.commit p)) := by
  have h0 := hS.1
  have hX := hS.2.exec
  obtain ⟨σ', E, hH, -, -, -, -, -, hcase⟩ := commit_cases S fr i n p hidle hm
  have hH2 := hs_deliver S fr i n (.commit p) hidle hm
  have hσ : σ' = (hCommit (S.rep i) p).1 := by
    have := congrFun (hH.rep.symm.trans hH2.rep) i
    simpa [hMsg] using this
  have hch := deliver_chan S fr i n (.commit p)
  simp only [hMsg] at hch hH2
  generalize S.deliver fr i n (.commit p) = S' at hH hH2 hch h0' ⊢
  generalize hx : (⟨toN p.replica, toN p.inst⟩ : InstId) = x at hcase
  have hro := recOr_of (S.rep i) x
  generalize hw0 : recOr (S.rep i) x = w0 at hcase hro
  -- the records after the step
  obtain ⟨w', hσi, hw'⟩ : ∃ w', σ'.inst = upd (S.rep i).inst x (some w') ∧
      (w' = w0 ∨ (∃ lbo, (lbo = w0.lb ∨ ∃ lb, w0.lb = some lb ∧
        lbo = some { lb with clientProposals := none }) ∧ w' = comRec w0 lbo p ∧
        stGe w0.status stCOMMITTED = false)) := by
    rcases hcase with ⟨h1, -, -⟩ | ⟨lbo, h1, h2, h3, -⟩
    · exact ⟨w0, h1, Or.inl rfl⟩
    · exact ⟨_, h2, Or.inr ⟨lbo, h1, rfl, h3⟩⟩
  have hrep : ∀ r y, (S'.rep r).inst y =
      if r = i ∧ y = x then some w' else (S.rep r).inst y := by
    intro r y
    rw [hH.rep]
    by_cases h : r = i
    · subst h; simp only [upd_same, hσi, upd_apply, true_and]
    · simp [upd_other _ _ _ _ h, h]
  have hcv : ∀ y v, S.committedVal y v → S'.committedVal y v :=
    cv_mono h0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (fun r e h => hH.ev_old h)
  have hcp : ∀ y w'' lb'', (S'.rep y.q).inst y = some w'' →
      w''.lb = some lb'' → lb''.clientProposals ≠ none →
      ∃ w lb, (S.rep y.q).inst y = some w ∧ w.lb = some lb ∧ lb.clientProposals ≠ none := by
    intro y w'' lb'' h2 hl hne
    rw [hrep] at h2
    split at h2
    · rename_i hc; obtain ⟨h1, rfl⟩ := hc
      cases h2
      have hold : ∀ lb, w0.lb = some lb → lb.clientProposals ≠ none →
          ∃ w lb, (S.rep y.q).inst y = some w ∧ w.lb = some lb ∧ lb.clientProposals ≠ none := by
        intro lb h3 h4
        rcases hro with h | ⟨-, h⟩
        · exact ⟨w0, lb, by rw [h1]; exact h, h3, h4⟩
        · subst h; simp [newInstanceDefault] at h3
      rcases hw' with rfl | ⟨lbo, h3 | ⟨lb, h3, rfl⟩, rfl, -⟩
      · exact hold lb'' hl hne
      · simp only [comRec] at hl; rw [h3] at hl; exact hold lb'' hl hne
      · simp only [comRec, Option.some.injEq] at hl; subst hl; exact absurd rfl hne
    · exact ⟨w'', lb'', h2, hl, hne⟩
  have hdead : ∀ y, S.propDead y → S'.propDead y := propDead_keep hcv hcp
  -- the step with the channels kept
  have X : InvExec { S' with proposeChan := S.proposeChan } := by
    refine invExec_step h0 hX (fun r e h => hH.ev_old h) (I0.agr h0') hH.execLog hH.execCur
      hH.execIdx hH.gexec hH.owner rfl hH.ops (fun r _ y hy => ?_) (fun r _ hne y => ?_) hcp
    · show cmdsAt (S'.rep r) y = cmdsAt (S.rep r) y
      simp only [cmdsAt, hrep]
      split
      · rename_i hc; obtain ⟨rfl, rfl⟩ := hc
        obtain ⟨w, hw, hs⟩ := hy
        rcases hro with h | ⟨h, -⟩
        · rw [h] at hw; cases hw
          rcases hw' with rfl | ⟨-, -, -, h3⟩
          · rw [h]
          · rw [hs] at h3; exact absurd h3 (by decide)
        · rw [h] at hw; cases hw
      · rfl
    · show cmdsAt (S'.rep r) y = cmdsAt (S.rep r) y
      have : r ≠ i := by intro e; subst e; exact hne hidle.2
      simp only [cmdsAt, hrep, this, false_and, if_false]
  -- the channels
  rcases commit_reprop (S.rep i) p with h | ⟨w, lb, ps, c, hw, hlb, hps, hid, hc1, hc2, hR, hlb', hev⟩
  · have hch' : S'.proposeChan = S.proposeChan := by
      rw [hch]; funext r; simp only [h]; split <;> simp
    exact ⟨X.reach, X.ord, X.gloc, X.tokSlot, by rw [hch']; exact X.tokChan,
      by rw [hch']; exact X.chanOnce, by rw [hch', hH.ops]; exact hX.chanOps⟩
  · -- the re-proposal: `x`'s batch moves to `i`'s channel
    have hiid : (S.rep i).id = i := h0.1.1 i hi
    rw [hx] at hw hlb' hev
    have hxq : x.q = i := by rw [← hx]; simp only; rw [hid, hiid]
    have howner : S.owner x = some ps := (h0.1.2.1 i hi x w hw).2.2.2.2.2.2 lb ps hlb hps
    have hndead : ¬ S.propDead x := by
      rintro ⟨-, h2⟩; rw [hxq] at h2; rw [h2 w lb hw hlb] at hps; cases hps
    have hdx : S'.propDead x := by
      refine ⟨⟨⟨p.command, p.seq, p.deps⟩, c, Or.inl ⟨i, p.ballot, ?_⟩, hc1, hc2⟩, ?_⟩
      · refine hH2.ev_new ?_
        simp only [evsOf]; exact List.mem_filterMap.mpr ⟨_, hev, rfl⟩
      · intro w2 lb2 h2 hl2
        rw [hxq, hH2.rep] at h2; simp only [upd_same] at h2
        rw [h2] at hlb'; simp only [Option.bind_some, hl2, Option.some.injEq] at hlb'
        rw [hlb']
    have hslot : ∀ k q, ps[k]? = some q → S.slotOp (x, k) = some q := by
      intro k q h; simp only [Sys.slotOp, howner, Option.bind_some]; exact h
    have hchi : ∀ r, S'.proposeChan r =
        S.proposeChan r ++ (if r = i then ps else []) := by
      intro r; rw [hch]; simp only [hR]
    have hpos : ∀ r k q, (S'.proposeChan r)[k]? = some q →
        (S.proposeChan r)[k]? = some q ∨ (r = i ∧ ∃ k', k = (S.proposeChan r).length + k' ∧ ps[k']? = some q) := by
      intro r k q h
      rw [hchi] at h
      rcases pos_append h with h | ⟨k', e, h⟩
      · exact Or.inl h
      · split at h
        · rename_i hr; exact Or.inr ⟨hr, k', e, h⟩
        · simp at h
    refine ⟨X.reach, X.ord, X.gloc, X.tokSlot, fun j q s q' h1 h2 h3 => ?_,
      fun j1 j2 k1 k2 q q' h1 h2 h3 => ?_, fun j q h => ?_⟩
    · rw [hchi] at h1
      rcases List.mem_append.mp h1 with h1 | h1
      · exact X.tokChan j q s q' h1 h2 h3
      · split at h1
        · obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp h1
          by_cases hs : s = (x, k)
          · rw [hs]; exact hdx
          · have h2' : S.slotOp s = some q' := by simpa only [Sys.slotOp, hH.owner] using h2
            rcases hX.tokSlot s (x, k) q' q hs h2' (hslot k q hk) h3 with h | h
            · exact hdead _ h
            · exact absurd h hndead
        · simp at h1
    · rcases hpos j1 k1 q h1 with g1 | ⟨e1, k1', e1', g1⟩ <;>
        rcases hpos j2 k2 q' h2 with g2 | ⟨e2, k2', e2', g2⟩
      · exact hX.chanOnce j1 j2 k1 k2 q q' g1 g2 h3
      · exact absurd (hX.tokChan j1 q (x, k2') q' (List.mem_of_getElem? g1) (hslot k2' q' g2) h3.symm)
          hndead
      · exact absurd (hX.tokChan j2 q' (x, k1') q (List.mem_of_getElem? g2) (hslot k1' q g1) h3)
          hndead
      · subst e1 e2
        refine ⟨rfl, ?_⟩
        by_cases hk : k1' = k2'
        · rw [e1', e2', hk]
        · rcases hX.tokSlot (x, k1') (x, k2') q q' (by simp [hk]) (hslot k1' q g1) (hslot k2' q' g2) h3
            with h | h <;> exact absurd h hndead
    · rw [hchi] at h
      rw [hH.ops]
      rcases List.mem_append.mp h with h | h
      · exact hX.chanOps j q h
      · split at h
        · rename_i hj
          have := (I0.slots h0).2 x ps howner q h
          rw [hxq] at this; rw [hj]; exact this
        · simp at h

end ExecOrd

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
