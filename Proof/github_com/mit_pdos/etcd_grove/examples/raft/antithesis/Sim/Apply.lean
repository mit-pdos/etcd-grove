/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: `apply` (#33 S4, the invariant phase)

`antSim_apply` (`Stmts.lean`): the committed entries of a node's `Ready` are reported
(`drain`, `evApply`) and taken (`ApplyEv`, B 598-609): after the `GC` steps due (`antSim_gc`),
they start right after what was handed out (C1: `delivered ++ ce` a prefix of the log, whose
indices are its positions), end within the commit index, which is within `chain` and agrees with it
(C3), and are the log's entries there; `memCommit` is the commit index (no queued write), so no
`ApplyBeyondCommit`. `ApplyEv` sets `lastApplied[n]` to their end and clears the announced write,
which C1 and C3 then hold of.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Boot
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Scope

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open AntCheck

/-! ## Entries compared and sliced -/

theorem value_equal_self (v : Value) : v.equal v = .ok true := by
  unfold Value.equal
  cases v.isRec <;> simp [epure]

theorem entry_equal_self (e : Entry) : e.equal e = .ok true := by
  unfold Entry.equal
  simp [value_equal_self]

theorem entriesEqualAux_self : ∀ a : List Entry, entriesEqualAux a a = .ok true
  | [] => rfl
  | e :: xs => by
    unfold entriesEqualAux
    simp only [entry_equal_self, eok_bind, Bool.not_true, Bool.false_eq_true, ite_false]
    exact entriesEqualAux_self xs

theorem entriesEqual_self (a : List Entry) : entriesEqual a a = .ok true := by
  unfold entriesEqual
  simp [entriesEqualAux_self]

/-- `SubSeq(s, d + 1, d + c)` of naturals within `s`. -/
theorem subSeq_nat (s : List Entry) (d c : Nat) (h : d + c ≤ s.length) :
    subSeq s ((d : Int) + 1) ((d : Int) + c) = .ok ((s.drop d).take c) := by
  unfold subSeq
  by_cases hc : c = 0
  · subst hc
    have h1 : (d : Int) + 1 > (d : Int) + ((0 : Nat) : Int) := by omega
    simp only [h1, ite_true, epure, List.take_zero]
  · have h1 : ¬ ((d : Int) + 1 > (d : Int) + c) := by omega
    have h2 : ¬ ((d : Int) + 1 < 1 ∨ (d : Int) + c > (s.length : Int)) := by omega
    simp only [h1, h2, ite_false, epure]
    have e1 : ((d : Int) + 1 - 1).toNat = d := by omega
    have e2 : ((d : Int) + c - ((d : Int) + 1) + 1).toNat = c := by omega
    rw [e1, e2]

section apply
variable [GooseExts]

theorem logOf_length (l : List EntryM) : (logOf l).length = l.length := List.length_map _

/-- What `ApplyEv` leaves: `lastApplied[n]` at the entries' end, the announced write cleared. -/
def applyS (S : State) (n : Nat) (last : Int) : State :=
  { S with lastApplied := S.lastApplied.set n last, undo := S.undo.set n none, i := S.i + 1 }

theorem apply_eq {R : RunCfg} {S : State} (n : Fin R.N) (v : NodeView) (hc : S.cfg = R.cfg) (hce : v.ce ≠ [])
    (hla : S.lastApplied[n.val]! = (v.delivered.length : Int))
    (hlg : S.log[n.val]! = logOf v.dur.log) (hidx : LogIdx v.dur.log)
    (hpre : v.delivered ++ v.ce <+: v.dur.log)
    (hch : ((v.delivered ++ v.ce).length : Int) ≤ S.chain.length)
    (hag : S.chain.take (v.delivered ++ v.ce).length = (S.log[n.val]!).take (v.delivered ++ v.ce).length)
    (hq : S.queue[n.val]! = [])
    (hmc : ((v.delivered ++ v.ce).length : Int) ≤ S.commitIndex[n.val]!) :
    S.step (evApply (nodeId n) v.byE v.ce) =
      .ok (some (applyS S n.val ((v.delivered ++ v.ce).length : Int))) := by
  obtain ⟨e0, ce', hce'⟩ : ∃ e0 ce', v.ce = e0 :: ce' := by
    cases h : v.ce with
    | nil => exact absurd h hce
    | cons a b => exact ⟨a, b, rfl⟩
  obtain ⟨tl, htl⟩ := hpre
  have hlog : v.dur.log = v.delivered ++ v.ce ++ tl := htl.symm
  have hd : (v.delivered.length : Nat) < v.dur.log.length := by
    rw [hlog, hce']; simp
  have he0 : v.dur.log[v.delivered.length]? = some e0 := by
    rw [hlog, hce']; simp
  have hfirst : firstOf v.ce = (v.delivered.length : Int) + 1 := by
    rw [hce']; unfold firstOf; exact hidx _ _ he0
  have hlen : ((v.delivered ++ v.ce).length : Int) = (v.delivered.length : Int) + v.ce.length := by
    simp
  have hlast : (v.delivered.length : Int) + 1 + ((logOf v.ce).length : Int) - 1 =
      ((v.delivered ++ v.ce).length : Int) := by
    rw [logOf_length, hlen]; omega
  have hlogn : ((v.delivered ++ v.ce).length : Int) ≤ ((S.log[n.val]!).length : Int) := by
    rw [hlg, logOf_length, hlog]; simp only [List.length_append]; omega
  have hs1 : subSeq S.chain 1 ((v.delivered ++ v.ce).length : Int) =
      .ok (S.chain.take (v.delivered ++ v.ce).length) := by
    have := subSeq_nat S.chain 0 (v.delivered ++ v.ce).length (by omega)
    simpa using this
  have hs2 : subSeq (S.log[n.val]!) 1 ((v.delivered ++ v.ce).length : Int) =
      .ok ((S.log[n.val]!).take (v.delivered ++ v.ce).length) := by
    have := subSeq_nat (S.log[n.val]!) 0 (v.delivered ++ v.ce).length (by omega)
    simpa using this
  have hs3 : subSeq (S.log[n.val]!) ((v.delivered.length : Int) + 1) ((v.delivered ++ v.ce).length : Int) =
      .ok (logOf v.ce) := by
    have := subSeq_nat (S.log[n.val]!) v.delivered.length v.ce.length (by
      have : (v.delivered ++ v.ce).length ≤ (S.log[n.val]!).length := by exact_mod_cast hlogn
      simpa using this)
    rw [hlen, this, hlg, hlog]
    unfold logOf
    rw [← List.map_drop, ← List.map_take]
    simp
  have hmem : S.memCommit n.val = .ok (S.commitIndex[n.val]!) := by
    unfold State.memCommit; rw [hq]; rfl
  unfold State.step
  simp (config := { decide := true }) only [evApply, idx_name hc, State.bind, State.applyEv, eok_bind,
    epure, ite_true, ite_false, need, Bool.false_eq_true, bne_self_eq_false, hfirst, hla, hlast]
  have hnot : ¬ (((v.delivered ++ v.ce).length : Int) > S.commitIndex[n.val]!) := by omega
  simp only [Bool.false_eq_true, ite_false, eok_bind, hs1, hs2, hag, entriesEqual_self, Bool.not_true,
    hs3, decide_eq_true hlogn, decide_eq_true hch, Bool.and_self, hmem, hnot]
  rfl

/-- **`apply`** (B 598-609), for the runs a mask below `mskB1a` admits (sync: no queued write). -/
theorem antSim_apply_in (msk : SimMask) (hmsk : msk ≤ mskB1a) :
    ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
      (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N),
      InMask msk R net xnet →
      SimPre R dec S V net xnet evs G → R.md.async = false → (V n).ce ≠ [] → Told (V n) →
      SimStep R dec evs G (evApply (nodeId n) (V n).byE (V n).ce)
        (setV V n { V n with delivered := (V n).delivered ++ (V n).ce, ce := [], undo := none,
                             made := true }) net xnet := by
  intro R dec S V net xnet evs G n hin ⟨hp, hs, hl, hgo⟩ hasync hce _
  obtain ⟨_, _, hbt, hpar, hspl, _, _, _⟩ := hin.b1a hmsk
  obtain ⟨S1, hgc, hs1, hgo1⟩ := antSim_gc R dec S V net xnet G hs hl hgo
  obtain ⟨hsh, hb, hn, hxn, hno⟩ := hs1
  have hc : S1.cfg = R.cfg := hsh.1
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18⟩ := hno n
  have hmems := (d3 hasync hbt hspl hpar).1
  obtain ⟨hcl, hag⟩ := hb.2.2.1 n
  have hmc : (((V n).delivered ++ (V n).ce).length : Int) ≤ S1.commitIndex[n.val]! := by
    rw [d1.2.2.2]
    have h1 : ((uint.nat (V n).dur.commit : Nat) : Int) = uint.Z (V n).dur.commit := by word
    have := d8.len; omega
  have hag' : S1.chain.take ((V n).delivered ++ (V n).ce).length =
      (S1.log[n.val]!).take ((V n).delivered ++ (V n).ce).length := by
    have e : ((V n).delivered ++ (V n).ce).length =
        min ((V n).delivered ++ (V n).ce).length (S1.commitIndex[n.val]!).toNat := by omega
    rw [e, ← List.take_take, ← List.take_take, hag]
  have hq : S1.queue[n.val]! = [] := by rw [d5, hmems]; rfl
  have hstep := apply_eq n (V n) hc hce d2.2.1 d1.2.2.1 d8.logIdx d8.prefix (by omega) hag' hq hmc
  obtain ⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, sh7, sh8, sh9, sh10, sh11, sh12, sh13, sh14⟩ := hsh
  let L : Int := (((V n).delivered ++ (V n).ce).length : Int)
  have hgo2 : GlobalOk R (applyS S1 n.val L) net G := hgo1
  have hrel : AntSim R dec (applyS S1 n.val L)
      (setV V n { V n with delivered := (V n).delivered ++ (V n).ce, ce := [], undo := none,
                           made := true }) net xnet := by
    refine ⟨⟨sh0, sh1, sh2, sh3, sh4, sh5, sh6, by simpa [applyS] using sh7, sh8, sh9, sh10,
      by simpa [applyS] using sh11, sh12, sh13, sh14⟩, hb, hn, hxn, fun k => ?_⟩
    by_cases hk : k = n
    · subst hk
      simp only [setV, ite_true]
      obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := d8
      refine ⟨d1, ⟨d2.1, ?_, d2.2.2⟩, fun a b c e => ⟨hmems, (d3 a b c e).2.1, fun h => absurd rfl h⟩,
        ⟨?_, ?_⟩, d5, d6, d7, ⟨f1, f2, f3, f4, by simpa using f5, by simpa using f6, f7⟩, d9, d10, d11, d12,
        d13, d14, d15, d16, d17, d18⟩
      · change (S1.lastApplied.set k.val L)[k.val]! = _
        rw [get!_set_self _ (by rw [sh7]; exact k.isLt)]
      · change ((S1.undo.set k.val none)[k.val]!).isNone = true ↔ (none : Option DurW) = none
        rw [get!_set_self _ (by rw [sh11]; exact k.isLt)]; simp
      · intro p hp
        change (S1.undo.set k.val none)[k.val]! = some p at hp
        rw [get!_set_self _ (by rw [sh11]; exact k.isLt)] at hp; cases hp
    · simp only [setV, hk, ite_false]
      have hne : k.val ≠ n.val := fun h => hk (Fin.ext h)
      obtain ⟨e1, e2, e3, e4, e5⟩ := hno k
      refine ⟨e1, ⟨e2.1, ?_, e2.2.2⟩, e3, ?_, e5⟩
      · rw [show (applyS S1 n.val L).lastApplied[k.val]! = S1.lastApplied[k.val]! from get!_set_ne _ _ hne]
        exact e2.2.1
      · unfold UndoIs
        rw [show (applyS S1 n.val L).undo[k.val]! = S1.undo[k.val]! from get!_set_ne _ _ hne]
        exact e4
  exact ⟨_, Prefix.snoc hp hgc hstep (violated_nil hb.1 hl hgo2), hrel, hgo2⟩

end apply

end AntSim
end EtcdGrove
end Perennial
