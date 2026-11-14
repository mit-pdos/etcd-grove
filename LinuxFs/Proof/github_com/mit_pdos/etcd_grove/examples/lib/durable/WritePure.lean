/- Lean-first (no Rocq counterpart).

# `examples/lib/durable` over `fsExt`: `Write`'s physical steps, pure (W4c U2, `notes/wal-fsext-w4c-plan.md`)

The physical states after `tryWrite`'s steps and the invariant's facts (`DurOk`) across them:
* `crHt`: the temporary's history after `os.OpenFile`'s create (`DurOk.crHt`: nothing but the
  temporary's name changes, which holds a file);
* `renPhys`: after the rename of the temporary (inode `c.i`, the new candidate `c`) over the name:
  `DurOk.renA`, the first rename (`alt = none` before: the client's state becomes `⟨data, cur⟩`; a
  crash keeps the rename or not, so the name holds the old `cur` or `data`), `DurOk.renB`, a retry's
  (the state already `⟨data, some old⟩`, unchanged);
* `DurOk.commit`: the directory's sync committed every entry of the name's claim (`HistCoh`): the
  state's `alt := none`.
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Defs
public import LinuxFs.Spec.os.Rename
public import GooseLang.Ext.Fs.TreeSharedCoh

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace DurFs

open Fs

/-! ## `valAfter` across an entry -/

theorem durValAfter_log_notKept (h : NamesH) (j : Ino) (K : Nat → Prop) (b : GoString) (x : Nat)
    (e : LogEntry) (c : Ents) (hx : ¬ K x) : (h.log x e c).valAfter j K b = h.valAfter j K b := by
  classical
  unfold NamesH.valAfter NamesH.log
  simp only [List.filter_append, List.filter_cons, List.filter_nil]
  rw [if_neg (by simp [hx])]
  simp

theorem durValAfter_log_last (h : NamesH) (j : Ino) (K : Nat → Prop) (b : GoString) (x : Nat)
    (e : LogEntry) (c : Ents) (hK : K x) (hw : e.op.Writes j b) :
    (h.log x e c).valAfter j K b = c !! b := by
  classical
  unfold NamesH.valAfter NamesH.log
  simp only [List.filter_append, List.filter_cons, List.filter_nil]
  rw [if_pos (by simp [hK, hw])]
  simp

/-! ## Names -/

theorem DFile.tb_ne (f : DFile) : f.tb ≠ f.b := by
  intro h
  have := congrArg List.length h
  simp [DFile.tb] at this
  omega

theorem DFile.b_ne_tb (f : DFile) : f.b ≠ f.tb := fun h => f.tb_ne h.symm

/-! ## The physical states -/

/-- The temporary's history after `os.OpenFile`'s create outcome `o`. -/
def crHt (f : DFile) (ht : NamesH) : Option (Nat × Nat × Ino) → NamesH
  | none => ht
  | some (x, s, i) => ht.log x (crEnt f.J f.tb i s) (<[f.tb := .file i]> ht.cur)

/-- The rename's entry (the temporary's inode `i` over the name, by a call begun at `s`). -/
def renEnt (f : DFile) (p : DurPhys) (i : Ino) (s : Nat) : LogEntry :=
  renFileEnt f.J f.tb f.J f.b i p.hb s

/-- **The physical state after the rename** of the temporary (the candidate `c`) over the name, logged
at `x` by a call begun at `s`, the state's `alt` now `a`. -/
def renPhys (f : DFile) (p : DurPhys) (c : DCand) (a : Option (Option GoString)) (x s : Nat) :
    DurPhys :=
  { hb := p.hb.log x (renEnt f p c.i s) (<[f.b := .file c.i]> p.hb.cur),
    ht := p.ht.log x (renEnt f p c.i s) (GMap.delete f.tb p.ht.cur),
    nc := p.nc, cands := p.cands ++ [c], alt := a }

@[simp] theorem renPhys_hb (f : DFile) (p : DurPhys) (c : DCand) (a : Option (Option GoString))
    (x s : Nat) :
    (renPhys f p c a x s).hb = p.hb.log x (renFileEnt f.J f.tb f.J f.b c.i p.hb s)
      (<[f.b := .file c.i]> p.hb.cur) := rfl
@[simp] theorem renPhys_ht (f : DFile) (p : DurPhys) (c : DCand) (a : Option (Option GoString))
    (x s : Nat) :
    (renPhys f p c a x s).ht = p.ht.log x (renFileEnt f.J f.tb f.J f.b c.i p.hb s)
      (GMap.delete f.tb p.ht.cur) := rfl
@[simp] theorem renPhys_nc (f : DFile) (p : DurPhys) (c : DCand) (a : Option (Option GoString))
    (x s : Nat) : (renPhys f p c a x s).nc = p.nc := rfl
@[simp] theorem renPhys_cands (f : DFile) (p : DurPhys) (c : DCand) (a : Option (Option GoString))
    (x s : Nat) : (renPhys f p c a x s).cands = p.cands ++ [c] := rfl
@[simp] theorem renPhys_alt (f : DFile) (p : DurPhys) (c : DCand) (a : Option (Option GoString))
    (x s : Nat) : (renPhys f p c a x s).alt = a := rfl

theorem renEnt_writes (f : DFile) (p : DurPhys) (i : Ino) (s : Nat) :
    (renEnt f p i s).op.Writes f.J f.b := by
  left
  simp [renEnt, renFileEnt, MetaOp.slots]

/-! ## The invariant's facts across the steps -/

theorem OutOk.mono_cands {s : DurSt} {cs cs' : List DCand} (hc : ∀ c ∈ cs, c ∈ cs')
    {o : Option Node} (h : OutOk s cs o) : OutOk s cs' o := by
  match o, h with
  | none, h => exact h
  | some (.file i), ⟨c, hc', hi, hv⟩ => exact ⟨c, hc c hc', hi, hv⟩

theorem DurOk.crHt {f : DFile} {s : DurSt} {p : DurPhys} (h : DurOk f s p)
    (o : Option (Nat × Nat × Ino)) : DurOk f s { p with ht := crHt f p.ht o } := by
  refine ⟨h.crash, h.cur, ?_, h.synced, h.cands, h.inj, h.alt⟩
  intro J
  match o with
  | none => exact h.tmp J
  | some (x, s0, i) =>
    simp only [DurFs.crHt, NamesH.log, GMap.lookup_insert]
    intro he; cases he

/-- The new candidate's facts, the rename's for both forms. -/
theorem DurOk.ren_common {f : DFile} {s s' : DurSt} {p : DurPhys} (h : DurOk f s p) (c : DCand)
    (a : Option (Option GoString)) (x s0 : Nat) (hc : c.Ok) (hci : c.i ∉ p.cands.map DCand.i)
    (hcur : s'.cur = some c.v) (halt : s'.alt = a) (ha : a ≠ none)
    (hold : ∀ o, OutOk s p.cands o → OutOk s' (p.cands ++ [c]) o) :
    DurOk f s' (renPhys f p c a x s0) := by
  have hmem : c ∈ p.cands ++ [c] := List.mem_append_right _ (List.mem_singleton_self _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, halt⟩
  · intro K hK
    by_cases hx : K x
    · simp only [renPhys]
      rw [durValAfter_log_last _ _ _ _ _ _ _ hx (renEnt_writes f p c.i s0), GMap.lookup_insert]
      exact ⟨c, hmem, rfl, Or.inl hcur⟩
    · simp only [renPhys]
      rw [durValAfter_log_notKept _ _ _ _ _ _ _ hx]
      refine hold _ (h.crash K (fun y e E hy hyn => hK y e E ?_ hyn))
      simp only [renPhys, NamesH.log]
      exact List.mem_append_left _ hy
  · rw [hcur]
    refine ⟨c, hmem, rfl, ?_⟩
    simp only [renPhys, NamesH.log, GMap.lookup_insert]
  · intro J
    simp only [renPhys, NamesH.log, GMap.lookup_delete]
    intro he; cases he
  · intro hn; rw [halt] at hn; exact absurd hn ha
  · intro c' hc'
    rcases List.mem_append.1 hc' with hc' | hc'
    · exact h.cands c' hc'
    · rw [List.mem_singleton.1 hc']; exact hc
  · simp only [renPhys, List.map_append, List.map_cons, List.map_nil]
    exact List.nodup_append.2 ⟨h.inj, (by simp), fun a ha b hb => by
      rw [List.mem_singleton.1 hb]; rintro rfl; exact hci ha⟩

/-- **The first rename** (`alt = none` before): the state becomes `⟨data, some cur⟩`. -/
theorem DurOk.renA {f : DFile} {s : DurSt} {p : DurPhys} (h : DurOk f s p) (hA : p.alt = none)
    (c : DCand) (x s0 : Nat) (hc : c.Ok) (hci : c.i ∉ p.cands.map DCand.i) :
    DurOk f ⟨some c.v, some s.cur⟩ (renPhys f p c (some s.cur) x s0) := by
  have hsa : s.alt = none := h.alt.trans hA
  refine h.ren_common c (some s.cur) x s0 hc hci rfl rfl (by simp) (fun o ho => ?_)
  match o, ho with
  | none, ho =>
    rcases ho with ho | ho
    · exact Or.inr (by simp only; rw [ho])
    · rw [hsa] at ho; cases ho
  | some (.file i), ⟨c', hc', hi, hv⟩ =>
    refine ⟨c', List.mem_append_left _ hc', hi, Or.inr ?_⟩
    rcases hv with hv | hv
    · simp only; rw [hv]
    · rw [hsa] at hv; cases hv

/-- **A retry's rename** (`alt ≠ none`, the name already holding `data`): the state unchanged. -/
theorem DurOk.renB {f : DFile} {s : DurSt} {p : DurPhys} (h : DurOk f s p) (hB : p.alt ≠ none)
    (c : DCand) (x s0 : Nat) (hc : c.Ok) (hci : c.i ∉ p.cands.map DCand.i)
    (hcur : s.cur = some c.v) :
    DurOk f s (renPhys f p c p.alt x s0) :=
  h.ren_common c p.alt x s0 hc hci hcur h.alt hB
    (fun _ ho => ho.mono_cands (fun _ h' => List.mem_append_left _ h'))

/-- **The commit**: every entry of the name's claim below `n` (its `next`), the state's `alt := none`. -/
theorem DurOk.commit {f : DFile} {s : DurSt} {p : DurPhys} (h : DurOk f s p)
    (hcoh : HistCoh p.hb f.J (.only [f.b])) (n : Nat) (hn : p.hb.next ≤ n) :
    DurOk f ⟨s.cur, none⟩ { p with nc := n, alt := none } := by
  refine ⟨?_, h.cur, h.tmp, fun _ => hn, h.cands, h.inj, rfl⟩
  intro K hK
  have hall : ∀ xe ∈ p.hb.ents, K xe.1 := fun xe hxe =>
    hK xe.1 xe.2.1 xe.2.2 hxe (Nat.lt_of_lt_of_le (hcoh.1 xe hxe) hn)
  show OutOk ⟨s.cur, none⟩ p.cands (p.hb.valAfter f.J K f.b)
  rw [hcoh.2 K hall f.b (by simp [NameSet.Mem])]
  have hc := h.cur
  cases hs : s.cur with
  | none =>
    rw [hs] at hc
    simp only at hc
    rw [hc]; exact Or.inl rfl
  | some v =>
    rw [hs] at hc
    obtain ⟨c, hc, hv, he⟩ := hc
    rw [he]
    exact ⟨c, hc, rfl, Or.inl (by rw [hv])⟩

end DurFs
end EtcdGrove
end Perennial
