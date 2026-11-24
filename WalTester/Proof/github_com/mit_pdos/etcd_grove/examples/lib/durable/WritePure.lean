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

public import Perennial.Proof.strings.JoinBounded
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Defs
public import Spec.os.RenameS
public import GooseLang.Ext.Fs.TreeSharedCoh
public import Spec.os.File__WriteAt
public import Spec.os.WriteLong
public import Spec.os.File__Sync

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

theorem DFile.child_eq (d b : GoString) : child d b = d ++ [path.slash] ++ b := by
  simp [child]; rfl

/-- `filepath.Dir(name)`: the directory. -/
theorem DFile.dir_name {f : DFile} (hf : f.Ok) : path.dirModel f.name = f.d := by
  unfold DFile.name; rw [DFile.child_eq]; exact filepath.dirModel_name f.d f.b hf.1 hf.2.1

/-- `filepath.Base(name)`: the base name. -/
theorem DFile.base_name {f : DFile} (hf : f.Ok) : path.baseModel f.name = f.b := by
  unfold DFile.name; rw [DFile.child_eq]; exact filepath.baseModel_name f.d f.b hf.2.1

/-- `filepath.Join(dir, ".durable-"+base)`: the temporary's path. -/
theorem DFile.join_tmp {f : DFile} (hf : f.Ok) : path.joinModel [f.d, f.tb] = f.tmp := by
  unfold DFile.tmp; rw [DFile.child_eq]; exact filepath.joinModel_name f.d f.tb hf.1 hf.2.2.1

theorem DFile.join_len {f : DFile} (hf : f.Ok) : ([f.d, f.tb].map List.length).sum + 2 ≤ _root_.Perennial.strings.joinMax := by

  unfold _root_.Perennial.strings.joinMax
  have := hf.2.2.2.2.2
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- `O_RDWR|O_CREATE|O_TRUNC` with `O_CLOEXEC`: a valid read-write create-truncate open. -/
theorem durOpenFlag_ok :
    OpenFlagsOk ((W64 2 ||| W64 64 ||| W64 512) ||| W64 0x80000).toNat ∧
      ((W64 2 ||| W64 64 ||| W64 512) ||| W64 0x80000).toNat / O_CREAT % 2 = 1 ∧
      ((W64 2 ||| W64 64 ||| W64 512) ||| W64 0x80000).toNat / O_TRUNC % 2 = 1 := by
  unfold OpenFlagsOk O_CREAT O_TRUNC O_CLOEXEC
  decide

@[simp] theorem durOpenFd_ino (i : Ino) (fl : w64) : (openFd i fl).ino = i := rfl

theorem durOpenFlag_writable (i : Ino) :
    (openFd i ((W64 2 ||| W64 64 ||| W64 512) ||| W64 0x80000)).writable = true := by
  show decide (((W64 2 ||| W64 64 ||| W64 512) ||| W64 0x80000).toNat % 4 ≠ O_RDONLY) = true
  decide

/-! ## The temporary's file across the write and the sync -/

/-- What `trFile` says of a file's `OsMeta` `m` and bytes `ys` (but the size): every byte held, not
mapped, no sync without its bytes pending, a crash's lower bound at most the size, zeros known from at
least the size. -/
def TrOk (m : OsMeta) (ys : List ByteG) : Prop :=
  ys.length = m.size ∧ m.maps = ∅ ∧ m.cut = none ∧ m.lo ≤ m.size ∧ m.ZfGe

theorem pwSize_zero (n j : Nat) (hj : j ≤ n) : min n (pwSize 0 0 j) = pwSize 0 0 j ∧
    pwSize 0 0 j = j := by
  unfold pwSize
  split <;> omega

/-- The write of `data` (`j` bytes landed) at 0 into the empty file keeps `TrOk`. -/
theorem TrOk.pw {m : OsMeta} (hm : TrOk m []) (hsz : m.size = 0) (data : List w8) (hd : 0 < data.length)
    (j : Nat) (hj : j ≤ data.length) {ys : List ByteG} (hpw : os.PwOut m 0 data j [] ys) :
    TrOk (pwPost m 0 data.length j) ys := by
  obtain ⟨-, hmaps, hcut, hlo, ⟨z, hz, hzs⟩⟩ := hm
  obtain ⟨hl, -⟩ := hpw
  have hps := pwSize_zero data.length j hj
  have hs : (pwPost m 0 data.length j).size = j := by
    simp only [pwPost]; rw [hsz]; exact hps.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hs, hl, hsz]; simp only [Nat.zero_add, Nat.sub_zero]; rw [hps.1, hps.2]
  · simp only [pwPost, announce_maps]; exact hmaps
  · simp only [pwPost, OsMeta.announce_cut]; exact hcut
  · rw [hs]; simp only [pwPost, announce_lo]; omega
  · refine ⟨if min 0 m.size < 0 + data.length then max z (0 + data.length) else z, ?_, ?_⟩
    · simp only [pwPost, announce_zf, hz, Option.map_some]
    · rw [hs]; rw [if_pos (by omega)]; omega

/-- A write that landed whole holds `data`, and the file is its size. -/
theorem pw_whole {m : OsMeta} (hsz : m.size = 0) (data : List w8) (hd : 0 < data.length)
    {ys : List ByteG} (hpw : os.PwOut m 0 data data.length [] ys) :
    ys.map Prod.fst = data ∧ (pwPost m 0 data.length data.length).size = data.length := by
  obtain ⟨hl, hv⟩ := hpw
  have hps := pwSize_zero data.length data.length (Nat.le_refl _)
  simp only [Nat.zero_add, Nat.sub_zero] at hl
  rw [hsz, hps.1, hps.2] at hl
  refine ⟨List.ext_getElem (by simp [hl]) (fun i h1 h2 => ?_), ?_⟩
  · have hi : i < ys.length := by simpa using h1
    rw [List.getElem_map, (hv i hi).1]
    unfold pwByte
    rw [if_pos (by omega)]
    simp only [Nat.zero_add, Nat.sub_zero]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
  · simp only [pwPost]; rw [hsz]; exact hps.2

/-- `TrOk.pw` for a write of any length (`WriteAt.specLong`: chunks of at most 1 GiB, the first `A`
bytes announced, `j` landed, the last whole chunk ending at `E`). -/
theorem TrOk.pwA {m : OsMeta} (hm : TrOk m []) (hsz : m.size = 0) (data : List w8)
    (A j E : Nat) (hjA : j ≤ A) (hj : j ≤ data.length) {ys : List ByteG}
    (hpw : os.PwOutA m 0 data A j [] ys) :
    TrOk (os.pwPostE m 0 A j E) ys := by
  obtain ⟨-, hmaps, hcut, hlo, ⟨z, hz, hzs⟩⟩ := hm
  obtain ⟨hl, -⟩ := hpw
  have hps := pwSize_zero data.length j hj
  have hs : (os.pwPostE m 0 A j E).size = j := by
    simp only [os.pwPostE, pwPost]; rw [hsz]; exact hps.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hs, hl, hsz]; simp only [Nat.zero_add, Nat.sub_zero]; rw [hps.1, hps.2]
  · simp only [os.pwPostE, pwPost, announce_maps]; exact hmaps
  · simp only [os.pwPostE, pwPost, OsMeta.announce_cut]; exact hcut
  · rw [hs]; simp only [os.pwPostE, pwPost, announce_lo]; omega
  · refine ⟨if min 0 m.size < 0 + A then max z (0 + A) else z, ?_, ?_⟩
    · simp only [os.pwPostE, pwPost, announce_zf, hz, Option.map_some]
    · rw [hs]; split <;> omega

/-- `pw_whole` for a write of any length that landed whole. -/
theorem pw_wholeA {m : OsMeta} (hsz : m.size = 0) (data : List w8) (hd : 0 < data.length)
    (A E : Nat) {ys : List ByteG} (hpw : os.PwOutA m 0 data A data.length [] ys) :
    ys.map Prod.fst = data ∧ (os.pwPostE m 0 A data.length E).size = data.length := by
  obtain ⟨hl, hv⟩ := hpw
  have hps := pwSize_zero data.length data.length (Nat.le_refl _)
  simp only [Nat.zero_add, Nat.sub_zero] at hl
  rw [hsz, hps.1, hps.2] at hl
  refine ⟨List.ext_getElem (by simp [hl]) (fun i h1 h2 => ?_), ?_⟩
  · have hi : i < ys.length := by simpa using h1
    rw [List.getElem_map, (hv i hi).1]
    unfold pwByte
    rw [if_pos (by omega)]
    simp only [Nat.zero_add, Nat.sub_zero]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
  · simp only [os.pwPostE, pwPost]; rw [hsz]; exact hps.2

variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj] in
/-- A successful sync keeps `TrOk`, with the bytes durable. -/
theorem TrOk.synced {m : OsMeta} {ys : List ByteG} (h : TrOk m ys) :
    TrOk m.synced (ys.map (fun x => durB x.1)) := by
  obtain ⟨hl, hmaps, hcut, -, -⟩ := h
  refine ⟨by simp [hl, OsMeta.synced], hmaps, hcut, by simp [OsMeta.synced], ?_⟩
  exact ⟨m.syncZ, rfl, m.size_le_syncZ⟩

/-- The file of `data`, written whole and synced: a candidate. -/
theorem dcand_ok (i : Ino) {m : OsMeta} (data : List w8) (hsz : m.size = data.length)
    (hd : data.length < 2 ^ 63) : (DCand.mk i m.synced data).Ok :=
  ⟨hsz, rfl, rfl, hd⟩

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
  refine ⟨h.crash, h.cur, ?_, h.synced, h.cands, h.inj, h.alt, ?_⟩
  · intro J
    match o with
    | none => exact h.tmp J
    | some (x, s0, i) =>
      simp only [DurFs.crHt, NamesH.log, GMap.lookup_insert]
      intro he; cases he
  · match o with
    | none => exact h.tmpH
    | some (x, s0, i) =>
      refine h.tmpH.log x _ _ (fun J => ?_)
      simp only [GMap.lookup_insert]
      intro he; cases he

/-- The new candidate's facts, the rename's for both forms. -/
theorem DurOk.ren_common {f : DFile} {s s' : DurSt} {p : DurPhys} (h : DurOk f s p) (c : DCand)
    (a : Option (Option GoString)) (x s0 : Nat) (hc : c.Ok) (hci : c.i ∉ p.cands.map DCand.i)
    (hcur : s'.cur = some c.v) (halt : s'.alt = a) (ha : a ≠ none)
    (hold : ∀ o, OutOk s p.cands o → OutOk s' (p.cands ++ [c]) o) :
    DurOk f s' (renPhys f p c a x s0) := by
  have hmem : c ∈ p.cands ++ [c] := List.mem_append_right _ (List.mem_singleton_self _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, halt, ?_⟩
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
  · refine h.tmpH.log x _ _ (fun J => ?_)
    simp only [GMap.lookup_delete]
    intro he; cases he

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
  refine ⟨?_, h.cur, h.tmp, fun _ => hn, h.cands, h.inj, rfl, h.tmpH⟩
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
