/- Lean-first (no Rocq counterpart).

# The fresh WAL directory's claim (W4, `notes/wal-fsext-plan.md`, "W4 implementation log", eighteenth
session; pure)

`Create`'s directory `J`: `CreateDirAll` returns its whole claim with no name at any crash
(`valAfter … = none`, `fileutil.CreateDirAll.specTmp`'s post), then `createNewWALFile` logs the segment's
create at `w0` (`crOut`). The claim merged back (`osNames_merge`'s restrictions):

* `createJ_val`/`createJ_cur`: at any crash a name of `J` holds nothing, or the segment's file at `w0`;
  now exactly the segment at `w0`.
* `createJ_segsNamed`, `createJ_segsNamedC`, `createJ_walInos`: `walCreate_osAUnc`'s `hsn`, `hJC` and the
  layout's `.wal` entries (`createLay_abs`'s `hents`) for the claim off the pipeline's names.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateKeys
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutCommitPure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDrop
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutCrash
public import LinuxFs.Spec.os.OpenFileS
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutRen

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

section pure
variable [GooseExts]

/-- **A claim restricted to names `M` holds nothing at the others**, at any crash. -/
theorem valAfter_restrict_not (h : NamesH) (j : Ino) (M : NameSet) (K : Nat → Prop) (b : GoString)
    (hb : ¬ M.Mem b) : (h.restrict j M).valAfter j K b = none := by
  classical
  unfold NamesH.valAfter
  split
  · rename_i xe hxe
    have hm := List.mem_of_getLast? hxe
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 (List.mem_filter.1 hm).1
    exact restrictN_lookup_not _ _ _ hb
  · exact restrictN_lookup_not _ _ _ hb

/-- The segment's create writes its name. -/
theorem crEnt_writes (J : Ino) (b : GoString) (i : Ino) (s : Nat) : (crEnt J b i s).op.Writes J b := by
  left; simp [crEnt, MetaOp.slots]

/-- The history `crOut … (some (x, s, i))` gives the segment's name in `J`'s claim. -/
abbrev crH (hJ : NamesH) (J : Ino) (w0 : GoString) (x s : Nat) (i : Ino) : NamesH :=
  (hJ.restrict J ((NameSet.except []).inter [w0])).log x (crEnt J w0 i s)
    (<[w0 := .file i]> (hJ.restrict J ((NameSet.except []).inter [w0])).cur)

/-- **At any crash of the merged claim, a name holds nothing or the segment's file at `w0`.** -/
theorem createJ_val {hJ hJ' : NamesH} {J : Ino} {w0 : GoString} {x s : Nat} {i : Ino}
    (hfr : ∀ (K : Nat → Prop) (b : GoString), hJ.valAfter J K b = none)
    (hA : hJ'.restrict J ((NameSet.except []).diff [w0]) =
      hJ.restrict J ((NameSet.except []).diff [w0]))
    (hB : hJ'.restrict J (.only [w0]) = (crH hJ J w0 x s i).restrict J (.only [w0]))
    (K : Nat → Prop) (b : GoString) :
    hJ'.valAfter J K b = none ∨ (b = w0 ∧ hJ'.valAfter J K b = some (.file i)) := by
  by_cases hb : b = w0
  · subst hb
    have hm : (NameSet.only [b]).Mem b := by simp [NameSet.Mem]
    rw [← valAfter_restrict hJ' J _ K b hm, hB, valAfter_restrict _ J _ K b hm]
    by_cases hK : K x
    · right
      refine ⟨rfl, ?_⟩
      rw [valAfter_log_last _ J K b x _ _ hK (crEnt_writes J b i s)]
      simp
    · left
      rw [valAfter_log_notKept _ J K b x _ _ hK,
        valAfter_restrict _ J _ K b ((NameSet.mem_inter _ _ _).2 ⟨by simp [NameSet.Mem], by simp⟩)]
      exact hfr K b
  · left
    have hm : ((NameSet.except []).diff [w0]).Mem b := by
      rw [NameSet.mem_diff]; simp [NameSet.Mem, hb]
    rw [← valAfter_restrict hJ' J _ K b hm, hA, valAfter_restrict _ J _ K b hm]
    exact hfr K b

/-- **Now, the merged claim holds exactly the segment at `w0`.** -/
theorem createJ_cur {hJ hJ' : NamesH} {J : Ino} {w0 : GoString} {x s : Nat} {i : Ino}
    (hJe : hJ.cur = ∅)
    (hA : hJ'.restrict J ((NameSet.except []).diff [w0]) =
      hJ.restrict J ((NameSet.except []).diff [w0]))
    (hB : hJ'.restrict J (.only [w0]) = (crH hJ J w0 x s i).restrict J (.only [w0]))
    (b : GoString) : hJ'.cur !! b = if b = w0 then some (.file i) else none := by
  by_cases hb : b = w0
  · subst hb
    have hm : (NameSet.only [b]).Mem b := by simp [NameSet.Mem]
    have := congrArg (fun h : NamesH => h.cur !! b) hB
    simp only [NamesH.restrict] at this
    rw [restrictN_lookup _ _ _ hm, restrictN_lookup _ _ _ hm] at this
    rw [this]; simp [NamesH.log]
  · have hm : ((NameSet.except []).diff [w0]).Mem b := by
      rw [NameSet.mem_diff]; simp [NameSet.Mem, hb]
    have := congrArg (fun h : NamesH => h.cur !! b) hA
    simp only [NamesH.restrict] at this
    rw [restrictN_lookup _ _ _ hm, restrictN_lookup _ _ _ hm, hJe] at this
    rw [this, if_neg hb]; rfl

/-- A `.wal` name is a name of the claim off the pipeline's names. -/
theorem mem_diff_walTmps {b : GoString} (hb : walNameP b = true) :
    ((NameSet.except []).diff walTmps).Mem b := by
  rw [NameSet.mem_diff]
  refine ⟨by simp [NameSet.Mem], fun hbt => ?_⟩
  rw [walTmps_not_wal b hbt] at hb; cases hb

section segs
variable {hJ' : NamesH} {J : Ino} {g : SegG}

/-- **`hsn`**: the segment at its name in the claim off the pipeline's names. -/
theorem createJ_segsNamed (hg : g.name = walFileName 0 0)
    (hcur : ∀ b, hJ'.cur !! b = if b = g.name then some (.file g.ino) else none) :
    SegsNamed [g] (hJ'.restrict J ((NameSet.except []).diff walTmps)).cur := by
  have hw : walNameP g.name = true := by rw [hg]; exact walNameP_walFileName 0 0
  refine ⟨fun g' hg' => ?_, fun b e hb he => ?_⟩
  · simp only [List.mem_singleton] at hg'; subst hg'
    refine ⟨hw, ?_⟩
    simp only [NamesH.restrict]
    rw [restrictN_lookup _ _ _ (mem_diff_walTmps hw), hcur]; simp
  · simp only [NamesH.restrict] at he
    rw [restrictN_lookup _ _ _ (mem_diff_walTmps hb), hcur] at he
    split at he
    · cases he; exact ⟨_, rfl⟩
    · cases he

/-- **`hJC`**: after any crash of the claim off the pipeline's names, the only `.wal` file is the
segment's, at its name. -/
theorem createJ_segsNamedC
    (hval : ∀ (K : Nat → Prop) (b : GoString),
      hJ'.valAfter J K b = none ∨ (b = g.name ∧ hJ'.valAfter J K b = some (.file g.ino)))
    (hw : walNameP g.name = true) (K : Nat → Prop) (E : Ents)
    (hE : ∀ b, walNameP b = true →
      E !! b = (hJ'.restrict J ((NameSet.except []).diff walTmps)).valAfter J K b) :
    SegsNamedC [g] E := by
  have hE' : ∀ b, walNameP b = true → E !! b = none ∨ (b = g.name ∧ E !! b = some (.file g.ino)) := by
    intro b hb
    rw [hE b hb, valAfter_restrict _ J _ K b (mem_diff_walTmps hb)]
    exact hval K b
  refine ⟨fun g' hg' => ?_, fun b e hb he => ?_, fun i hi => ?_⟩
  · simp only [List.mem_singleton] at hg'; subst hg'
    refine ⟨hw, fun hi => ?_⟩
    obtain ⟨b, hb, hbe⟩ := walInos_mem hi
    rcases hE' b hb with h | ⟨rfl, h⟩
    · rw [h] at hbe; cases hbe
    · exact h
  · rcases hE' b hb with h | ⟨-, h⟩
    · rw [h] at he; cases he
    · rw [h] at he; cases he; exact ⟨_, rfl⟩
  · obtain ⟨b, hb, hbe⟩ := walInos_mem hi
    rcases hE' b hb with h | ⟨-, h⟩
    · rw [h] at hbe; cases hbe
    · rw [h] at hbe; cases hbe; simp

/-- **The claim's `.wal` entries are the segment's file** (`createLay_abs`'s `hents`). -/
theorem createJ_walInos (hw : walNameP g.name = true)
    (hcur : ∀ b, hJ'.cur !! b = if b = g.name then some (.file g.ino) else none) :
    walInos (hJ'.restrict J ((NameSet.except []).diff walTmps)).cur = [g.ino] := by
  have e : walInos (hJ'.restrict J ((NameSet.except []).diff walTmps)).cur =
      walInos (<[g.name := Node.file g.ino]> (∅ : Ents)) := by
    apply walInos_congr
    intro b hb
    simp only [NamesH.restrict]
    rw [restrictN_lookup _ _ _ (mem_diff_walTmps hb), hcur]
    by_cases hbg : b = g.name
    · subst hbg; simp
    · rw [if_neg hbg, GMap.lookup_insert_ne _ _ (Ne.symm hbg)]; rfl
  have h0 : walInos (∅ : Ents) = [] := List.eq_nil_iff_forall_not_mem.2 (fun i hi => by
    obtain ⟨b, -, hb⟩ := walInos_mem hi; simp at hb)
  rw [e, walInos_insert_last hw (by rfl) (fun b e' _ he => by simp at he), h0]
  rfl

end segs

end pure

end WalFs
end EtcdGrove
end Perennial
