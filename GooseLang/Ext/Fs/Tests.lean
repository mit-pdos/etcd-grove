/-
Behaviours Linux has that the extension's semantics (`Impl.lean`) must contain, as concrete
executions, and a few guarantees it gives: each test exhibits the model's outcome. Untrusted (a
check of the trusted definitions).

* `crash_old_name_new_bytes`: create `t`, write `X`, rename `t` to `a`, write `Y`, crash before the
  rename commits: `t` may hold `Y` (the file's writeback does not wait for the journal).
* `crash_loses_unsynced`: a machine crash may lose a write that was never synced.
* `crash_mix`: a synced page overwritten by one `pwrite` (landed whole, short, or still in flight),
  then a crash: each byte may come back old or new, independently: a new prefix (mechanism A, a
  source page migrated during the copy) or any mix (mechanism B, a page rewritten during its
  writeback), both measured on C (`notes/axiom-review/fs-v2-r6/e2e/`).
* `crash_after_sync` (a guarantee): after a successful sync with nothing in flight, every crash
  leaves the file exactly as it was synced.
* `crash_append_old_block`: an append into the block holding the old end, then a crash: the new
  size may come back with the block's old bytes, stale ones included (`fs-config/crash.sh
  append-end`).
* `crash_new_block_zeros`: a new file's first write, then a crash: the new size may come back with
  zeros where the write was (ext4 commits the unwritten extent first; `crash.sh empty-write`).
* `crash_past_end_zeros` (a guarantee): a file grown past its durable size's last page, then a
  crash: the grown pages read zeros, whatever the disk held past the old end (durable zeros;
  `crash.sh shrink-grow`, `keep-size`).
* `crash_current`: a crash may keep a file as it is, when its page cache is among its candidates
  (`CacheCand`, which `ofDisk`, `announce` and `synced` keep).
* `sectorWhole_durable`: `SectorWhole` is satisfiable: a crash keeping every byte as of the last
  sync is a crash, and leaves every sector as one state of it.
* `crash_overlap`: two overlapping calls in disjoint directories (a rename of the file `a` to `d`,
  and a create in `c/x` begun before the rename took effect): a crash may keep the create without
  the rename.
* `dirsync_new_dir` (a guarantee): after a successful `fsync` of the root, every crash keeps the
  directory made in it during the same run.
* `rmdir_open_fd`: `rmdir` of an empty directory succeeds while an fd is open on it.
-/
module

public import GooseLang.Ext.Fs.Lookup
public import GooseLang.Ext.Fs.Premises
public import Perennial.Golang.Defn.PostLang

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs
namespace Tests

def rootP : GoString := go!"/r"
def tB : GoString := go!"t"
def aB : GoString := go!"a"

def bx : w8 := 1
def byt : w8 := 2

/-- A crash leaving `ofDisk img sz`: a size in range and each byte a candidate. -/
theorem crashFile_of (st : OsState) (i : Ino) (f : OsFile) (img : Nat → w8) (sz : Nat)
    (hlo : f.sizeLo ≤ sz) (hhi : sz ≤ f.sizeHi) (hc : ∀ b, ∃ s, (img b, s) ∈ f.cand b) :
    CrashFile st i f (OsFile.ofDisk img sz) :=
  ⟨sz, img, ⟨.inl hlo, .inl hhi⟩, hc, rfl⟩

/-- Write `c` at offset 0 as the change numbered `n`, announced and landed whole. -/
def wr (f : OsFile) (c : List w8) (n : Nat) : OsFile :=
  (f.announceWrite 0 c n).landWrite 0 c c.length

theorem diskByte_page0 (img : Nat → w8) (sz b : Nat) (hsz : 0 < sz) (hb : b < 4096) :
    diskByte img sz b = img b := by
  simp [diskByte, pageIn, Nat.div_eq_of_lt hb, hsz]

theorem diskByte_past (img : Nat → w8) (sz b : Nat) (h : sz ≤ 4096 * (b / 4096)) :
    diskByte img sz b = 0 := by
  simp [diskByte, pageIn]; omega

theorem diskByte_zero (img : Nat → w8) (b : Nat) : diskByte img 0 b = 0 :=
  diskByte_past img 0 b (Nat.zero_le _)

/-- The durable image of a list's bytes is the list's bytes, zero past its end. -/
theorem diskByte_list (c : List w8) (b : Nat) :
    diskByte (fun b => c.getD b 0) c.length b = c.getD b 0 := by
  unfold diskByte; split
  · rfl
  · rename_i h
    simp only [pageIn, decide_eq_true_eq, Nat.not_lt] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl

theorem written_length (f : OsFile) (off : Nat) (d : List w8) (hd : d ≠ []) :
    (f.written off d).length = max f.size (off + d.length) := by
  simp only [OsFile.written, hd, ite_false, List.length_append, List.length_take,
    List.length_drop, OsFile.resized, List.length_map, List.length_range]
  omega

/-- Writing a page's worth from offset 0 over a file no longer than it gives that page. -/
theorem written_full (f : OsFile) (x : List w8) (hx : x ≠ []) (hle : f.size ≤ x.length) :
    f.written 0 x = x := by
  simp only [OsFile.written, hx, ite_false, Nat.zero_add, List.take_zero, List.nil_append]
  have hl : (f.resized (max f.size x.length)).length = x.length := by
    simp [OsFile.resized]; omega
  rw [List.drop_eq_nil_of_le (by omega), List.append_nil]

theorem landWrite_cand (f : OsFile) (off : Nat) (d : List w8) (k : Nat) :
    (f.landWrite off d k).cand = f.cand := by
  unfold OsFile.landWrite; split <;> rfl

theorem landWrite_sizes (f : OsFile) (off : Nat) (d : List w8) (k : Nat) (hk : 0 < k)
    (hkd : k ≤ d.length) :
    (f.landWrite off d k).size = max f.size (off + k) ∧
    (f.landWrite off d k).sizeLo = min f.sizeLo (max f.size (off + k)) ∧
    (f.landWrite off d k).sizeHi = max f.sizeHi (max f.size (off + k)) := by
  have hne : d.take k ≠ [] := by
    intro h
    rcases List.take_eq_nil_iff.1 h with h | h
    · omega
    · subst h; simp at hkd; omega
  have hlk : (d.take k).length = k := by simp; omega
  have hl := written_length f off (d.take k) hne
  rw [hlk] at hl
  unfold OsFile.landWrite
  rw [if_neg (by omega)]
  exact ⟨by simp [OsFile.change, hl], by simp [OsFile.change, hl], by simp [OsFile.change, hl]⟩

theorem mem_announce_old {f : OsFile} {e : w8 × Nat} {b : Nat} (h : e ∈ f.cand b) (lo hi : Nat)
    (v : Nat → w8) (n : Nat) : e ∈ (f.announce lo hi v n).cand b := by
  simp only [OsFile.announce]; split
  · exact List.mem_append_left _ h
  · exact h

theorem mem_announce_new (f : OsFile) {lo hi b : Nat} (h : inRange lo hi b = true)
    (v : Nat → w8) (n : Nat) : (v b, n) ∈ (f.announce lo hi v n).cand b := by
  simp only [OsFile.announce, h, ite_true]; exact List.mem_append_right _ (by simp)

/-- What a candidate of an announced byte is: one it had, or the announced value. -/
theorem mem_announce {f : OsFile} {lo hi b : Nat} {v : Nat → w8} {n : Nat} {e : w8 × Nat}
    (h : e ∈ (f.announce lo hi v n).cand b) : e ∈ f.cand b ∨ e = (v b, n) := by
  simp only [OsFile.announce] at h; split at h
  · rcases List.mem_append.1 h with h | h
    · exact .inl h
    · exact .inr (by simpa using h)
  · exact .inl h

theorem ofDisk_cand (img : Nat → w8) (sz b : Nat) :
    (OsFile.ofDisk img sz).cand b = [(diskByte img sz b, 0)] := rfl

/-- `wr`: the candidates and sizes, for a file no longer than what is written. -/
theorem wr_facts (f : OsFile) (c : List w8) (n : Nat) (hc : c ≠ []) (hle : f.size ≤ c.length) :
    (∀ b, (b < c.length → (c.getD b 0, n) ∈ (wr f c n).cand b) ∧
      (∀ e, e ∈ f.cand b → e ∈ (wr f c n).cand b)) ∧
    (wr f c n).size = c.length ∧ (wr f c n).sizeLo = min f.sizeLo c.length ∧
    (wr f c n).sizeHi = max f.sizeHi c.length := by
  have hlen : 0 < c.length := List.length_pos_iff.2 hc
  obtain ⟨h1, h2, h3⟩ := landWrite_sizes (f.announceWrite 0 c n) 0 c c.length hlen (Nat.le_refl _)
  have hs : (f.announceWrite 0 c n).size = f.size := rfl
  have hlo : (f.announceWrite 0 c n).sizeLo = f.sizeLo := rfl
  have hhi : (f.announceWrite 0 c n).sizeHi = f.sizeHi := rfl
  refine ⟨fun b => ⟨fun hb => ?_, fun e he => ?_⟩, ?_, ?_, ?_⟩
  · unfold wr; rw [landWrite_cand]; unfold OsFile.announceWrite; rw [written_full f c hc hle]
    exact mem_announce_new f (lo := min 0 f.size) (hi := 0 + c.length) (b := b)
      (by simp [inRange]; omega) (fun b => c.getD b 0) n
  · unfold wr; rw [landWrite_cand]; exact mem_announce_old he _ _ _ _
  · unfold wr; rw [h1, hs]; omega
  · unfold wr; rw [h2, hs, hlo]; omega
  · unfold wr; rw [h3, hs, hhi]; omega

/-- A one-byte file written `X` then `Y` since its creation, never synced. -/
def fXY : OsFile := wr (wr newFile [bx] 1) [byt] 2

theorem fXY_facts : fXY.size = 1 ∧ fXY.sizeLo = 0 ∧ fXY.sizeHi = 1 ∧ (byt, 2) ∈ fXY.cand 0 ∧
    ∀ b, ((0 : w8), 0) ∈ fXY.cand b := by
  obtain ⟨hc1, hs1, hl1, hh1⟩ := wr_facts newFile [bx] 1 (by simp) (by simp [newFile, OsFile.ofBytes, OsFile.ofDisk])
  obtain ⟨hc2, hs2, hl2, hh2⟩ := wr_facts (wr newFile [bx] 1) [byt] 2 (by simp) (by rw [hs1]; simp)
  refine ⟨by rw [fXY, hs2]; rfl, by rw [fXY, hl2, hl1]; rfl, by rw [fXY, hh2, hh1]; rfl,
    by unfold fXY; exact (hc2 0).1 (by simp), fun b => ?_⟩
  unfold fXY
  refine (hc2 b).2 _ ((hc1 b).2 _ ?_)
  simp [newFile, OsFile.ofBytes, ofDisk_cand, diskByte_zero]

/-- Before the crash: the file of inode 0 created as `t` in the root (inode 1), renamed to `a`,
neither committed. -/
def stOld : OsState :=
  { fs := { roots := [(rootP, 1)], treeDur := {[1 := ∅]},
            metaLog := [⟨.create 1 tB 0, 0⟩, ⟨.rename 1 tB 1 aB (.file 0) none, 1⟩],
            committed := fun _ => False, files := {[0 := fXY]}, nextIno := 2, stamp := 2 },
    proc := ProcState.empty }

/-- After: the crash kept the create, not the rename; `t` holds `Y`. -/
def stNew : OsState :=
  { fs := { roots := [(rootP, 1)], treeDur := replay [.create 1 tB 0] {[1 := ∅]},
            metaLog := [], committed := fun _ => False, files := {[0 := OsFile.ofBytes [byt]]},
            nextIno := 2, stamp := 2 },
    proc := ProcState.empty }

theorem entry_new (j : Ino) (b : GoString) :
    stNew.fs.treeDur.entry j b = if j = 1 ∧ b = tB then some (.file 0) else none := by
  simp only [stNew, replay, List.foldl, MetaOp.apply, Tree.upd, Tree.entry]
  by_cases hj : j = 1
  · subst hj; by_cases hb : b = tB
    · subst hb; simp
    · simp [hb, Ne.symm hb]
  · simp [hj, Ne.symm hj]

theorem named_new (i : Ino) : Named stNew.fs.treeDur i ↔ i = 0 := by
  constructor
  · rintro ⟨j, b, h⟩
    rw [entry_new] at h; split at h
    · cases h; rfl
    · cases h
  · rintro rfl; exact ⟨1, tB, by rw [entry_new]; simp⟩

theorem keptOps_first :
    keptOps stOld.fs.metaLog (fun x => x = 0) = [.create 1 tB 0] := by
  simp [keptOps, stOld, List.range_succ]

theorem closed_first : Closed stOld.fs.metaLog (fun x => x = 0) := by
  intro x y hx hf; subst hx; exact absurd hf.1 (Nat.not_lt_zero _)

/-- **A crash may keep the old name with the new bytes.** -/
theorem crash_old_name_new_bytes : OsCrash stOld stNew := by
  refine ⟨rfl, rfl, rfl, fun _ h => h, rfl, rfl,
    ⟨fun x => x = 0, fun x hx => by simp [hx, stOld], fun _ h => h.elim, closed_first,
      by rw [keptOps_first]; rfl⟩, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · obtain rfl := (named_new i).1 hi
    obtain ⟨hs, hlo, hhi, hc0, hcb⟩ := fXY_facts
    refine ⟨fXY, OsFile.ofBytes [byt], by simp [stOld], ?_, by simp [stNew]⟩
    refine crashFile_of _ _ _ _ _ (by simp [OsFile.ofBytes]; omega)
      (by simp [OsFile.ofBytes]; omega) (fun b => ?_)
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact ⟨2, hc0⟩
    · refine ⟨0, ?_⟩
      have : [byt].getD b 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
      rw [this]; exact hcb b
  · have : i ≠ 0 := fun h => hi ((named_new i).2 h)
    simp [stNew, Ne.symm this]

/-! ## Crashes of one file -/

/-- One synced page `o` of a file, overwritten by `x` as change `n`, of which `k` bytes landed:
all of it, a short write, or none yet (the write still in flight). -/
def fMix (o x : List w8) (n k : Nat) : OsFile :=
  ((OsFile.ofBytes o).announceWrite 0 x n).landWrite 0 x k

/-- **A crash may leave any byte-wise mix of the old page and the new one** (mechanisms A and B, a
short write, a write in flight): each byte of the page old or new, the rest of the file zeros. -/
theorem crash_mix (st : OsState) (i : Ino) (o x : List w8) (ho : o.length = 4096)
    (hx : x.length = 4096) (n k : Nat) (hk : k ≤ 4096) (img : Nat → w8)
    (himg : ∀ b, (b < 4096 → img b = o.getD b 0 ∨ img b = x.getD b 0) ∧
      (4096 ≤ b → img b = 0)) :
    CrashFile st i (fMix o x n k) (OsFile.ofDisk img 4096) := by
  have hxne : x ≠ [] := by intro h; simp [h] at hx
  have hs0 : (OsFile.ofBytes o).size = 4096 := ho
  have hsz : (fMix o x n k).sizeLo = 4096 ∧ (fMix o x n k).sizeHi = 4096 := by
    unfold fMix
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [OsFile.landWrite, ite_true]
      exact ⟨ho, ho⟩
    · obtain ⟨-, h2, h3⟩ := landWrite_sizes ((OsFile.ofBytes o).announceWrite 0 x n) 0 x k hk0
        (by omega)
      have hs : ((OsFile.ofBytes o).announceWrite 0 x n).size = 4096 := ho
      have hl : ((OsFile.ofBytes o).announceWrite 0 x n).sizeLo = 4096 := ho
      have hh : ((OsFile.ofBytes o).announceWrite 0 x n).sizeHi = 4096 := ho
      rw [h2, h3, hs, hl, hh]; omega
  refine crashFile_of _ _ _ _ _ (by omega) (by omega) (fun b => ?_)
  unfold fMix; rw [landWrite_cand]
  obtain ⟨hlt, hge⟩ := himg b
  have hbase : (diskByte (fun b => o.getD b 0) o.length b, 0) ∈ (OsFile.ofBytes o).cand b := by
    simp [OsFile.ofBytes, ofDisk_cand]
  rw [diskByte_list] at hbase
  by_cases hb : b < 4096
  · rcases hlt hb with h | h
    · exact ⟨0, by rw [h]; exact mem_announce_old hbase _ _ _ _⟩
    · refine ⟨n, ?_⟩
      unfold OsFile.announceWrite; rw [written_full _ x hxne (by omega), h]
      exact mem_announce_new (OsFile.ofBytes o) (lo := min 0 (OsFile.ofBytes o).size)
        (hi := 0 + x.length) (b := b) (by simp [inRange]; omega) (fun b => x.getD b 0) n
  · refine ⟨0, ?_⟩
    have h0 : o.getD b 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [hge (by omega), ← h0]; exact mem_announce_old hbase _ _ _ _

/-- **A machine crash may lose a write that was never synced**: `Y` written over `X`, no sync;
a crash may leave `X`. -/
theorem crash_loses_unsynced (st : OsState) (i : Ino) :
    CrashFile st i (wr (OsFile.ofBytes [bx]) [byt] 1) (OsFile.ofBytes [bx]) := by
  obtain ⟨hc, -, hl, hh⟩ := wr_facts (OsFile.ofBytes [bx]) [byt] 1 (by simp) (by simp [OsFile.ofBytes, OsFile.ofDisk])
  refine crashFile_of _ _ _ _ _ (by rw [hl]; simp [OsFile.ofBytes, OsFile.ofDisk])
    (by rw [hh]; simp [OsFile.ofBytes, OsFile.ofDisk]) (fun b => ⟨0, (hc b).2 _ ?_⟩)
  show _ ∈ [(diskByte (fun b => [bx].getD b 0) [bx].length b, 0)]
  rw [diskByte_list]; exact List.mem_singleton_self _

/-- **After a successful sync, a crash leaves the file exactly as synced** (a guarantee, with no
change in flight on it). -/
theorem crash_after_sync (st : OsState) (i : Ino) (f f' : OsFile)
    (hnone : ∀ t c, st.proc.inflight !! t = some c → c.ino ≠ i)
    (hc : CrashFile st i (f.synced (fun _ => False)) f') :
    f' = OsFile.ofDisk f.cache f.size := by
  obtain ⟨sz, img, ⟨hlo, hhi⟩, himg, rfl⟩ := hc
  have hsz : sz = f.size := by
    rcases hlo with h | ⟨t, c, ht, hi, -⟩
    · rcases hhi with h' | ⟨t, c, ht, hi, -⟩
      · simp only [OsFile.synced] at h h'; omega
      · exact absurd hi (hnone t c ht)
    · exact absurd hi (hnone t c ht)
  subst hsz
  have hi : ∀ b, img b = diskByte f.cache f.size b := by
    intro b; obtain ⟨s, h⟩ := himg b; simp [OsFile.synced] at h; exact h.1
  have hd : ∀ b, diskByte img f.size b = diskByte f.cache f.size b := by
    intro b; unfold diskByte; split
    · rw [hi b, diskByte, if_pos (by assumption)]
    · rfl
  simp only [OsFile.ofDisk]
  congr 1
  · funext b; exact hd b
  · funext b; rw [hd b]

/-- A one-byte file as a crash may find it on disk, its bytes `img` (stale past its end), `Y`
appended at 1 as change `n`. -/
def fApp (img : Nat → w8) (n : Nat) : OsFile :=
  ((OsFile.ofDisk img 1).announceWrite 1 [byt] n).landWrite 1 [byt] 1

/-- **An append into the block holding the old end is not ordered**: a crash may keep the new size
with the block's old bytes, the stale one included. -/
theorem crash_append_old_block (st : OsState) (i : Ino) (img : Nat → w8) (n : Nat)
    (hz : ∀ b, 4096 ≤ b → img b = 0) :
    CrashFile st i (fApp img n) (OsFile.ofDisk img 2) := by
  obtain ⟨-, h2, h3⟩ := landWrite_sizes ((OsFile.ofDisk img 1).announceWrite 1 [byt] n) 1 [byt] 1
    (by omega) (by simp)
  have hs : ((OsFile.ofDisk img 1).announceWrite 1 [byt] n).size = 1 := rfl
  have hl : ((OsFile.ofDisk img 1).announceWrite 1 [byt] n).sizeLo = 1 := rfl
  have hh : ((OsFile.ofDisk img 1).announceWrite 1 [byt] n).sizeHi = 1 := rfl
  refine crashFile_of _ _ _ _ _ (by unfold fApp; rw [h2, hs, hl]; omega)
    (by unfold fApp; rw [h3, hs, hh]; omega) (fun b => ⟨0, ?_⟩)
  unfold fApp; rw [landWrite_cand]
  have hv : diskByte img 1 b = img b := by
    by_cases hb : b < 4096
    · exact diskByte_page0 img 1 b (by omega) hb
    · rw [diskByte_past img 1 b (by omega), hz b (by omega)]
  refine mem_announce_old ?_ _ _ _ _
  rw [ofDisk_cand, hv]; simp

/-- **A new block may come back as zeros under the size that covers it** (ext4 with
`dioread_nolock` commits the unwritten extent with the size before the data). -/
theorem crash_new_block_zeros (st : OsState) (i : Ino) (n : Nat) :
    CrashFile st i (wr (OsFile.ofBytes []) [byt] n) (OsFile.ofDisk (fun _ => 0) 1) := by
  obtain ⟨hc, -, hl, hh⟩ := wr_facts (OsFile.ofBytes []) [byt] n (by simp) (by simp [OsFile.ofBytes, OsFile.ofDisk])
  refine crashFile_of _ _ _ _ _ (by rw [hl]; simp [OsFile.ofBytes, OsFile.ofDisk])
    (by rw [hh]; simp [OsFile.ofBytes, OsFile.ofDisk]) (fun b => ⟨0, (hc b).2 _ ?_⟩)
  simp [OsFile.ofBytes, ofDisk_cand, diskByte_zero]

/-- A file of size 1 as a crash may find it on disk, its bytes `img` (stale past its end), grown
to 8192 bytes as change `n`. -/
def fGrow (img : Nat → w8) (n : Nat) : OsFile :=
  ((OsFile.ofDisk img 1).announceResize 8192 n).truncate 8192

/-- **Durable zeros** (a guarantee): after the file is grown past its durable size's last page, a
crash leaves the grown pages zeros, whatever the disk held past the old end. -/
theorem crash_past_end_zeros (st : OsState) (i : Ino) (img : Nat → w8) (n : Nat) (f' : OsFile)
    (hc : CrashFile st i (fGrow img n) f') (b : Nat) (hb : 4096 ≤ b) : f'.cache b = 0 := by
  obtain ⟨sz, img', -, himg, rfl⟩ := hc
  obtain ⟨s, h⟩ := himg b
  have hcand : (fGrow img n).cand b = ((OsFile.ofDisk img 1).announceResize 8192 n).cand b := rfl
  rw [hcand] at h
  have hv : img' b = 0 := by
    rcases mem_announce h with h | h
    · rw [ofDisk_cand, diskByte_past img 1 b (by omega)] at h
      simp at h; exact h.1
    · exact (Prod.mk.inj h).1
  simp only [OsFile.ofDisk, diskByte, hv]; split <;> rfl

/-- The page cache is among the candidates, byte by byte, and the size in its range. -/
def CacheCand (f : OsFile) : Prop :=
  (∀ b, ∃ s, (f.cache b, s) ∈ f.cand b) ∧ f.sizeLo ≤ f.size ∧ f.size ≤ f.sizeHi

/-- **A crash may keep a file as it is** (its page cache and size; the pages past the size zeros):
the crash rule never leaves a file without a crash. -/
theorem crash_current (st : OsState) (i : Ino) (f : OsFile) (hok : CacheCand f) :
    CrashFile st i f (OsFile.ofDisk f.cache f.size) :=
  crashFile_of _ _ _ _ _ hok.2.1 hok.2.2 hok.1

theorem cacheCand_ofDisk (img : Nat → w8) (sz : Nat) : CacheCand (OsFile.ofDisk img sz) :=
  ⟨fun b => ⟨0, by simp [OsFile.ofDisk]⟩, Nat.le_refl _, Nat.le_refl _⟩

theorem cacheCand_announce {f : OsFile} (hok : CacheCand f) (lo hi : Nat) (v : Nat → w8)
    (n : Nat) : CacheCand (f.announce lo hi v n) := by
  refine ⟨fun b => ?_, hok.2.1, hok.2.2⟩
  obtain ⟨s, h⟩ := hok.1 b
  refine ⟨s, ?_⟩
  simp only [OsFile.announce]; split
  · exact List.mem_append_left _ h
  · exact h

theorem cacheCand_synced {f : OsFile} (hok : CacheCand f) (busy : Nat → Prop)
    [DecidablePred busy] : CacheCand (f.synced busy) := by
  refine ⟨fun b => ?_, by simp [OsFile.synced], by simp [OsFile.synced]⟩
  simp only [OsFile.synced]; split
  · exact hok.1 b
  · exact ⟨0, by simp⟩

/-- `valAt l 0` is a candidate, when `l` has one stamped 0. -/
theorem valAt_mem (l : Cands) (h : ∃ v, (v, 0) ∈ l) : ∃ s, (valAt l 0, s) ∈ l := by
  obtain ⟨v, hv⟩ := h
  have hne : l.filter (·.2 ≤ 0) ≠ [] := by
    intro he
    have : (v, 0) ∈ l.filter (·.2 ≤ 0) := List.mem_filter.2 ⟨hv, by simp⟩
    rw [he] at this; simp at this
  obtain ⟨e, he⟩ : ∃ e, (l.filter (·.2 ≤ 0)).getLast? = some e := by
    cases hl : (l.filter (·.2 ≤ 0)).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 hl) hne
    | some e => exact ⟨e, rfl⟩
  have hm : e ∈ l := (List.mem_filter.1 (List.mem_of_getLast? he)).1
  have hv : valAt l 0 = e.1 := by simp only [valAt, he, Option.map_some, Option.getD_some]
  exact ⟨e.2, by rw [hv]; exact hm⟩

/-- **`SectorWhole` is satisfiable**: the crash that keeps every byte as of the last sync (its
candidate stamped 0), at the smallest size since, is a crash, and leaves each sector below its size
the state as of change 0. -/
theorem sectorWhole_durable (st : OsState) (i : Ino) (f : OsFile) (hsz : f.sizeLo ≤ f.sizeHi)
    (h0 : ∀ b, ∃ v, (v, 0) ∈ f.cand b) :
    CrashFile st i f (OsFile.ofDisk (fun b => valAt (f.cand b) 0) f.sizeLo) ∧
    ∀ n, 512 * n < (OsFile.ofDisk (fun b => valAt (f.cand b) 0) f.sizeLo).size → ∀ j < 512,
      (OsFile.ofDisk (fun b => valAt (f.cand b) 0) f.sizeLo).cache (512 * n + j) =
        valAt (f.cand (512 * n + j)) 0 := by
  refine ⟨crashFile_of _ _ _ _ _ (Nat.le_refl _) hsz (fun b => valAt_mem _ (h0 b)),
    fun n hn j hj => ?_⟩
  simp only [OsFile.ofDisk] at hn ⊢
  rw [diskByte, if_pos]
  simp only [pageIn, decide_eq_true_eq]
  have h1 : (512 * n + j) / 4096 = (512 * n) / 4096 := by omega
  have h2 : 4096 * ((512 * n) / 4096) ≤ 512 * n := Nat.mul_div_le _ _
  rw [h1]; omega

/-! ## The directory tree -/

def cB : GoString := go!"c"
def dB : GoString := go!"d"
def xB : GoString := go!"x"
def yB : GoString := go!"y"

/-- `/r/a`, a file (inode 7); `/r/c/x`, directories 4 and 5. -/
def tree3 : Tree :=
  <[1 := <[aB := .file 7]> {[cB := .dir 4]}]> (<[4 := {[xB := .dir 5]}]> {[5 := ∅]})

/-- Two overlapping calls: the rename of the file `a` to `d` took effect first; the create of `y` in
`/r/c/x` had begun before it did. -/
def stOv : OsState :=
  { fs := { roots := [(rootP, 1)], treeDur := tree3,
            metaLog := [⟨.rename 1 aB 1 dB (.file 7) none, 0⟩, ⟨.create 5 yB 6, 0⟩],
            committed := fun _ => False, files := <[6 := newFile]> {[7 := newFile]}, nextIno := 8, stamp := 0 },
    proc := ProcState.empty }

/-- After a crash that kept the create but not the rename. -/
def stOv' : OsState :=
  { fs := { roots := [(rootP, 1)], treeDur := replay [.create 5 yB 6] tree3,
            metaLog := [], committed := fun _ => False,
            files := <[6 := OsFile.ofBytes []]> {[7 := OsFile.ofBytes []]}, nextIno := 8, stamp := 0 },
    proc := ProcState.empty }

theorem named_ov (i : Ino) : Named stOv'.fs.treeDur i ↔ i = 6 ∨ i = 7 := by
  constructor
  · rintro ⟨j, b, h⟩
    simp [stOv', tree3, replay, MetaOp.apply, Tree.upd, Tree.entry] at h
    by_cases h5 : 5 = j
    · simp [h5] at h
      by_cases hb : yB = b
      · simp [hb] at h; exact .inl h.symm
      · simp [hb] at h
    · simp [h5] at h
      by_cases h1 : 1 = j
      · simp [h1] at h
        by_cases hb : aB = b
        · simp [hb] at h; exact .inr h.symm
        · simp [hb] at h
      · simp [h1] at h
        by_cases h4 : 4 = j
        · simp [h4] at h
        · simp [h4] at h
  · rintro (rfl | rfl)
    · exact ⟨5, yB, by simp [stOv', tree3, replay, MetaOp.apply, Tree.upd, Tree.entry]⟩
    · exact ⟨1, aB, by simp [stOv', tree3, replay, MetaOp.apply, Tree.upd, Tree.entry]⟩

/-- **Overlapping calls in disjoint directories**: a crash may keep the create in `/r/c/x` without
the rename of `/r/a` that took effect before it (the create's call began before the rename took
effect, so the journal may have either first). -/
theorem crash_overlap : OsCrash stOv stOv' := by
  refine ⟨rfl, rfl, rfl, fun _ h => h, rfl, rfl,
    ⟨fun x => x = 1, fun x hx => by simp [hx, stOv], fun _ h => h.elim, ?_, ?_⟩,
    fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · intro x y hx hf; subst hx
    obtain ⟨hy, ex, hex, h⟩ := hf
    have : y = 0 := by omega
    subst this
    simp [stOv] at hex; subst hex
    simp at h
  · simp [keptOps, stOv, List.range_succ]; rfl
  · have hf : ∃ f, stOv.fs.files !! i = some f ∧ f = newFile ∧
        stOv'.fs.files !! i = some (OsFile.ofBytes []) := by
      rcases (named_ov i).1 hi with rfl | rfl <;> exact ⟨newFile, by simp [stOv, stOv']⟩
    obtain ⟨f, hfi, rfl, hfi'⟩ := hf
    exact ⟨newFile, OsFile.ofBytes [], hfi,
      crashFile_of _ _ _ _ _ (Nat.le_refl _) (Nat.le_refl _) (fun b => ⟨0, by
        simp [newFile, OsFile.ofBytes, OsFile.ofDisk, diskByte_zero]⟩), hfi'⟩
  · have h6 : i ≠ 6 := fun h => hi ((named_ov i).2 (.inl h))
    have h7 : i ≠ 7 := fun h => hi ((named_ov i).2 (.inr h))
    simp [stOv', Ne.symm h6, Ne.symm h7]

/-! ## A directory's `fsync` makes a directory made in the same run durable -/

/-- `m` made in the root (inode 2); a directory fd 3 on the root. -/
def stMk : OsState :=
  { fs := { roots := [(rootP, 1)], treeDur := {[1 := ∅]}, metaLog := [⟨.mkdir 1 go!"m" 2, 0⟩],
            committed := fun _ => False, files := ∅, nextIno := 3, stamp := 0 },
    proc := { ProcState.empty with dfds := {[W64 3 := ⟨1, .idle⟩]} } }

/-- **After the root's `fsync` succeeds, every crash keeps `m`.** -/
theorem dirsync_new_dir [GooseExts] [GoGlobalContext] [go.BasicIntoValInj] (st' st'' : OsState) (e' : Expr)
    (hs : IsFsStep "DirSync" (#(W64 3)) stMk e' st') (he : e' = Val (#(0 : w64)))
    (hc : MachineCrash st' st'') : st''.fs.treeDur.entry 1 go!"m" = some (.dir 2) := by
  obtain ⟨fd, df, hv, hdf, hr⟩ := hs
  have hfd : fd = W64 3 := by
    have := go.intoVal_inj hv; exact this.symm
  subst hfd
  simp [stMk] at hdf; subst hdf
  rcases hr with ⟨rfl, -⟩ | ⟨e, he0, rfl, -⟩
  · obtain ⟨-, -, -, -, -, -, ⟨S, hlt, hS, -, htr⟩, -⟩ := hc
    have h0 : S 0 := hS 0 (.inr (by simp [stMk]))
    have hk : keptOps stMk.fs.metaLog S = [.mkdir 1 go!"m" 2] := by
      simp [keptOps, stMk, h0]
    simp only [OsState.commitAll] at htr
    rw [htr, hk]
    simp [replay, MetaOp.apply, Tree.upd, Tree.entry, stMk]
  · exact absurd (go.intoVal_inj (by simpa using he)) he0

/-! ## `rmdir` of a directory with an open fd -/

/-- `m`, an empty directory (inode 2) in the root, with a directory fd 3 on it, and a metadata call
(token 0) begun. -/
def stRm : OsState :=
  { fs := { roots := [(rootP, 1)], treeDur := <[1 := {[go!"m" := .dir 2]}]> {[2 := ∅]},
            metaLog := [], committed := fun _ => False, files := ∅, nextIno := 3, stamp := 0 },
    proc := { ProcState.empty with dfds := {[W64 3 := ⟨2, .idle⟩]}, calls := {[0 := 0]} } }

/-- **`rmdir` succeeds although an fd is open on the directory** (the fd keeps it, empty). -/
theorem rmdir_open_fd [GooseExts] [GoGlobalContext] :
    ∃ st' e', IsFsStep "Rmdir" (PairV (osTokV 0) (#(go!"/r/m"))) stRm e' st' := by
  have hp : (go!"/r/m" : GoString) = joinPath rootP [go!"m"] := rfl
  have hr : (go!"/r" : GoString) = joinPath rootP [] := rfl
  have hl : stRm.lookup (go!"/r/m") = some (.dir 2) := by
    rw [hp, lookup_one (r := rootP) (j := 1) rfl (by decide)]
    simp [walk, stRm, OsState.tree, replay, Tree.entry]
  have hl0 : stRm.lookup (go!"/r") = some (.dir 1) := by
    rw [hr, lookup_one (r := rootP) (j := 1) rfl (by decide)]; rfl
  have hpar : stRm.parent (go!"/r/m") = some (1, go!"m") := by
    unfold OsState.parent
    rw [show parentOf (go!"/r/m") = some (go!"/r") by decide]
    dsimp only
    rw [hl0]
    rfl
  refine ⟨_, _, go!"/r/m", 0, 0, rfl, ⟨(rootP, 1), by simp [stRm], [go!"m"], by simp, by decide, hp⟩,
    by simp [stRm], .inl ⟨2, 1, go!"m", ⟨hl, fun b => ?_⟩, hpar, .inl ⟨rfl, rfl⟩⟩⟩
  simp [stRm, OsState.tree, replay, Tree.entry]

end Tests
end Fs
end Perennial

end
