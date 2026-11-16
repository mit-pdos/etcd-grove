/- Lean-first (no Rocq counterpart).

# W1 with a removed segment put back (unit `locks`, session 8; `notes/wal-units/locks.md`)

Pure. A crash that keeps a purge's removal of the first named segment `g0` is, with `g0`'s name set back,
a crash of the claims before it (`regionCrashedK_keptSet`), so the old crash condition applies there,
given W1 over the crashed directory's `.wal` files **with `g0`'s file in front** (`W1G`). The crash gives W1
over the files without it. `w1G_cons_durable` closes the gap: `g0` is intact and durable, so its frames are
as of the last sync, and a reader that starts at `g0` reaches the next file at some CRC; that file starts
with a CRC record (`intact_head`, `tail_head`: every segment's first record is its CRC record, and a crash
keeps it, durable below the least crash size), which a fresh reader does not check and which a chained
reader either rejects or accepts with the same result (`decStep_c_of_crc0`), so the chained reader accepts
in the later files only frames a fresh reader from the next file accepts (`acceptsFiles_sub_crc0`), which
the crash's W1 covers.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.TailCrash
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PurgeCrash
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PurgeRegion

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Fs WalEnc go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-! ## The reader at another CRC -/

/-- A CRC record a fresh reader accepts is, at any CRC, accepted with the same result or rejected. -/
theorem decStep_c_of_crc0 {C : WalCodec} {last : Bool} {bs : List w8} {off : Nat}
    {r : WalRec} {len : Nat} {c0 : w32} (c : w32) (ht : r.typ = crcType)
    (h : decStep C last bs off 0#32 = .accept r len c0) :
    decStep C last bs off c = .accept r len c0 ∨ decStep C last bs off c = .stop .crcRec := by
  unfold decStep at h ⊢
  simp only at h ⊢
  split at h; · cases h
  rename_i h1; rw [ite_eq_right h1]
  split at h; · cases h
  rename_i h2; rw [ite_eq_right h2]
  split at h; · cases h
  rename_i h3; rw [ite_eq_right h3]
  split at h; · cases h
  rename_i h4; rw [ite_eq_right h4]
  split at h; · cases h
  rename_i h5; rw [ite_eq_right h5]
  split at h
  · cases h
  · rename_i r' hr'
    split at h
    · split at h
      · injection h with e1 e2 e3; subst e1; exact absurd ht (by assumption)
      · cases h
    · rename_i hty
      rw [ite_eq_right hty]
      split at h
      · rename_i hc; exact absurd rfl hc.1
      · injection h with e1 e2 e3
        subst e1 e2 e3
        by_cases hc : c ≠ 0#32 ∧ r'.crc ≠ c
        · right; rw [ite_eq_left hc]
        · left; rw [ite_eq_right hc]

/-- **A chained reader of files whose first record is a CRC record accepts only what a fresh one does.** -/
theorem acceptsFiles_sub_crc0 (C : WalCodec) {f : List w8} {fs : List (List w8)} {r : WalRec}
    {len : Nat} {c0 : w32} (ht : r.typ = crcType) (h : decStep C fs.isEmpty f 0 0#32 = .accept r len c0)
    (c : w32) : ∀ p ∈ acceptsFiles C (f :: fs) c, p ∈ acceptsFiles C (f :: fs) 0#32 := by
  intro p hp
  rcases decStep_c_of_crc0 c ht h with hc | hc
  · have e : acceptsFiles C (f :: fs) c = acceptsFiles C (f :: fs) 0#32 := by
      cases fs with
      | nil =>
        simp only [List.isEmpty_nil] at h hc
        simp only [acceptsFiles, acceptsFrom_accept h, acceptsFrom_accept hc]
      | cons g gs =>
        simp only [List.isEmpty_cons] at h hc
        have e1 : walDecodeFrom C false f 0 c = walDecodeFrom C false f 0 0#32 := by
          rw [walDecodeFrom_unfold C false f 0 c, walDecodeFrom_unfold C false f 0 0#32, h, hc]
        simp only [acceptsFiles, acceptsFrom_accept h, acceptsFrom_accept hc, e1]
    rw [← e]; exact hp
  · exfalso
    have ha : acceptsFrom C fs.isEmpty f 0 c = [] := by rw [acceptsFrom_unfold, hc]
    have hd : (walDecodeFrom C fs.isEmpty f 0 c).stop = .crcRec := by
      rw [walDecodeFrom_unfold, hc]
    cases fs with
    | nil =>
      simp only [List.isEmpty_nil] at ha
      simp [acceptsFiles, ha] at hp
    | cons g gs =>
      simp only [List.isEmpty_cons] at ha hd
      simp [acceptsFiles, ha, hd] at hp

/-! ## W1 with a durable file in front -/

/-- A frame within a durable file's image is as of the last sync. -/
theorem asOfOneG_durable {bs : List ByteG} {rz : List Nat} {img : List w8} {o len : Nat}
    (hdur : ∀ y ∈ bs, y = durB y.1) (himg : img = bs.map (·.1)) (hb : o + len ≤ img.length) :
    AsOfOneG bs rz img o len := by
  left
  intro b hb1 hb2
  show img.getD b 0 = valAt (bs.getD b (0, [])).2 0
  have hlt : b < img.length := by omega
  rw [himg] at hlt ⊢
  simp only [List.length_map] at hlt
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  simp only [Option.map_some, Option.getD_some]
  rw [hdur _ (List.getElem_mem hlt)]
  exact (valAt_durB _).symm

/-- **W1 with a durable file in front** (see the file header): from W1 over the files `js`, W1 over
`i0 :: js`, `i0`'s image its durable bytes, the first of `js` starting with a CRC record. -/
theorem w1G_cons_durable {C : WalCodec} {js : List Ino} {img img' : Ino → List w8}
    {bsOf : Ino → Option (List ByteG)} {rzOf : Ino → List Nat} {i0 : Ino} {bs0 : List ByteG}
    (hw : W1G C js img bsOf rzOf) (himg : ∀ i ∈ js, img' i = img i)
    (hb0 : bsOf i0 = some bs0) (hdur : ∀ y ∈ bs0, y = durB y.1) (himg0 : img' i0 = bs0.map (·.1))
    (hhead : ∀ i1 js', js = i1 :: js' → ∃ r len c0, r.typ = crcType ∧
        decStep C js'.isEmpty (img i1) 0 0#32 = .accept r len c0) :
    W1G C (i0 :: js) img' bsOf rzOf := by
  have hmap : ∀ k, (js.drop k).map img' = (js.drop k).map img := fun k =>
    List.map_congr_left (fun i hi => himg i (List.mem_of_mem_drop hi))
  -- a frame of `i0`
  have hown : ∀ p : Nat × Nat, p.1 = 0 → ∀ i bs, (i0 :: js)[p.1]? = some i → bsOf i = some bs →
      p.2 + frameCore (img' i) p.2 ≤ (img' i).length →
      AsOfOneG bs (rzOf i) (img' i) p.2 (frameCore (img' i) p.2) := by
    intro p hp1 i bs hi hbs hb
    rw [hp1] at hi
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    rw [hb0] at hbs; cases hbs
    exact asOfOneG_durable hdur himg0 hb
  intro k p hp i bs hi hbs hsz
  cases k with
  | succ k =>
    simp only [List.drop_succ_cons] at hp hi
    rw [hmap k] at hp
    have hij : i ∈ js := List.mem_of_mem_drop (List.mem_of_getElem? hi)
    rw [himg i hij] at hsz ⊢
    exact hw k p hp i bs hi hbs hsz
  | zero =>
    simp only [List.drop_zero] at hp hi
    obtain ⟨x, hx, hxb⟩ := acceptsFiles_bound C _ _ p hp
    cases js with
    | nil =>
      simp only [List.map_cons, List.map_nil, acceptsFiles, List.mem_map] at hp
      obtain ⟨o, -, rfl⟩ := hp
      refine hown (0, o) rfl i bs hi hbs ?_
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      have hx' : img' i0 = x := by simpa using hx
      rw [hx']; exact hxb
    | cons i1 js' =>
      simp only [List.map_cons, acceptsFiles, List.mem_append, List.mem_map] at hp
      rcases hp with ⟨o, -, rfl⟩ | hp
      · refine hown (0, o) rfl i bs hi hbs ?_
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        have hx' : img' i0 = x := by simpa using hx
        rw [hx']; exact hxb
      · split at hp
        · simp only [List.mem_map] at hp
          obtain ⟨q, hq, rfl⟩ := hp
          obtain ⟨r, len, c0, ht, hd⟩ := hhead i1 js' rfl
          have hmap' : img' i1 :: js'.map img' = img i1 :: js'.map img := by
            have := hmap 0
            simpa using this
          rw [hmap'] at hq
          have hq0 := acceptsFiles_sub_crc0 C (fs := js'.map img) ht
            (by rw [List.isEmpty_map]; exact hd) _ q hq
          simp only [List.getElem?_cons_succ] at hi
          have hij : i ∈ i1 :: js' := List.mem_of_getElem? hi
          rw [himg i hij] at hsz ⊢
          exact hw 0 q (by simpa using hq0) i bs (by simpa using hi) hbs hsz
        · simp at hp

/-! ## Every segment starts with its CRC record -/

theorem segsDs_head (M : WalMarshal) (md : List w8) :
    ∀ (first : Bool) (P : WalHist) (Ss : List WalHist), ∀ D ∈ segsDs M md first P Ss,
      ∃ x rest, D = (crcType, x) :: rest
  | _, _, [], D, hD => by simp [segsDs] at hD
  | first, P, S :: Ss, D, hD => by
    simp only [segsDs, List.mem_cons] at hD
    rcases hD with rfl | hD
    · unfold segHdrDs hdrDs cutHdrDs
      split <;> exact ⟨_, _, rfl⟩
    · exact segsDs_head M md false (P ++ S) Ss D hD

theorem chainSegs_head (C : WalCodec) : ∀ (c : w32) (Ds : List (List (w64 × List w8))),
    (∀ D ∈ Ds, ∃ x rest, D = (crcType, x) :: rest) →
    ∀ rs ∈ chainSegs C c Ds, ∃ r rs', rs = r :: rs' ∧ r.typ = crcType
  | _, [], _, rs, h => by simp [chainSegs] at h
  | c, D :: Ds, hD, rs, h => by
    simp only [chainSegs, List.mem_cons] at h
    rcases h with rfl | h
    · obtain ⟨x, rest, rfl⟩ := hD D (List.mem_cons_self ..)
      exact ⟨_, _, rfl, rfl⟩
    · exact chainSegs_head C _ Ds (fun D' hD' => hD D' (List.mem_cons_of_mem _ hD')) rs h

/-- **Each segment's records start with its CRC record**, one of the WAL's records. -/
theorem segRecs_head (C : WalCodec) (Mr : WalMarshal) (d : WalDur) (cuts : List Nat) {k : Nat}
    (hk : k < cuts.length + 1) :
    ∃ r rs', (segRecs C Mr d cuts).getD k [] = r :: rs' ∧ r.typ = crcType ∧
      r ∈ recsOfSegs C Mr d.metadata (segsOf (histM d) cuts) := by
  have hlen : (segRecs C Mr d cuts).length = cuts.length + 1 := by
    unfold segRecs; rw [length_chainSegs, length_segsDs]; simp [segsOf]
  have hm : (segRecs C Mr d cuts).getD k [] ∈ segRecs C Mr d cuts := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.getElem_mem _
  obtain ⟨r, rs', he, ht⟩ := chainSegs_head C _ _ (segsDs_head Mr d.metadata true [] _) _ hm
  refine ⟨r, rs', he, ht, ?_⟩
  unfold recsOfSegs
  rw [← flatten_chainSegs]
  exact List.mem_flatten.2 ⟨_, hm, by rw [he]; exact List.mem_cons_self ..⟩

/-- A crash of a file whose first `B` bytes are durable (`S`'s), `B` at most its least crash size:
its image is at least `B` long and starts with them. -/
theorem crashImg_durPrefix {om : OsMeta} {dq : DFrac} {bs : List ByteG} {S : List w8} {B : Nat}
    {f : Fs.OsFile} (h : FileCrashedR om [(0, dq, bs)] (some f)) (hB : B ≤ om.lo) (hBl : B ≤ bs.length)
    (hd : ∀ b, b < B → bs.getD b (0, []) = durB (S.getD b 0)) :
    B ≤ f.contents.length ∧ ∀ b, b < B → f.contents.getD b 0 = S.getD b 0 := by
  obtain ⟨-, h1, -, hrun, -⟩ := h f rfl
  refine ⟨by rw [contents_length]; omega, fun b hb => ?_⟩
  have hbl : b < bs.length := by omega
  rcases hrun _ (List.mem_singleton_self _) b hbl (by simp only [Nat.zero_add]; omega) with
    ⟨s, hs⟩ | ⟨h0, -⟩
  · simp only [Nat.zero_add] at hs
    have := hd b hb
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl, Option.getD_some] at this
    rw [this] at hs
    simp only [durB, List.mem_singleton, Prod.mk.injEq] at hs
    rw [contents_getD f b (by omega), hs.1]
  · simp only [Nat.zero_add] at h0; omega

/-- An image starting with a CRC record's frame: a fresh reader accepts it. -/
theorem decStep_head_of_prefix {C : WalCodec} (hC : C.Ok) (last : Bool) {img : List w8} {r : WalRec}
    {rs : List WalRec} (ht : r.typ = crcType) (hfit : (C.encRec r).length < 2 ^ 56)
    {B : Nat} (hB : (frame (C.encRec r)).length ≤ B) (hl : B ≤ img.length)
    (himg : ∀ b, b < B → img.getD b 0 = (recFrames C (r :: rs)).getD b 0) :
    ∃ len c0, decStep C last img 0 0#32 = .accept r len c0 := by
  have hpre : frame (C.encRec r) <+: img := by
    apply prefix_of_getD (by omega)
    intro b hb
    rw [himg b (by omega), recFrames_cons, List.getD_eq_getElem?_getD,
      List.getElem?_append_left hb, ← List.getD_eq_getElem?_getD]
  obtain ⟨rest, hrest⟩ := hpre
  exact ⟨_, _, decStep_frame hC last (off := 0) (rest := rest) hfit (by rw [List.drop_zero, hrest])
    (by simp [CrcOk, ht])⟩

/-- **A crash of an intact segment starts with its CRC record.** -/
theorem intact_head {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents : Ents} (habs : WalAbsD C Mr d lay ents) {k : Nat} {g : SegG}
    (hk : k + 1 < lay.segs.length) (hg : lay.segs[k]? = some g) (hex : SegExact g) {dq : DFrac}
    {f : Fs.OsFile} (hfc : FileCrashedR g.om [(0, dq, g.bs)] (some f)) (last : Bool) :
    ∃ r len c0, r.typ = crcType ∧ decStep C last f.contents 0 0#32 = .accept r len c0 := by
  have hint := habs.intact k g hk hg
  have hcl := habs.cuts.2.2
  obtain ⟨r, rs, he, ht, hmem⟩ := segRecs_head C Mr d lay.cuts (k := lay.first + k) (by omega)
  have hS : segStream C Mr d lay.cuts (lay.first + k) = recFrames C (r :: rs) := by
    unfold segStream; rw [he]
  have himg := durable_img (xs := segStream C Mr d lay.cuts (lay.first + k)) (by rw [← hint]; exact hfc)
    (by rw [hex.1, hint, List.length_map]) (by rw [hex.2, hint, List.length_map])
  obtain ⟨len, c0, hd⟩ := decStep_head_of_prefix hC last (img := f.contents) (rs := rs) ht (habs.fit r hmem)
    (B := (frame (C.encRec r)).length) (Nat.le_refl _)
    (by rw [himg, hS, recFrames_cons, List.length_append]; omega)
    (fun b _ => by rw [himg, hS])
  exact ⟨r, len, c0, ht, hd⟩

/-- **A crash of the last segment starts with its CRC record** (synced, below the least crash size). -/
theorem tail_head {C : WalCodec} (hC : C.Ok) {Mr : WalMarshal} {d : WalDur} {lay : WalLay}
    {ents : Ents} (habs : WalAbsD C Mr d lay ents) {g : SegG} (hg : lay.segs.getLast? = some g)
    (hc : lay.cuts ≠ []) {dq : DFrac} {f : Fs.OsFile}
    (hfc : FileCrashedR g.om [(0, dq, g.bs)] (some f)) (last : Bool) :
    ∃ r len c0, r.typ = crcType ∧ decStep C last f.contents 0 0#32 = .accept r len c0 := by
  have hsorted := habs.cuts.2.1
  have hLm : segStart lay.cuts lay.cuts.length ≤ d.m := habs.lastSynced
  obtain ⟨r0, rs, hR0, ht0⟩ := lastRecs_head_crc C Mr d hc
  have hRS : segStream C Mr d lay.cuts lay.cuts.length = recFrames C (r0 :: rs) := by
    rw [← hR0]; rfl
  have hfit : (C.encRec r0).length < 2 ^ 56 := habs.fit r0 (by
    rw [allRecs_split, hR0]; exact List.mem_append_right _ (List.mem_cons_self ..))
  -- the first frame is synced
  generalize hA : (lastHdr Mr d lay.cuts).length + (((lastOps d lay.cuts).take
    (d.m - segStart lay.cuts lay.cuts.length)).flatMap (opDs Mr)).length = a
  have hha : 1 ≤ a := by have := lastHdr_pos Mr d lay.cuts; omega
  have hso : (frame (C.encRec r0)).length ≤ lay.so := by
    have hs := habs.synced.2
    have e : (segRecs C Mr { d with H := d.H.take d.m } lay.cuts).getD lay.cuts.length [] =
        (r0 :: rs).take a := by
      rw [← hA, ← hR0]; exact lastRecs_synced C Mr d hsorted hLm
    rw [e] at hs
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [List.take_succ_cons, recFrames_cons, List.length_append] at hs
    omega
  obtain ⟨hsw, -, -, hwb, -⟩ := habs.lastWin g hg
  have hlo := habs.winLo_any g hg
  unfold WinLo at hlo
  obtain ⟨hB, himg⟩ := crashImg_durPrefix (S := segStream C Mr d lay.cuts lay.cuts.length)
    (B := lay.so) hfc (by omega) (by omega)
    (fun b hb => by
      have hbl : b < g.bs.length := by omega
      rcases habs.low g hg b (g.bs[b]) (List.getElem?_eq_getElem hbl) (by omega) with
        ⟨-, hB⟩ | ⟨-, h2, -⟩
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hbl, Option.getD_some]
        simpa [ByteOk, hb] using hB
      · omega)
  obtain ⟨len, c0, hd⟩ := decStep_head_of_prefix hC last (img := f.contents) (rs := rs) ht0 hfit hso hB
    (fun b hb => by rw [himg b hb, hRS])
  exact ⟨r0, len, c0, ht0, hd⟩

end pure

end WalFs
end EtcdGrove
end Perennial

end
