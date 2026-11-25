/-
`fsync`/`fdatasync` with the file's bytes held **per byte, by masks** (Lean-first, no Rocq
counterpart): `wp_osFsync2` (`GooseLang/Ext/Fs/Specs.lean`) takes the bytes it makes durable as two
runs, whole; a client whose not-yet-durable bytes are spread over many runs (bbolt's dirty pages,
the caller's half of each in its own invariants, the crash invariant's half beside them) needs any
set of them. `wp_osFsyncC` takes them as `cBytes` (`Proof/os/CrashSt.lean`) of one list of the
file's bytes from 0: those of the mask `cF` whole (made durable), those of `cD` at any fraction
(durable inside the range not yet durable, `[dlo, dhi)`; passed through). With no cut on the file
(`m.cut = none`), it also says that the bytes of `cD` are durable (outside `[dlo, dhi)` the file
extension knows them so). Its proof is `wp_osFsync2`'s, with `insertC` for `insertBytes`.
-/
module

public import Proof.os.CrashSt

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs goose_heap

/-- `m` with the bytes `ys` from `off` on where `c` holds. -/
def insertC (i : Ino) (c : Nat → Bool) : Nat → List ByteG → GMap (Ino × Nat) ByteG →
    GMap (Ino × Nat) ByteG
  | _, [], m => m
  | off, y :: ys, m => insertC i c (off + 1) ys (if c off then <[(i, off) := y]> m else m)

theorem lookup_insertC (i : Ino) (c : Nat → Bool) : ∀ (off : Nat) (ys : List ByteG)
    (m : GMap (Ino × Nat) ByteG) (q : Ino) (j : Nat),
    insertC i c off ys m !! (q, j) =
      if q = i ∧ off ≤ j ∧ j < off + ys.length ∧ c j = true then ys[j - off]? else m !! (q, j)
  | off, [], m, q, j => by simp [insertC]; intros; omega
  | off, y :: ys, m, q, j => by
    simp only [insertC]
    rw [lookup_insertC i c (off + 1) ys]
    simp only [List.length_cons]
    by_cases h1 : q = i ∧ off + 1 ≤ j ∧ j < off + 1 + ys.length ∧ c j = true
    · rw [if_pos h1, if_pos ⟨h1.1, by omega, by omega, h1.2.2.2⟩,
        show j - off = (j - (off + 1)) + 1 by omega, List.getElem?_cons_succ]
    · rw [if_neg h1]
      by_cases h2 : q = i ∧ j = off ∧ c j = true
      · obtain ⟨hq, hj, hc⟩ := h2
        have hc' : c off = true := by rw [← hj]; exact hc
        rw [if_pos hc', GMap.lookup_insert_eq_iff, if_pos (by rw [hq, hj]),
          if_pos ⟨hq, by omega, by omega, hc⟩, hj, Nat.sub_self, List.getElem?_cons_zero]
      · have hn : ¬ (q = i ∧ off ≤ j ∧ j < off + (ys.length + 1) ∧ c j = true) := by
          rintro ⟨hq, h3, h4, h5⟩
          by_cases hj : j = off
          · exact h2 ⟨hq, hj, h5⟩
          · exact h1 ⟨hq, by omega, by omega, h5⟩
        rw [if_neg hn]
        split
        · rename_i hc
          rw [GMap.lookup_insert_eq_iff, if_neg]
          intro h
          simp only [Prod.mk.injEq] at h
          obtain ⟨h3, h4⟩ := h
          have hj : j = off := by omega
          exact h2 ⟨by first | exact h3 | exact h3.symm, hj, by rw [hj]; exact hc⟩
        · rfl

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}
attribute [local instance] Classical.propDecidable

theorem cBytes_consC (p : Ino) (d : Nat → DFrac) (c : Nat → Bool) (off : Nat) (x : ByteG)
    (xs : List ByteG) :
    cBytes (L := L) p d c off (x :: xs) ⊣⊢ cByte (L := L) p d c off x ∗ cBytes (L := L) p d c (off + 1) xs := by
  unfold cBytes
  refine BigSepL.bigSepL_cons.trans ?_
  rw [Nat.add_zero, BigSepL.bigSepL_eq_of_forall_eq (l := xs)
    (Ψ := fun k x => cByte (L := L) p d c (off + 1 + k) x) (fun {k x} => by congr 1; omega)]
  exact .rfl

/-- The bytes of a mask, in the ghost map. -/
theorem cBytes_lookup (i : Ino) (d : Nat → DFrac) (c : Nat → Bool) (Γb : GMap (Ino × Nat) ByteG)
    (off : Nat) (xs : List ByteG) :
    ⊢ gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb -∗ cBytes (L := L) i d c off xs -∗
      ⌜∀ k (hk : k < xs.length), c (off + k) = true → Γb !! (i, off + k) = some xs[k]⌝ := by
  iintro HA Hbs
  iapply pure_forall.2; iintro %k
  iapply pure_forall.2; iintro %hk
  by_cases hc : c (off + k) = true
  · unfold cBytes
    icases BigSepL.bigSepL_lookup (Φ := fun k (x : ByteG) => cByte (L := L) i d c (off + k) x)
      (List.getElem?_eq_getElem hk) $$ Hbs with Hb
    ihave Hb := (show cByte (L := L) i d c (off + k) xs[k] ⊢
        gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb (i, off + k) (d (off + k)) xs[k] by
      unfold cByte osByte; rw [if_pos hc]) $$ Hb
    ihave %h := gAuth_lookup _ _ _ _ _ _ $$ HA Hb
    ipureintro; exact fun _ => h
  · ipureintro; intro h; exact absurd h hc

/-- The bytes of a mask, whole, updated. -/
theorem cBytes_update (i : Ino) (c : Nat → Bool) : ∀ (off : Nat) (xs ys : List ByteG)
    (Γb : GMap (Ino × Nat) ByteG), ys.length = xs.length →
    gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb Γb ∗
        cBytes (L := L) i (fun _ => DFrac.own 1) c off xs ⊢
      |==> (gAuth (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb (insertC i c off ys Γb) ∗
        cBytes (L := L) i (fun _ => DFrac.own 1) c off ys)
  | off, [], [], Γb, _ => by
    simp only [insertC]
    iintro ⟨H, -⟩; imodintro; iframe; iapply (cBytes_nil (L := L) i _ c off).2; iempintro
  | off, x :: xs, y :: ys, Γb, hl => by
    simp only [insertC]
    iintro ⟨H, Hb⟩
    icases (cBytes_consC i _ c off x xs).1 $$ Hb with ⟨Hx, Hxs⟩
    by_cases hc : c off = true
    · rw [if_pos hc]
      ihave Hx := (show cByte (L := L) i (fun _ => DFrac.own 1) c off x ⊢
          gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb (i, off) (DFrac.own 1) x by
        unfold cByte osByte; rw [if_pos hc]) $$ Hx
      imod gAuth_update _ _ _ _ _ y $$ H Hx with ⟨H, Hy⟩
      imod cBytes_update i c (off + 1) xs ys _ (by simpa using hl) $$ [H Hxs] with ⟨H, Hys⟩
      · iframe
      imodintro
      iframe H
      iapply (cBytes_consC i _ c off y ys).2
      iframe Hys
      iapply (show gElem (gooseOsGS (L := L)) (gooseOsGS (L := L)).γb (i, off) (DFrac.own 1) y ⊢
          cByte (L := L) i (fun _ => DFrac.own 1) c off y by
        unfold cByte osByte; rw [if_pos hc])
      iexact Hy
    · rw [if_neg hc]
      imod cBytes_update i c (off + 1) xs ys Γb (by simpa using hl) $$ [H Hxs] with ⟨H, Hys⟩
      · iframe
      imodintro
      iframe H
      iapply (cBytes_consC i _ c off y ys).2
      iframe Hys
      iapply (show emp ⊢ cByte (L := L) i (fun _ => DFrac.own 1) c off y by
        unfold cByte; rw [if_neg hc])
      iempintro
  | _, [], _ :: _, _, hl => by simp at hl
  | _, _ :: _, [], _, hl => by simp at hl

/-- **`fsync`/`fdatasync` with the bytes per byte** (see the file header): those of `cF` whole, made
durable; those of `cD` at `dqd`, durable inside `[dlo, dhi)`, passed through; on success, every byte
of `cD` is durable when the file has no cut. On failure, which is never `EINTR`, nothing changes. -/
theorem wp_osFsyncC (fd : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (xs : List ByteG)
    (cF cD : Nat → Bool) (dqd : DFrac)
    (hdur : ∀ k (hk : k < xs.length), cD k = true → m.dlo ≤ k → k < m.dhi → xs[k] = durB xs[k].1)
    (hcov : ∀ b, b < m.size → m.dlo ≤ b → b < m.dhi →
      b < xs.length ∧ (cF b = true ∨ cD b = true))
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino (DFrac.own 1) m -∗
      cBytes (L := L) d.ino (fun _ => DFrac.own 1) cF 0 xs -∗ cBytes (L := L) d.ino (fun _ => dqd) cD 0 xs -∗
      (∀ e : w64,
        ((⌜e = 0 ∧ (m.cut = none → ∀ k (hk : k < xs.length), cD k = true → xs[k] = durB xs[k].1)⌝ ∗
            osMeta (L := L) d.ino (DFrac.own 1) m.synced ∗
            cBytes (L := L) d.ino (fun _ => DFrac.own 1) cF 0 (xs.map (fun x => durB x.1))) ∨
         (⌜e ≠ 0 ∧ e ≠ EINTR⌝ ∗ osMeta (L := L) d.ino (DFrac.own 1) m ∗
            cBytes (L := L) d.ino (fun _ => DFrac.own 1) cF 0 xs)) -∗
        osFd (L := L) fd dq d -∗ cBytes (L := L) d.ino (fun _ => dqd) cD 0 xs -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Fsync" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Hm Hbs Hrs HΦ
  iapply wp_os_step "Fsync" _ Φ (by simp) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd osMeta
  icases cBytes_lookup d.ino _ cF Γb 0 xs $$ HAb Hbs with %Hbl
  icases cBytes_lookup d.ino _ cD Γb 0 xs $$ HAb Hrs with %Hrl
  icases gFdElem_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
  icases tokRes_meta_whole _ $$ Htok Hm with %Hnt
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  obtain ⟨f, hf, hmo⟩ := coh_meta hcoh Hml
  have hdurD : m.cut = none → ∀ k (hk : k < xs.length), cD k = true → xs[k] = durB xs[k].1 := by
    intro hcut k hk hck
    by_cases hdd : m.dlo ≤ k ∧ k < m.dhi
    · exact hdur k hk hck hdd.1 hdd.2
    · have hy := Hrl k hk (by simpa using hck)
      rw [Nat.zero_add] at hy
      obtain ⟨f1, hf1, hb, hx1, -, hrel⟩ := hcoh.bytes _ _ _ hy
      rw [hf] at hf1; cases hf1
      simp only [cutOf, Hml, Option.bind_some, hcut] at hrel
      have hd := hmo.dur k hb hdd
      simp only [CandRel] at hrel
      rw [hd] at hrel
      refine Prod.ext rfl ?_
      show xs[k].2 = [(xs[k].1, 0)]
      rw [← hrel, hx1]
  have hni := noInfl_of_noTok hcoh Hnt
  have hnoI : ∀ b, ¬ InflightAt st d.ino b := by
    rintro b ⟨t, c, ht, hcp, -⟩; exact hni t c ht hcp
  let f' := f.synced (InflightAt st d.ino ·)
  have hszf := hwf.sizes d.ino f hf
  have hwfS : OsWf (st.setFile d.ino f') :=
    osWf_setFile' hwf hf (by simp only [f', OsFile.synced]; omega) (fun b p hp => by
      simp only [f', OsFile.synced, if_neg (hnoI b), List.mem_singleton] at hp; subst hp; simp)
  have hcvS : cellView (st.setFile d.ino f') = cellView st :=
    cellView_congr hwf hwfS rfl (fun q => by
      rw [file_setFile]; split
      · subst_vars; rw [hf]; simp [f', synced_contents]
      · rfl) rfl
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, _, ⟨fd, d, f, rfl, hfd, hf, .inl ⟨rfl, rfl⟩⟩, mapsFresh_same rfl,
      heapRendered_same hwfS rfl hcvS Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', d', f'', hv, hfd', hf', hres⟩ := Hst
  cases go.intoVal_inj hv
  simp only [FdOpen, hfd, Option.some.injEq] at hfd'; subst hfd'
  rw [hf] at hf'; cases hf'
  rcases hres with ⟨rfl, rfl⟩ | ⟨e, he, hEINTR, rfl, rfl⟩
  · -- success
    imod gAuth_update _ _ _ _ _ m.synced $$ HAm Hm with ⟨HAm, Hm⟩
    imod cBytes_update d.ino cF 0 xs (xs.map (fun x => durB x.1)) Γb (by simp) $$ [HAb Hbs]
      with ⟨HAb, Hbs⟩
    · iframe
    imod cells_same hwf hwfS Hr Hfr rfl hcvS $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    imodintro
    iexists _, _, Γf, Γt
    iframe
    isplitr
    · ipureintro
      refine ⟨hwfS, osCoh_setFile hcoh hf Hnt _ m.synced _ rfl rfl ?_ ?_ ?_ ?_ (Nat.le_refl _)
        (fun c hc => hcoh.cut_le d.ino m c Hml hc)⟩
      · refine ⟨by simp [OsMeta.synced, hmo.size, f', synced_size],
          by simp [OsMeta.synced, f', OsFile.synced, hmo.size],
          by simp [OsMeta.synced, f', OsFile.synced, hmo.size], hmo.maps,
          fun t c ht hc => absurd hc (hni t c ht), ?_, ?_, ?_, ?_, fun _ h => by simp [OsMeta.synced] at h,
          ?_,
          fun b hb => by
            simp only [f', synced_size] at hb
            simp only [f', OsFile.synced, if_neg (hnoI b)]
            exact diskByte_past hb, OsFile.xs_synced hmo.size⟩
        rotate_right
        · intro z hz b hb
          simp only [OsMeta.synced, Option.some.injEq] at hz; subst hz
          have hsz := hmo.size
          simp only [f', OsFile.synced, if_neg (hnoI b)]
          by_cases hpb : pageEnd m.size ≤ b
          · rw [diskByte_past (by rw [← hsz]; exact hpb)]
          · unfold OsMeta.syncZ at hb
            split at hb
            · unfold diskByte; split
              · exact hmo.cz b (by omega) (by omega)
              · rfl
            · omega
        · intro b _ _; exact synced_cand f _ b (hnoI b)
        · intro z hz
          simp only [OsMeta.synced, Option.some.injEq] at hz; subst hz
          have hsz := hmo.size
          refine ⟨by have := m.size_le_syncZ; simp only [synced_size]; omega, fun b hb => ?_⟩
          rw [synced_cand f _ b (hnoI b)]
          simp only [f', OsFile.synced, if_neg (hnoI b)]
          by_cases hpb : pageEnd m.size ≤ b
          · rw [diskByte_past (by rw [← hsz]; exact hpb)]
          · unfold OsMeta.syncZ at hb
            split at hb
            · rename_i hcz
              have h0 : diskByte f.cache f.size b = 0 := by
                unfold diskByte; split
                · exact hmo.cz b (by omega) (by omega)
                · rfl
              rw [h0]
            · omega
        · intro b c _ hc; simp [OsMeta.synced] at hc
        · intro b hb hbz
          have hsz := hmo.size
          simp only [f', OsFile.synced, if_neg (hnoI b)]
          simp only [OsMeta.synced] at hbz
          unfold diskByte; split
          · exact hmo.cz b (by simp only [f', synced_size] at hb; omega) hbz
          · rfl
      · intro b x hx
        rw [lookup_insertC] at hx
        split at hx
        · rename_i hr
          obtain ⟨-, -, h2, hc⟩ := hr
          have hk : b - 0 < xs.length := by simp at h2; omega
          rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hx
          simp only [Option.map_some, Option.some.injEq] at hx; subst hx
          obtain ⟨f1, hf1, hb, hx1, -, -⟩ := hcoh.bytes _ _ _ (Hbl (b - 0) hk (by simpa using hc))
          rw [hf] at hf1; cases hf1
          rw [show 0 + (b - 0) = b by omega] at hb hx1
          refine ⟨hb, by rw [synced_cache_lt f _ b hb]; exact hx1, ⟨0, by simp⟩, ?_⟩
          rw [synced_cand f _ b (hnoI b), synced_cache_lt f _ b hb, ← hx1]
          exact CandRel.dur _ _
        · obtain ⟨f1, hf1, hb, hx1, hmem, hrel⟩ := hcoh.bytes _ _ _ hx
          rw [hf] at hf1; cases hf1
          simp only [cutOf, Hml, Option.bind_some] at hrel
          refine ⟨hb, by rw [synced_cache_lt f _ b hb]; exact hx1, hmem, ?_⟩
          rw [synced_cand f _ b (hnoI b), synced_cache_lt f _ b hb, ← hx1]
          show CandRel m.cut x.2 [(x.1, 0)]
          rename_i hn
          by_cases hdd : m.dlo ≤ b ∧ b < m.dhi
          · obtain ⟨hbl, hc | hc⟩ := hcov b (by rw [hmo.size]; exact hb) hdd.1 hdd.2
            · exact absurd ⟨rfl, Nat.zero_le _, by simp; omega, hc⟩ hn
            · have hy := Hrl b hbl (by simpa using hc)
              rw [Nat.zero_add, hx] at hy
              have hd := hdur b hbl hc hdd.1 hdd.2
              rw [← Option.some.inj hy] at hd
              have h2 : x.2 = [(x.1, 0)] := congrArg Prod.snd hd
              rw [h2]; exact CandRel.dur _ _
          · have hd := hmo.dur b hb hdd
            rw [hx1, ← hd]; exact hrel
      · intro b hb
        rw [lookup_insertC]; split
        · rename_i hr; rw [List.getElem?_eq_getElem (by simp at hr ⊢; omega)]; rfl
        · exact hcoh.bytes_full _ f b hf hb
      · intro q b hq
        rw [lookup_insertC, if_neg (fun h => hq h.1)]
    iapply wp_value'
    iapply HΦ $$ [Hm Hbs] Hfd Hrs
    ileft; iframe; ipureintro; exact ⟨rfl, hdurD⟩
  · -- failure: nothing changes
    imod cells_same hwf hwf Hr Hfr rfl rfl $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
    · iframe
    imodintro
    iexists Γb, Γm, Γf, Γt
    iframe
    isplitr
    · ipureintro; exact ⟨hwf, hcoh⟩
    iapply wp_value'
    iapply HΦ $$ [Hm Hbs] Hfd Hrs
    iright; iframe; ipureintro; exact ⟨he, hEINTR⟩


end specs

end Perennial
