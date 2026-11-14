/- Lean-first (no Rocq counterpart).

# `ReadAll`'s handle, the files before the tail (W3/W5 of `notes/wal-fsext-plan.md`, twenty-seventh session)

The decoder hands back, at `io.EOF`, the read files before the tail (`walFileS` each); `ReadAll` keeps
them open as the handle's non-tail locks (`walLockH`, with the tie's `fileutil.lockedFile`s) and gives
the program's halves of their segments back to the invariant (`walInv_readGive`):

* `readAll_splitLeft`: the files split into the segments' halves and the locks;
* `filter_out_take`: what the handle holds out after the give-back is the tail alone.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Fs WalEnc

section pure

/-- **What the handle holds out after the give-back is the tail alone.** -/
theorem filter_out_take {l : List SegG} {n : Nat} {g : SegG} (h : l = l.take n ++ [g])
    (hnd : (l.map (·.ino)).Nodup) :
    (l.map (·.ino)).filter (fun x => decide (x ∉ (l.take n).map (·.ino))) = [g.ino] := by
  generalize hA : l.take n = A at h
  subst h
  rw [List.map_append, List.map_singleton] at hnd
  have hg : g.ino ∉ A.map (·.ino) := fun hm =>
    (List.nodup_append.1 hnd).2.2 _ hm _ (List.mem_singleton_self _) rfl
  rw [List.map_append, List.map_singleton, List.filter_append]
  have h1 : (A.map (·.ino)).filter (fun x => decide (x ∉ A.map (·.ino))) = [] := by
    rw [List.filter_eq_nil_iff]; intro x hx; simp [hx]
  rw [h1, List.nil_append]
  simp only [List.filter_cons, List.filter_nil]
  rw [if_pos (by simpa using hg)]

end pure

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- **The read files before the tail: the segments' halves and the locks** (see the file header). -/
theorem readAll_splitLeft (dir : GoString) :
    ∀ (fsI : List (DecFile GF)) (gs : List SegG) (fls ls : List Loc) (flag : Ino → OsFd),
      fsI.length = gs.length → ls.length = fsI.length →
      (∀ (k : Nat) (F : DecFile GF) (g : SegG), fsI[k]? = some F → gs[k]? = some g →
        ∃ (f : Loc) (fd : w64), fls[k]? = some f ∧
          F.S = walFileS f fd (child dir g.name) (flag g.ino) g) →
      ([∗list] y ∈ fsI, ∃ q, y.S q) ∗
        ([∗list] k ↦ lf ∈ ls, fileutil.lockedFile lf (fls.getD k null)) ⊢
      ([∗list] g ∈ gs, segRes (L := hG.goose_localGS) g) ∗ [∗list] lf ∈ ls, walLockH lf
  | [], gs, fls, ls, _, hl, hls, _ => by
    have hg : gs = [] := List.eq_nil_of_length_eq_zero (by simp at hl; omega)
    have hl' : ls = [] := List.eq_nil_of_length_eq_zero (by simpa using hls)
    subst hg hl'
    iintro -
    isplitl
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  | F :: fsI, gs, fls, ls, flag, hl, hls, hk => by
    obtain ⟨g, gs', rfl⟩ : ∃ g gs', gs = g :: gs' := by
      cases gs with
      | nil => simp at hl
      | cons g gs' => exact ⟨g, gs', rfl⟩
    obtain ⟨lf, ls', rfl⟩ : ∃ lf ls', ls = lf :: ls' := by
      cases ls with
      | nil => simp at hls
      | cons lf ls' => exact ⟨lf, ls', rfl⟩
    obtain ⟨f, fd, hf0, hS⟩ := hk 0 F g rfl rfl
    obtain ⟨f0, fls', rfl⟩ : ∃ f0 fls', fls = f0 :: fls' := by
      cases fls with
      | nil => simp at hf0
      | cons f0 fls' => exact ⟨f0, fls', rfl⟩
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hf0
    subst hf0
    have ih := readAll_splitLeft dir fsI gs' fls' ls' flag (by simpa using hl) (by simpa using hls)
      (fun k F' g' h1 h2 => by
        obtain ⟨f', fd', h3, h4⟩ := hk (k + 1) F' g' (by simpa using h1) (by simpa using h2)
        exact ⟨f', fd', by simpa using h3, h4⟩)
    iintro ⟨HF, HL⟩
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ HF with ⟨⟨%q, H0⟩, HF⟩
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ HL with ⟨#Hl0, HL⟩
    rw [hS]
    unfold walFileS
    icases H0 with ⟨-, Hfile, Hfd, -, Hm, Hb⟩
    ihave HL' : [∗list] k ↦ lf ∈ ls', fileutil.lockedFile lf (fls'.getD k null) $$ [HL]
    · iapply (BigSepL.bigSepL_mono (fun {k x} _ => ?_)) $$ HL
      simp only [List.getD_cons_succ]
      exact .rfl
    icases ih $$ [HF HL'] with ⟨HS, HLk⟩
    · iframe HF HL'
    isplitl [Hm Hb HS]
    · iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      iframe HS
      unfold segRes
      iframe Hm Hb
    · iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
      iframe HLk
      unfold walLockH
      iexists f0, fd, child dir g.name, flag g.ino
      iframe Hfile Hfd
      simp only [List.getD_cons_zero]
      iexact Hl0

end handle

end WalFs
end EtcdGrove
end Perennial

end
