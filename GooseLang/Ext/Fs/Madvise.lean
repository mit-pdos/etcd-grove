/-
WP specs of the Linux file extension's `madvise` (`IsFsStep`'s `"Madvise"`, a paging hint: no
visible change, any errno; session S3d, pending the user's review): `wp_osMadvise`, any errno; and
under `NoMapLockErr` of a mapping of a covered file (every inode covered), errno 0
(`wp_osMadviseNE`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.NoMapLockErrSpecs

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [S : ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- `madvise(addr, len, advice)` with a paging hint: any errno, no visible change; with a resource
`P` that tells a fact `R` of the state, the errno is one the semantics' steps from such a state
give (`hR`; `P` back). -/
theorem wp_osMadviseG (addr : Loc) (len adv : w64) (hadv : adv.toNat ≤ 3) (hE : ↑osN ⊆ E)
    (P : IProp GF) (R : OsState → Prop) (Ψ : w64 → Prop)
    (hP : ∀ st Γb Γm Γf Γt h, osWorld (L := L) st Γb Γm Γf Γt h -∗ P -∗ ⌜R st⌝)
    (hR : ∀ h st e' h' st', R st →
      FsStepV "Madvise" (PairV (#addr) (PairV (#len) (#adv))) h st () e' h' st' () →
      ExtSemantics.step (E := fsExt) GoLocalContext.typeFns "Madvise" (PairV (#addr) (PairV (#len) (#adv))) h st () e' h' st' () →
      ∀ e : w64, e' = Val (#e) → Ψ e)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ P -∗ (∀ e : w64, ⌜Ψ e⌝ -∗ P -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Madvise" (Val (PairV (#addr) (PairV (#len) (#adv))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv HP HΦ
  iapply wp_os_stepX "Madvise" _ Φ (by simp [val.isPanic]) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  icases hP st Γb Γm Γf Γt h $$ Hw HP with %hRst
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨addr, len, adv, 0, rfl, hadv, rfl, rfl⟩, mapsFresh_same rfl,
      heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨⟨Hst0, Hfr, Hr⟩, Hsem⟩ := Hst
  have Hst := Hst0
  simp only [IsFsStep] at Hst
  obtain ⟨addr', len', adv', e, hv, -, rfl, rfl⟩ := Hst
  have hΨ := hR _ _ _ _ _ hRst ⟨Hst0, Hfr, Hr⟩ Hsem e rfl
  imod cells_same hwf hwf Hr Hfr rfl rfl $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
  · iframe
  imodintro
  iexists Γb, Γm, Γf, Γt
  iframe
  isplitr
  · ipureintro; exact ⟨hwf, hcoh⟩
  iapply wp_value'
  iapply HΦ $$ %e %hΨ HP

/-- `madvise(addr, len, advice)` with a paging hint: any errno, no visible change. -/
theorem wp_osMadvise (addr : Loc) (len adv : w64) (hadv : adv.toNat ≤ 3) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ (∀ e : w64, Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Madvise" (Val (PairV (#addr) (PairV (#len) (#adv))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv HΦ
  iapply wp_osMadviseG addr len adv hadv hE emp (fun _ => True) (fun _ => True)
    (fun _ _ _ _ _ _ => by iintro - -; ipureintro; trivial) (fun _ _ _ _ _ _ _ _ _ _ => trivial) Φ
    $$ Hinv [] [HΦ]
  · iempintro
  iintro %e - -
  iapply HΦ

/-- **`madvise` with no error** (under `NoMapLockErr`, every inode covered) of a mapping `base` of
the file `p` (its `OsMeta`, any fraction): errno 0. -/
theorem wp_osMadviseNE {Sio : IoSet} [hml : FsStepSat (NoMapLockErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (base : Loc) (len adv : w64) (p : Ino) (dq : DFrac) (m : OsMeta) (n : Nat)
    (hadv : adv.toNat ≤ 3) (hb : m.maps !! base = some n) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osMeta (L := L) p dq m -∗ (osMeta (L := L) p dq m -∗ Φ (#(0 : w64))) -∗
      WP (ExternalOp fsExt.name "Madvise" (Val (PairV (#base) (PairV (#len) (#adv))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hm HΦ
  iapply wp_osMadviseG base len adv hadv hE (osMeta (L := L) p dq m)
    (fun st => st.proc.maps !! base = some ⟨p, n⟩) (· = 0)
    (fun st Γb Γm Γf Γt h => by
      unfold osWorld osMeta
      iintro ⟨%Hwc, HAb, HAm, -⟩ Hm
      icases gAuth_lookup _ _ _ _ _ _ $$ HAm Hm with %Hml
      obtain ⟨f, hf, hmo⟩ := coh_meta Hwc.2 Hml
      ipureintro; exact (hmo.maps base n).1 hb)
    (fun h st e' h' st' hm Hv Hsem e he => by
      have hz := hml.sat _ _ _ _ _ _ _ _ _ Hsem ⟨base, _, ⟨p, n⟩, rfl, hm, hS _ _⟩
        ⟨Val (#(0 : w64)), st, ⟨base, len, adv, 0, rfl, hadv, rfl, rfl⟩, rfl⟩
      rw [he] at hz
      exact go.intoVal_inj (Expr.Val.inj hz))
    Φ $$ Hinv Hm [HΦ]
  iintro %e %he Hm
  subst he
  iapply HΦ $$ Hm

end specs

end Fs
end Perennial

end
