/- Lean-first (no Rocq counterpart).

# A handle's loans, made and returned (P6b fix A; ledger 2026-11-25, "loans carried in the handles")

A handle with no registration pending holds the lock holder's names record (`walHLoans dir none qs`,
`Handle.lean`): one loan of the WAL's name per path to `dir` it holds (`walDirH`'s own, its pipeline's).
`Close` returns them (`walInv_returnHLoans2`) before it gives the lock token back.

* `inArea_root`: two `InArea` of one directory agree on the root and the name.
* `walInv_dirKeyArea`: a WAL directory with a key is in the area (`InArea r dir nm`).
* `walHLoans_mk`: the record made from the loans `walInv_dirPath` records.
* `walInv_returnHLoans2`: the two loans of a write handle returned with their paths.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.NameLoans

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

/-- A separator's last occurrence splits a list one way. -/
theorem sep_last_inj {α : Type} (s : α) (a b c d : List α) (hb : s ∉ b) (hd : s ∉ d)
    (h : a ++ s :: b = c ++ s :: d) : a = c ∧ b = d := by
  induction a generalizing c with
  | nil =>
    cases c with
    | nil => simp at h; exact ⟨rfl, h⟩
    | cons y c =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.2 ▸ List.mem_append_right c (List.mem_cons_self)) hb
  | cons x a ih =>
    cases c with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.2 ▸ List.mem_append_right a (List.mem_cons_self)) hd
    | cons y c =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := ih c h.2
      exact ⟨by rw [h.1, h1], h2⟩

/-- **Two `InArea` of one directory agree** on the area root and the name (a WAL name has no `/`). -/
theorem inArea_root {r r' dir nm nm' : GoString} (h : InArea r dir nm) (h' : InArea r' dir nm') :
    r = r' ∧ nm = nm' := by
  obtain ⟨hn, hd⟩ := h
  obtain ⟨hn', hd'⟩ := h'
  have e : r ++ W8 47 :: nm = r' ++ W8 47 :: nm' := by
    have := hd.symm.trans hd'
    simpa [List.append_assoc] using this
  exact sep_last_inj (W8 47) r nm r' nm' hn.2.1 hn'.2.1 e

/-- `InArea` as a child path. -/
theorem inArea_child {r dir nm : GoString} (h : InArea r dir nm) : dir = child r nm := by
  rw [h.2]; simp [child, List.append_assoc]; rfl

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]

/-- **A WAL directory with a key is in the area**: `InArea r dir nm` for the invariant's root `r`
(`DirKeysOk`: a layout; `WalsOk`: a WAL, in the area). -/
theorem walInv_dirKeyArea (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (j : Ino) (X : List GoString) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ walDirKey (W := W) dir j X ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ ⌜∃ nm, InArea r dir nm⌝ := by
  iintro #Hinv Hnc #Hk
  imod walInv_open (L := hG.goose_localGS) C Mr R jr r ⊤ (fun _ _ => CoPset.mem_full) $$ Hinv Hnc
    with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl0, Hcm, Hlays, %HW, %HWC, HCR, Htl, %Hab, %HNm, Hpk,
    ⟨%K, %cp, HKa, Hca, %HDK⟩, %HAt, Hnms, Hbd⟩
  icases walDirKey_lookup (W := W) K dir j X $$ HKa Hk with %hK
  have hin : ∃ nm, InArea r dir nm := by
    obtain ⟨lay, -, hl, -⟩ := HDK.1 dir j X hK
    cases hw : s.wal !! dir with
    | none => rw [HW.2.1 dir hw] at hl; cases hl
    | some d =>
      obtain ⟨lay', nm, hj, -, hin, -⟩ := HW.1 dir d hw
      exact ⟨nm, Har ▸ hin⟩
  imod Hcl $$ [Hg Hcl0 Hcm Hlays HCR Htl Hpk HKa Hca Hnms Hbd] with -
  · iexists s
    iexists Ls, cl, n, F
    iframe Hg Hcl0 Hcm Hlays HCR Htl Hpk Hnms Hbd
    isplitr
    · ipureintro; exact Har
    isplitr
    · ipureintro; exact HW
    isplitr
    · ipureintro; exact HWC
    isplitr
    · ipureintro; exact Hab
    isplitr
    · ipureintro; exact HNm
    isplitl [HKa Hca]
    · iexists K, cp
      iframe HKa Hca
      ipureintro; exact HDK
    ipureintro; exact HAt
  imodintro
  iframe Hnc
  ipureintro; exact hin

/-- **A handle's record from the loans made** (`walInv_dirPath`'s, in the order of `qs`). -/
theorem walHLoans_mk (dir r nm : GoString) (qs : List Qp) (h : InArea r dir nm) :
    walNamesFragS (W := W) ⟨none, none, qs.map (fun q => (nm, q))⟩ ⊢ walHLoans (W := W) dir none qs := by
  iintro Hf
  unfold walHLoans
  iexists _
  iframe Hf
  ipureintro
  exact ⟨fun _ => ⟨r, nm, h, rfl⟩, fun h => absurd rfl h⟩

/-- **A write handle's two loans returned** (`Close`): with the WAL's key (for the area root) and the two
paths to `dir`, the record back to no loan out. -/
theorem walInv_returnHLoans2 (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (dir : GoString) (j j1 j2 : Ino) (X : List GoString) (q1 q2 : Qp) :
    ⊢ walInv (L := hG.goose_localGS) (W := W) C Mr R jr r -∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ walDirKey (W := W) dir j X -∗
      walHLoans (W := W) dir none [q1, q2] -∗
      osPathS (L := hG.goose_localGS) R dir (DFrac.own q1) j1 -∗
      osPathS (L := hG.goose_localGS) R dir (DFrac.own q2) j2 ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗ walNamesFrag (W := W) none := by
  iintro #Hinv Hnc #Hk Hl Hp1 Hp2
  imod walInv_dirKeyArea C Mr R jr r dir j X $$ Hinv Hnc Hk with ⟨Hnc, %hA⟩
  obtain ⟨nm2, hA⟩ := hA
  unfold walHLoans
  icases Hl with ⟨%Lh, Hf, %hL⟩
  obtain ⟨r', nm, hA', hLh⟩ := hL.1 rfl
  obtain ⟨-, rfl⟩ := inArea_root hA hA'
  subst hLh
  have hd := inArea_child hA
  simp only [List.map_cons, List.map_nil]
  imod walInv_dirPathRetDL C Mr R jr r dir nm2 q1 j1 [(nm2, q2)] hd $$ Hinv Hnc Hf Hp1 with ⟨Hnc, Hf⟩
  iapply walInv_dirPathRetD C Mr R jr r dir nm2 q2 j2 hd $$ Hinv Hnc Hf Hp2

end iris

end WalFs
end EtcdGrove
end Perennial

end
