/-
**Arming at an `Unlock` window's commit point** (backend-snapshot B2 step (c), 2026-11-20;
`notes/backend-snapshot-plan.md`). In a window the batch lock's client resource `W` exists only as the
`Unlock` caller's wand from the clients' half of the view at the session's logical view `L'`
(`bView γ 1 L' -∗ W ∗ Qw`), and that half is deposited in `cacheInv` while the view's three fractions
are still at the window's (physical) view. The commit point arms the snapshots' registrations with a
*hypothetical* ghost update (`regs_arm`'s `hF`, whose effects are dropped since its conclusion is pure):
the three fractions moved to `L'` (`view_upd3`), the caller's wand applied for `W`. The deposit is
borrowed from `cacheInv` for the step and put back unchanged; nothing of the window protocol changes.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RegLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ReadSide

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **The inputs at a window's commit point, by a hypothetical update**: the view's three fractions
(the readers' quarter, the batch lock's, the clients' half lent from `cacheInv`) moved to the
session's logical view `L'`, the caller's wand gives `W`; the quarter at `L'` is the observation's,
`S` thin of it (`Hpre`), the deleted entries exactly (`dlsOk` at `L'`). -/
theorem obsIn_win (γ : BNames) (P : BParams) (W Pk Qw : IProp GF) (st : BSess) (La Lb vd0 L' : VData)
    (hd : dlsOk P st L') :
    iprop((bView γ 1 L' -∗ W ∗ Qw) ∗ viewQ γ (1 : Qp).half.half (vData P (st.C, st.R)) La ∗
      viewQ γ (1 : Qp).half.half (vData P (st.C, st.R)) Lb ∗ bView γ 1 vd0 ∗ Pk ∗
      thinV γ (sData P st.S) L' ∗ trkSide γ P st ∗ fkHalf γ P st) ⊢
    |==> obsIn (GF := GF) γ P W Pk st.S := by
  unfold obsIn viewAtD trkSide trkHalf fkHalf hkOwn
  iintro ⟨HQw, Hvr, Hv, Hbv, HPk, #Hpre, ⟨⟨Hhk, Hrb⟩, -⟩, ⟨-, Hfkd, Hdls⟩⟩
  iunfold viewQ at Hvr Hv
  icases Hvr with ⟨Hvr, -⟩
  icases Hv with ⟨Hv, -⟩
  unfold bView bViewC
  icases Hbv with ⟨%c, Hvc, Hcw, Hcl⟩
  imod view_upd3 γ La Lb vd0 L' $$ [Hvr Hv Hvc] with ⟨-, Hv, Hvc⟩
  · iframe
  ihave HWQ := HQw $$ [Hvc Hcw Hcl]
  · iexists c; iframe
  icases HWQ with ⟨HW, -⟩
  imodintro
  iframe HW HPk Hhk Hfkd
  isplitl [Hv Hdls]
  · iexists (dlR P st.dl)
    iframe Hdls
    iexists L'
    unfold viewQ
    iframe Hv Hpre
    ipureintro; exact dlVd_of_dlsOk hd
  iapply rbSide_rbOwn γ P _ _ $$ Hrb

/-- The cache's namespace is in the commit point's mask. -/
theorem cached_cmtMask (p : GoString) : (↑(bN.@"cached") : CoPset) ⊆ cmtMask (dbNs p) := by
  intro x hx
  unfold cmtMask
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  have hb : x ∈ (↑(nroot.@"backend") : CoPset) := nclose_subseteq (nroot.@"backend") "cached" x hx
  refine ⟨⟨CoPset.mem_full, fun h' => ?_⟩, fun h' => ?_⟩
  · have h2 : x ∈ (↑(nroot.@"etcdBackendDb") : CoPset) := by
      unfold dbNs at h'
      exact nclose_subseteq _ _ x h'
    exact ndot_ne_disjoint nroot (show ("backend" : String) ≠ "etcdBackendDb" by decide) x ⟨hb, h2⟩
  · exact ndot_ne_disjoint (nroot.@"backend") (show ("cached" : String) ≠ "cmt" by decide) x ⟨hx, h'⟩

/-- **The arming step at an `Unlock` window's commit point**: the deposit of the clients' half
borrowed from `cacheInv` (the window open: `rtCm`'s half of the current key says so), `regs_arm` over
`obsIn_win`, the deposit put back. -/
theorem armStep_win (γ : BNames) (P : BParams) (W Pk Qw : IProp GF) (p : GoString) (st : BSess)
    (Lb L' : VData) (n : Nat) (hd : dlsOk P st L') :
    armStep (GF := GF) γ P W Pk (dbNs p)
      (iprop((bView γ 1 L' -∗ W ∗ Qw) ∗ rtCm γ P st.C st.R true ∗ cacheInv γ ∗ Pk ∗
        viewQ γ (1 : Qp).half.half (vData P (st.C, st.R)) Lb ∗ thinV γ (sData P st.S) L' ∗
        trkSide γ P st ∗ fkHalf γ P st)) st.S n := by
  intro Dc
  iintro ⟨⟨HQw, HrtCm, #Hci, HPk, Hv, #Hpre, Hhkd, Hfkh⟩, Hregs, #Hlb⟩
  have hsub := cached_cmtMask p
  iunfold cacheInv at Hci
  iinv Hci with ⟨%Cs, %k, %w0, >Hca, >#Hels, >Hcurinv, >Hcvw, >%Hcs, Hwin⟩ Hclose
  iunfold rtCm at HrtCm
  icases HrtCm with ⟨%rd, %H, %L, Hrd, Hvr, Hrvs, Hcur, Hcln, Hrbr, Hhist, %Hf, #Hha, #Hcv, Hpo, #Hauth⟩
  icombine Hcur Hcurinv gives %Hck
  have Hk := Hck.2
  simp only [Prod.mk.injEq] at Hk
  obtain ⟨rfl, rfl⟩ := Hk
  icases Hwin with (>%Hbad | ⟨%vd0, >Hbv⟩)
  · cases Hbad
  -- the arming, the deposit lent to the hypothetical update
  imod (regs_arm γ P W Pk Dc st.S n
      (iprop((bView γ 1 L' -∗ W ∗ Qw) ∗ viewQ γ (1 : Qp).half.half (vData P (st.C, st.R)) L ∗
        viewQ γ (1 : Qp).half.half (vData P (st.C, st.R)) Lb ∗ bView γ 1 vd0 ∗ Pk ∗
        thinV γ (sData P st.S) L' ∗ trkSide γ P st ∗ fkHalf γ P st))
      (obsIn_win γ P W Pk Qw st L Lb vd0 L' hd))
    $$ [HQw Hvr Hv Hbv HPk Hhkd Hfkh Hregs] with H
  · iframe HQw Hvr Hv Hbv HPk Hhkd Hfkh Hregs Hlb
    iframe Hpre
  imod H with ⟨⟨HQw, Hvr, Hv, Hbv, HPk, -, Hhkd, Hfkh⟩, Hregs, #Hlb'⟩
  -- the deposit back
  imod Hclose $$ [Hca Hcurinv Hcvw Hbv] with -
  · inext
    iexists Cs, ((st.R.ver, rd.idx) : w64 × Nat), true
    iframe Hca Hcurinv Hcvw
    iframe #
    isplitr
    · ipureintro; exact Hcs
    iright; iexists vd0; iexact Hbv
  imodintro
  isplitl [HQw HPk Hv Hhkd Hfkh Hrd Hvr Hrvs Hcur Hcln Hrbr Hhist Hpo]
  · isplitl [HQw]
    · iexact HQw
    isplitl [Hrd Hvr Hrvs Hcur Hcln Hrbr Hhist Hpo]
    · iunfold rtCm
      iexists rd, H, L
      iframe Hrd Hvr Hrvs Hcur Hcln Hrbr Hhist Hpo
      iframe #
      ipureintro; exact Hf
    isplitr
    · iunfold cacheInv; iexact Hci
    iframe HPk Hv Hhkd Hfkh Hpre
  iframe Hregs Hlb'

end lemmas

end backend
end EtcdGrove
end Perennial
