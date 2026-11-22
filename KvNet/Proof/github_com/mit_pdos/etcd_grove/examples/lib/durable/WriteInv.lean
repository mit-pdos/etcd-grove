-- The copy for the part `KvNet/` of `WalTester/Proof/github_com/mit_pdos/etcd_grove/examples/lib/durable/WriteInv.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

# `examples/lib/durable` over `fsExt`: `Write`'s invariant steps (W4c U2, `notes/wal-fsext-w4c-plan.md`)

* `durCreate_osAUnc`: the atomic update `os.OpenFile.specCreateTruncSnc` takes for the temporary's
  create: it opens `durInv` at the step (with `notCrashed`) and moves the invariant's half of the
  temporary's claim to the outcome (`crHt`).
* `durRename_osAUnc`: the update `os.Rename.specFileSnc` takes for the rename of the temporary over
  the name: at the commit the invariant's halves of both claims move to the outcome, the temporary's
  file becomes a candidate (half of its resources into the invariant), and the client's first update
  commits (`DurOk.renA`) or, after an earlier attempt's rename, the state stays (`DurOk.renB`).
* `durInv_commit`: the client's second update, at a step after the directory's sync committed every
  entry of the name's claim (`DurOk.commit`).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.WritePure
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Inv
public import GooseLang.Ext.Fs.Zeros

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace DurFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs

theorem durN_sub_au : (↑durN : CoPset) ⊆ osAuMask := by
  have h1 : (↑durN : CoPset) ## ↑osN := ndot_ne_disjoint nroot (by decide)
  have h2 : (↑durN : CoPset) ## ↑osShN := ndot_ne_disjoint nroot (by decide)
  intro p hp
  exact LawfulSet.mem_diff.2
    ⟨LawfulSet.mem_diff.2 ⟨CoPset.mem_full, fun hn => h1 p ⟨hp, hn⟩⟩, fun hn => h2 p ⟨hp, hn⟩⟩

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [os.Assumptions]

theorem durPhys_update (γ : DurGS) (p1 p2 p' : DurPhys) :
    ⊢ durPhys (GF := GF) γ p1 -∗ durPhys γ p2 ==∗ durPhys γ p' ∗ durPhys γ p' := by
  unfold durPhys
  exact ghostVar_update_halves p' γ.γp p1 p2

theorem durSt_update (γ : DurGS) (s1 s2 s' : DurSt) :
    ⊢ durSt (GF := GF) γ s1 -∗ ghostVar γ.γs (1 : Qp).half s2 ==∗
      durSt γ s' ∗ ghostVar γ.γs (1 : Qp).half s' := by
  unfold durSt
  exact ghostVar_update_halves s' γ.γs s1 s2

theorem osMeta_halves' (i : Ino) (m : OsMeta) :
    osMeta (GF := GF) i (DFrac.own 1) m ⊣⊢
      osMeta i (DFrac.own (1 : Qp).half) m ∗ osMeta i (DFrac.own (1 : Qp).half) m := by
  have h := gElem_split (gooseOsGS (GF := GF)) (gooseOsGS (GF := GF)).γm i (1 : Qp).half (1 : Qp).half m
  rw [Qp.half_add_half] at h
  exact h

theorem osBytes_halves' (i : Ino) (off : Nat) (xs : List ByteG) :
    osBytes (GF := GF) i off (DFrac.own 1) xs ⊣⊢
      osBytes i off (DFrac.own (1 : Qp).half) xs ∗ osBytes i off (DFrac.own (1 : Qp).half) xs := by
  have h := osBytes_frac (GF := GF) i off (1 : Qp).half (1 : Qp).half xs
  rw [Qp.half_add_half] at h
  exact h

/-- A file held whole is no candidate (the invariant holds half of each candidate's `OsMeta`). -/
theorem candRes_notin (i : Ino) (m : OsMeta) (cs : List DCand) :
    ⊢ osMeta (GF := GF) i (DFrac.own 1) m -∗
      ([∗list] c ∈ cs, candRes (GF := GF) c (DFrac.own (1 : Qp).half)) -∗
      ⌜i ∉ cs.map DCand.i⌝ ∗ osMeta i (DFrac.own 1) m ∗
        ([∗list] c ∈ cs, candRes c (DFrac.own (1 : Qp).half)) := by
  iintro Hm Hc
  by_cases hin : i ∈ cs.map DCand.i
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hin
    icases BigSepL.bigSepL_mem_acc hc $$ Hc with ⟨Hx, -⟩
    iunfold candRes at Hx
    icases Hx with ⟨Hm2, -⟩
    unfold osMeta
    icases gElem_valid_2 _ _ _ _ _ _ _ $$ Hm Hm2 with %hv
    exact absurd hv.1.validN (fun h => DFrac.own_whole_exclusive.exclusive0_l _ h)
  · isplitr
    · ipureintro; exact hin
    iframe Hm Hc

/-- **The temporary's create**: `os.OpenFile.specCreateTruncSnc`'s update on the invariant's half of
the temporary's claim. -/
theorem durCreate_osAUnc (γ : DurGS) (f : DFile) (p : DurPhys) :
    ⊢ durInv (GF := GF) γ f -∗ durPhys γ p -∗
      osAUnc (osNames f.J (.only [f.tb]) (DFrac.own (1 : Qp).half) p.ht)
        (crOut f.J f.tb p.ht (DFrac.own (1 : Qp).half))
        (fun o => durPhys γ { p with ht := crHt f p.ht o }) := by
  iintro #Hinv Hp
  iapply osAUnc_coiter _ _ _ (durPhys γ p) $$ [] Hp
  iintro !> Hp
  unfold osAUncPre
  iintro Hnc
  imod durInv_open γ f osAuMask durN_sub_au $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  unfold durInvBody
  icases Hb with ⟨%s, %p', Hs, Hp', Hnb, Hnt, Hlb, Hc, %hok⟩
  icases durPhys_agree γ p p' $$ Hp Hp' with %he
  subst he
  imod (fupd_mask_subseteq (show (∅ : CoPset) ⊆ osAuMask \ ↑durN from
    LawfulSet.empty_subset)) with Hcl'
  imodintro
  iframe Hnt Hnc
  isplit
  · iintro Hnt
    imod Hcl'
    imod Hcl $$ [Hs Hp' Hnb Hnt Hlb Hc] with -
    · iexists s, p; iframe; ipureintro; exact hok
    imodintro; iexact Hp
  · iintro %o Hβ
    imod Hcl'
    ihave Hnt : osNames f.J (.only [f.tb]) (DFrac.own (1 : Qp).half) (crHt f p.ht o) $$ [Hβ]
    · rcases o with _ | ⟨x, s0, i⟩
      · simp only [crOut, crHt]; iexact Hβ
      · simp only [crOut, crHt]
        icases Hβ with ⟨-, -, H⟩
        iexact H
    imod durPhys_update γ p p { p with ht := crHt f p.ht o } $$ Hp Hp' with ⟨Hp, Hp'⟩
    imod Hcl $$ [Hs Hp' Hnb Hnt Hlb Hc] with -
    · iexists s, { p with ht := crHt f p.ht o }; iframe; ipureintro; exact hok.crHt o
    imodintro; iexact Hp

/-- What the rename's update leaves its caller after the outcome `o`: nothing changed (`none`: the
resources back), or (`some (x, s)`) the physical state after the rename with the state's `alt` now
`a` (not `none`), the new candidate's other half, and the second update, still owed. -/
def durRenQ (γ : DurGS) (f : DFile) (p : DurPhys) (c : DCand) (Ψ : IProp GF) :
    Option (Nat × Nat) → IProp GF
  | none => iprop(durPhys γ p ∗ osMeta c.i (DFrac.own 1) c.m ∗
      osBytes c.i 0 (DFrac.own 1) (c.v.map durB) ∗ durWOwe γ f c.v p Ψ)
  | some (x, s) => iprop(∃ a, ⌜a ≠ none⌝ ∗ durPhys γ (renPhys f p c a x s) ∗
      candRes c (DFrac.own (1 : Qp).half) ∗ durWriteSync γ Ψ)

theorem renPhys_curIs (f : DFile) (p : DurPhys) (c : DCand) (a : Option (Option GoString))
    (x s : Nat) : (renPhys f p c a x s).CurIs f (some c.v) := by
  unfold DurPhys.CurIs
  simp only [renPhys, NamesH.log, GMap.lookup_insert]
  exact ⟨c, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩

/-- **The rename of the temporary over the name**: `os.Rename.specFileSnc`'s update on the
invariant's halves of the two claims. -/
theorem durRename_osAUnc (γ : DurGS) (f : DFile) (p : DurPhys) (c : DCand) (Ψ : IProp GF)
    (hc : c.Ok) :
    ⊢ durInv (GF := GF) γ f -∗ durRenQ γ f p c Ψ none -∗
      osAUnc iprop(osNames f.J (.only [f.tb]) (DFrac.own (1 : Qp).half) p.ht ∗
          osNames f.J (.only [f.b]) (DFrac.own (1 : Qp).half) p.hb)
        (renFileOut f.J f.J c.i (.only [f.tb]) (.only [f.b]) f.tb f.b p.ht p.hb
          (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half))
        (durRenQ γ f p c Ψ) := by
  iintro #Hinv HP
  iapply osAUnc_coiter _ _ _ (durRenQ γ f p c Ψ none) $$ [] HP
  iintro !> HP
  unfold osAUncPre
  iintro Hnc
  imod durInv_open γ f osAuMask durN_sub_au $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  unfold durInvBody
  icases Hb with ⟨%s, %p', Hs, Hp', Hnb, Hnt, Hlb, Hc, %hok⟩
  simp only [durRenQ]
  icases HP with ⟨Hp, Hm, Hby, Howe⟩
  icases durPhys_agree γ p p' $$ Hp Hp' with %he
  subst he
  imod (fupd_mask_subseteq (show (∅ : CoPset) ⊆ osAuMask \ ↑durN from
    LawfulSet.empty_subset)) with Hcl'
  imodintro
  isplitl [Hnt Hnb]
  · iframe Hnt Hnb
  iframe Hnc
  isplit
  · iintro ⟨Hnt, Hnb⟩
    imod Hcl'
    imod Hcl $$ [Hs Hp' Hnb Hnt Hlb Hc] with -
    · iexists s, p; iframe; ipureintro; exact hok
    imodintro; iframe
  · iintro %o Hβ
    rcases o with _ | ⟨x, s0⟩
    · unfold renFileOut
      simp only [logOut, claimOut]
      icases Hβ with ⟨-, Hnt, Hnb⟩
      imod Hcl'
      imod Hcl $$ [Hs Hp' Hnb Hnt Hlb Hc] with -
      · iexists s, p; iframe; ipureintro; exact hok
      imodintro; iframe
    · imod Hcl'
      unfold renFileOut
      simp only [logOut, claimOut]
      icases Hβ with ⟨-, Hnt, Hnb⟩
      icases candRes_notin c.i c.m p.cands $$ Hm Hc with ⟨%hci, Hm, Hc⟩
      icases (osMeta_halves' c.i c.m).1 $$ Hm with ⟨Hm1, Hm2⟩
      icases (osBytes_halves' c.i 0 (c.v.map durB)).1 $$ Hby with ⟨Hb1, Hb2⟩
      unfold durWOwe
      icases Howe with (⟨%hA, Hau⟩ | ⟨%hB, Hsync⟩)
      · -- the first rename: the client's first update
        rw [show osAuMask \ (↑durN : CoPset) = durAuMask from rfl]
        ihave Hacc := aupd_aacc $$ Hau
        unfold atomic_acc
        imod Hacc with Hacc
        isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
        icases Hacc with ⟨%s', Hs', Hucl⟩
        icases durSt_agree γ s' s $$ Hs' Hs with %he
        subst he
        icases Hucl with ⟨-, Hcommit⟩
        isimp only [tforall_nil, Std.Tele.app] at Hcommit
        imod durSt_update γ s' s' ⟨some c.v, some s'.cur⟩ $$ Hs' Hs with ⟨Hs', Hs⟩
        imod Hcommit $$ Hs' with Hsync
        imod durPhys_update γ p p (renPhys f p c (some s'.cur) x s0) $$ Hp Hp' with ⟨Hp, Hp'⟩
        imod Hcl $$ [Hs Hp' Hnb Hnt Hlb Hc Hm1 Hb1] with -
        · iexists ⟨some c.v, some s'.cur⟩, (renPhys f p c (some s'.cur) x s0)
          iframe Hs Hp'
          simp only [renPhys_hb, renPhys_ht, renPhys_nc, renPhys_cands]
          isplitl [Hnb]
          · iexact Hnb
          isplitl [Hnt]
          · iexact Hnt
          isplitl [Hlb]
          · iexact Hlb
          isplitl [Hc Hm1 Hb1]
          · iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
            iframe Hc
            iunfold candRes; iframe
          ipureintro
          exact hok.renA hA c x s0 hc hci
        imodintro
        iexists (some s'.cur)
        iframe Hp Hsync
        isplitr
        · ipureintro; simp
        iunfold candRes; iframe
      · -- a retry's rename: the state stays
        obtain ⟨hB1, hB2⟩ := hB
        have hcur : s.cur = some c.v := DurPhys.curIs_unique hok.inj hok.curIs hB2
        imod durPhys_update γ p p (renPhys f p c p.alt x s0) $$ Hp Hp' with ⟨Hp, Hp'⟩
        imod Hcl $$ [Hs Hp' Hnb Hnt Hlb Hc Hm1 Hb1] with -
        · iexists s, (renPhys f p c p.alt x s0)
          iframe Hs Hp'
          simp only [renPhys_hb, renPhys_ht, renPhys_nc, renPhys_cands]
          isplitl [Hnb]
          · iexact Hnb
          isplitl [Hnt]
          · iexact Hnt
          isplitl [Hlb]
          · iexact Hlb
          isplitl [Hc Hm1 Hb1]
          · iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
            iframe Hc
            iunfold candRes; iframe
          ipureintro
          exact hok.renB hB1 c x s0 hc hci hcur
        imodintro
        iexists p.alt
        iframe Hp Hsync
        isplitr
        · ipureintro; exact hB1
        iunfold candRes; iframe

/-- **The client's second update**, at a step after the directory's sync committed every entry of the
name's claim (`osCommitLb n`, `n` at least its `next`; the claim coherent). -/
theorem durInv_commit (γ : DurGS) (f : DFile) (p : DurPhys) (n : Nat) (Ψ : IProp GF)
    (hcoh : HistCoh p.hb f.J (.only [f.b])) (hn : p.hb.next ≤ n) :
    ⊢ durInv (GF := GF) γ f -∗ notCrashed (hC := hG.goose_localGS.goose_crashGS) -∗ durPhys γ p -∗
      osCommitLb n -∗ durWriteSync γ Ψ ={⊤}=∗
      notCrashed (hC := hG.goose_localGS.goose_crashGS) ∗
        durPhys γ { p with nc := n, alt := none } ∗ Ψ := by
  iintro #Hinv Hnc Hp #Hlb Hau
  imod durInv_open γ f ⊤ CoPset.subseteq_top $$ Hinv Hnc with ⟨Hb, Hnc, Hcl⟩
  unfold durInvBody
  icases Hb with ⟨%s, %p', Hs, Hp', Hnb, Hnt, -, Hc, %hok⟩
  icases durPhys_agree γ p p' $$ Hp Hp' with %he
  subst he
  ihave Hau := Hau $$ Hnc
  ihave Hau := atomic_update_mask_weaken durAuMask_sub $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%s', Hs', Hucl⟩
  icases durSt_agree γ s' s $$ Hs' Hs with %he
  subst he
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_nil, Std.Tele.app] at Hcommit
  imod durSt_update γ s' s' ⟨s'.cur, none⟩ $$ Hs' Hs with ⟨Hs', Hs⟩
  imod Hcommit $$ Hs' with ⟨Hnc, HΨ⟩
  imod durPhys_update γ p p { p with nc := n, alt := none } $$ Hp Hp' with ⟨Hp, Hp'⟩
  imod Hcl $$ [Hs Hp' Hnb Hnt Hc] with -
  · iexists ⟨s'.cur, none⟩, { p with nc := n, alt := none }
    iframe Hs Hp' Hnb Hnt Hc Hlb
    ipureintro
    exact hok.commit hcoh n hn
  imodintro
  iframe

end iris

end DurFs
end EtcdGrove
end Perennial
