/- Lean-first (no Rocq counterpart). The proof of `db.munmap()`'s crash-aware spec: as
`DB__munmap.lean`'s, with `Munmap.specCrashS`, whose obligation is `writer_okS`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__munmapCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__munmap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

theorem DB.munmap.wp_proof_crash
    (wp_Munmap : golang_org.x.sys.unix.Munmap.specCrashS (GF := GF) (hG := hG)) :
    DB.munmap.specCrash (GF := GF) (hG := hG) := by
  intro db dq sl dsz m0 m1 p γc m bs fa fb Hdq
  wp_start as ⟨Hd, Hs, H0, H1, Hm⟩
  unfold mappingResC
  icases Hm with (%Hnil | ⟨%base, %len, %vf, %Hsl, #Hos, #Hinv, Hm, Hc⟩)
  · subst Hnil
    wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    iframe
    unfold unmappedResC
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  · obtain ⟨rfl, Hpos, Hlen, Hb, hl, hcc⟩ := Hsl
    have hne : ({ ptr := base, len := len, cap := len } : GoSlice) ≠ slice.nil := by
      intro h; have := congrArg GoSlice.ptr h; simp [slice.nil] at this; subst this
      simp [null] at Hpos
    obtain rfl := Hdq hne
    wp_auto
    rw [decide_eq_false hne]
    wp_auto
    wp_apply wp_Munmap base len p dbCrashN γc (dbOk p) m bs fa fb vf Hlen Hb dbCrashN_disj
        (writer_okS fa fb hl hcc _) $$ [Hos Hinv Hm Hc] as %e He
    · iframe; iframe #
    (try wp_auto)
    iapply HΦ
    simp only [hne, ↓reduceIte]
    iframe
    unfold unmappedResC
    iright
    iexists base, len, vf, e
    iframe
    ipureintro; exact ⟨rfl, rfl⟩

end proof

end bboltfs
end EtcdGrove
end Perennial
