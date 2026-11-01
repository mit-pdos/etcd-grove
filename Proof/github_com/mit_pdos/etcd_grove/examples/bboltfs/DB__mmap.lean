/- Lean-first (no Rocq counterpart). The proof of `db.mmap(minsz)`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__mmap
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__munmap
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.mmapSize
public import Spec.os.File__Fd
public import Spec.golang_org.x.sys.unix.Mmap
public import Spec.golang_org.x.sys.unix.Madvise
public import Spec.golang_org.x.sys.unix.Munmap
public import Perennial.Proof.sync.Results

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

theorem DB.mmap.wp_proof (wp_munmap : DB.munmap.spec (GF := GF) (hG := hG))
    (wp_mmapSize : mmapSize.spec (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Mmap : golang_org.x.sys.unix.Mmap.spec (GF := GF) (hG := hG))
    (wp_Madvise : golang_org.x.sys.unix.Madvise.spec (GF := GF) (hG := hG))
    (wp_Munmap : golang_org.x.sys.unix.Munmap.spec (GF := GF) (hG := hG)) :
    DB.mmap.spec (GF := GF) (hG := hG) := by
  intro γ db f fd p minsz mp fl hwm st m Hmin0 Hmin Hsz
  wp_start as ⟨#Hpkg, #Hos, #Hfile, #Hguard, Hcur, Hmap, Hout, Hflds, Hw, Hpre⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  iunfold pkgFacts at Hpkg
  icases Hpkg with ⟨#Hsync, -⟩
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlocked, HR⟩
  unfold mapR mapBody
  icases HR with ⟨%st0, Hmap0, Hflds0, HR⟩
  icombine Hmap Hmap0 gives % ⟨_, Heq⟩
  subst Heq
  unfold writerFile
  icases Hw with ⟨%mxc, %tail, Hfsz, Hdsz, Hf, Hfd, Hm, Hmx, Htail, %Hw⟩
  wp_auto
  sorry

end proof

end bboltfs
end EtcdGrove
end Perennial
