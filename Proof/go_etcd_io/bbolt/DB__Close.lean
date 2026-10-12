module
public import Spec.go_etcd_io.bbolt.DB__Close
public import Spec.go_etcd_io.bbolt.DB__close

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

theorem DB.Close.wp_proof (hclose : DB.close.spec (GF := GF) (hG := hG)) :
    DB.Close.spec (GF := GF) (hG := hG) := by
  intro I dbl γ σ hf
  wp_start as Hdb
  simp only [ownDB]
  iNamed Hdb
  have hok := Hok
  obtain ⟨Hdata', Hps', Hdsz, Hm0, Hm1, Hopen, Hfile', Hfl', Hrw, Hdbl⟩ := Hdv
  isimp only [dbPlain] at Hplain
  iNamed Hplain
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  -- the write lock: no writer can be open (it holds the lock)
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hrwlock] as ⟨Hrwlocked, -⟩
  by_cases hrw0 : σ.rwtx = null
  rotate_left
  · rw [decide_eq_false hrw0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexfalso
    iapply sync.ownMutex_exclusive $$ Hrwl Hrwlocked
  rw [decide_eq_true hrw0]
  have hwr : σ.wr = none := (hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).2 hrw0
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmetalock] as ⟨Hmlocked, -⟩
  try wp_auto
  -- the mapping's write lock: no reader can be open (each holds a read lock)
  have hrs := hok.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  ihave Hmmaph := (show ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders -
      σ.readers.size) (), sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok (GF := GF) γ.mmap))
      ⊢ sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok γ.mmap) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size - 1) (),
          sync.ownRWMutex (structFieldRef DB go!"mmaplock" dbl) (mmapTok γ.mmap)) from by
    rw [show Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size =
      (Int.toNat sync.rwmutex.actualMaxReaders - σ.readers.size - 1) + 1 by omega, List.replicate_succ]
    exact BigSepL.bigSepL_cons.1) $$ Hmmaph
  icases Hmmaph with ⟨Hmh, Hmmaph⟩
  wp_apply sync.RWMutex.wp_Lock _ _ $$ [$Hmh] as ⟨Hlocked, Htok1⟩
  try wp_auto
  icases mmapTok_full_none γ.mmap σ.readers $$ [Htok1 Htoks] with ⟨%hM, Htok1⟩
  · iframe
  -- close: all of the mapping and the fields are the database's
  have hfr := frem_whole σ v0 v1 hok hM hwr
  rw [hfr] at *
  ihave Hmr := close_gather σ v0 v1 hok hM hwr $$ [Hslots Htail]
  · iframe
  iStructNamed ops
  rw [hrw0] at *
  simp only [flfQ, ↓reduceIte]
  rw [Hfile', Hopen]
  wp_apply hclose dbl σ.file σ.fd σ.bs σ.path dv.path' dv.readOnly' dv.freelist' dv.ops'.writeAt'
    dv.dataref' σ.data dv.datasz' dv.meta0' dv.meta1' σ.sz
    $$ [opened Hflf writeAt meta0 meta1 dataref Hdata datasz Hbytes Hmap Hmr file readOnly path Hfp]
    as %err Hres
  · iframe
    iright
    iframe; iframe #
    isplitr
    · ipureintro; exact hf
    rw [Hdr]
    iright
    iframe
    ipureintro
    exact ⟨loc_ne_null_of_car _ hok.2.2.2.2.1, rfl, rfl⟩
  try wp_auto
  icases Hres with ⟨-, -, -, -, -, -, -, -, -, -, -, Hfs⟩
  wp_apply sync.RWMutex.wp_Unlock _ _ $$ [$Hlocked $Htok1] as -
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmetalock $Hmlocked]
  · iframe; inext; itrivial
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hrwlock $Hrwlocked]
  · iframe; inext; itrivial
  try wp_auto
  iapply HΦ
  icases Hfs with (%Hn | Hfs)
  · exact absurd Hn hf
  iexact Hfs

end proof

end bbolt
end EtcdGrove
end Perennial
