/-
The lemmas of `DB__init.lean`'s proof (`osBytes_append`, `init_join1`, `synced_eq`, ...), in a module of
their own so that `DB__initCrash.lean` imports them without the proof (import tiers, 2026-11-18).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__init
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.initPages
public import Spec.os.File__WriteAt
public import Spec.os.File__Fd
public import Spec.syscall.Fdatasync
public import Spec.os.CrashSt
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Writer

@[expose] public section

noncomputable section

namespace Perennial

open Fs
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

section osbytes
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

theorem osBytes_append (p : Ino) (off : Nat) (dq : DFrac) (xs ys : List ByteG) :
    osBytes (L := L) p off dq (xs ++ ys) ⊣⊢
      osBytes (L := L) p off dq xs ∗ osBytes (L := L) p (off + xs.length) dq ys := by
  unfold osBytes; exact bytesG_append _ _ _ _ _ _

/-- After the first write: its four pages, then the bytes after them, as one. -/
theorem init_join1 (p : Ino) (xs ys : List ByteG) (n : Nat) (hys : ys.length = n) :
    osBytes (L := L) p 0 (DFrac.own 1) ys ∗
      osBytes (L := L) p (0 + (xs.take n).length) (DFrac.own 1) (xs.drop n) ⊢
    osBytes (L := L) p 0 (DFrac.own 1) (ys ++ xs.drop n) := by
  iintro ⟨H1, H2⟩
  ihave H2 : osBytes (L := L) p n (DFrac.own 1) (xs.drop n) $$ [H2]
  · by_cases h : n ≤ xs.length
    · rw [List.length_take, show 0 + min n xs.length = n by omega]; iexact H2
    · rw [List.drop_eq_nil_of_le (show xs.length ≤ n by omega)]
      unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
  iapply (osBytes_append p 0 _ _ _).2
  rw [hys, Nat.zero_add]; iframe

theorem pwPost_synced_maps (m : OsMeta) (off n k : Nat) : (pwPost m off n k).synced.maps = m.maps :=
  announce_maps m _ _ (max m.size (off + n))

theorem pwPost_synced_size (m : OsMeta) (off n k : Nat) :
    (pwPost m off n k).synced.size = pwSize m.size off k := rfl

/-- Two synced `OsMeta`s of the same size and mappings are the same. -/
theorem synced_eq (m1 m2 : OsMeta) (hs : m1.size = m2.size) (hm : m1.maps = m2.maps)
    (hc : m1.cut = m2.cut) (hz : m1.cz = m2.cz) : m1.synced = m2.synced := by
  cases m1; cases m2; simp only at hs hm hc hz; subst hs; subst hm; subst hc; subst hz; rfl

end osbytes
section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

end proof

end osfs_bboltfs
end EtcdGrove
end Perennial
