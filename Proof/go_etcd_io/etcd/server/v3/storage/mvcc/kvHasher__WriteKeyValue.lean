/-
The proof of `Spec/.../mvcc/kvHasher__WriteKeyValue.lean` (prove-etcdint3, 2026-11-21; until then an
axiom).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.kvHasher__WriteKeyValue
public import Spec.hash.crc32.digest__Write
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.BytesToRev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.BytesToBucketKey
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Revision__GreaterThan

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.kvHasher.WriteKeyValue.wp_proof (hBR : mvcc.BytesToRev.spec (GF := GF) (hG := hG))
    (hGT : mvcc.Revision.GreaterThan.spec (GF := GF) (hG := hG))
    (hBK : mvcc.BytesToBucketKey.spec (GF := GF) (hG := hG))
    (hWrite : hash.crc32.digest.Write.spec (GF := GF) (hG := hG)) :
    mvcc.kvHasher.WriteKeyValue.spec (GF := GF) (hG := hG) := by
  intro hp h keep dq K key val k v dk dv
  wp_start as ⟨Hh, Hok, %Hk, Hkeep, Hkey, Hval⟩
  obtain ⟨⟨r, rest, rfl, hrest, hr1, hr2⟩, hkeep⟩ := Hk
  iunfold mvcc.kvHasherOk at Hok
  icases Hok with ⟨%d, %tab, %c, %Hhash, Hd, #Ht⟩
  ihave #Hc32 : isPkgInit (PROP := IProp GF) pkg_id.hash.crc32 $$ []
  · iPkgInit
  wp_auto
  wp_apply (hBR key r rest dk hrest hr1 hr2) $$ [$Hkey] as Hkey
  -- `upper.GreaterThan(kr)`: the pointer wrapper, then the value method
  rw [method_unfold (t := go.GoType.PointerType Revision.ty) (m := go!"GreaterThan")]
  wp_auto
  wp_apply hGT
  cases (mvcc.revOf ({ Main' := h.revision' + W64 1, Sub' := 0 } : Revision)).gt (mvcc.revOf (mvcc.revVal r))
  · -- not above the hasher's revision: skipped
    wp_auto
    iapply HΦ
    iframe Hh Hkeep Hkey Hval
    iunfold mvcc.kvHasherOk
    iexists d, tab, _
    iframe Hd Ht
    ipureintro; exact Hhash
  wp_auto
  wp_apply (hBK key r rest dk hrest hr1 hr2) $$ [$Hkey] as Hkey
  rw [method_unfold (t := go.GoType.PointerType Revision.ty) (m := go!"GreaterThan")]
  wp_auto
  wp_apply hGT
  generalize (mvcc.revOf ({ Main' := h.compactRevision' + W64 1, Sub' := 0 } : Revision)).gt
    (mvcc.revOf (mvcc.revVal r)) = g
  cases g
  · wp_auto
    wp_if_destruct
    · wp_if_destruct
      · iapply HΦ
        iframe Hh Hkeep Hkey Hval
        iunfold mvcc.kvHasherOk
        iexists d, tab, _
        iframe Hd Ht
        ipureintro; exact Hhash
      · rw [Hhash]
        wp_auto
        wp_apply hWrite $$ [Hd Hkey] as ⟨Hd, Hkey⟩
        · iframe Ht; iframe
        wp_auto
        rw [Hhash]
        wp_auto
        wp_apply hWrite $$ [Hd Hval] as ⟨Hd, Hval⟩
        · iframe Ht; iframe
        iapply HΦ
        iframe Hh Hkeep Hkey Hval
        iunfold mvcc.kvHasherOk
        iexists d, tab, _
        iframe Hd Ht
        ipureintro; exact Hhash
    · rw [Hhash]
      wp_auto
      wp_apply hWrite $$ [Hd Hkey] as ⟨Hd, Hkey⟩
      · iframe Ht; iframe
      wp_auto
      rw [Hhash]
      wp_auto
      wp_apply hWrite $$ [Hd Hval] as ⟨Hd, Hval⟩
      · iframe Ht; iframe
      iapply HΦ
      iframe Hh Hkeep Hkey Hval
      iunfold mvcc.kvHasherOk
      iexists d, tab, _
      iframe Hd Ht
      ipureintro; exact Hhash
  · wp_auto
    rw [hkeep]
    wp_apply (wp_map_len keep K dq) $$ [$Hkeep] as Hkeep
    wp_if_destruct
    · rw [hkeep]
      wp_apply (wp_map_lookup2 Revision.ty (go.GoType.StructType []) keep K (mvcc.revVal r) dq)
        $$ [$Hkeep] as Hkeep
      wp_if_destruct
      · wp_if_destruct
        · wp_if_destruct
          · iapply HΦ
            iframe Hh Hkeep Hkey Hval
            iunfold mvcc.kvHasherOk
            iexists d, tab, _
            iframe Hd Ht
            ipureintro; exact Hhash
          · rw [Hhash]
            wp_auto
            wp_apply hWrite $$ [Hd Hkey] as ⟨Hd, Hkey⟩
            · iframe Ht; iframe
            wp_auto
            rw [Hhash]
            wp_auto
            wp_apply hWrite $$ [Hd Hval] as ⟨Hd, Hval⟩
            · iframe Ht; iframe
            iapply HΦ
            iframe Hh Hkeep Hkey Hval
            iunfold mvcc.kvHasherOk
            iexists d, tab, _
            iframe Hd Ht
            ipureintro; exact Hhash
        · rw [Hhash]
          wp_auto
          wp_apply hWrite $$ [Hd Hkey] as ⟨Hd, Hkey⟩
          · iframe Ht; iframe
          wp_auto
          rw [Hhash]
          wp_auto
          wp_apply hWrite $$ [Hd Hval] as ⟨Hd, Hval⟩
          · iframe Ht; iframe
          iapply HΦ
          iframe Hh Hkeep Hkey Hval
          iunfold mvcc.kvHasherOk
          iexists d, tab, _
          iframe Hd Ht
          ipureintro; exact Hhash
      · iapply HΦ
        iframe Hh Hkeep Hkey Hval
        iunfold mvcc.kvHasherOk
        iexists d, tab, _
        iframe Hd Ht
        ipureintro; exact Hhash
    · wp_if_destruct
      · wp_if_destruct
        · iapply HΦ
          iframe Hh Hkeep Hkey Hval
          iunfold mvcc.kvHasherOk
          iexists d, tab, _
          iframe Hd Ht
          ipureintro; exact Hhash
        · rw [Hhash]
          wp_auto
          wp_apply hWrite $$ [Hd Hkey] as ⟨Hd, Hkey⟩
          · iframe Ht; iframe
          wp_auto
          rw [Hhash]
          wp_auto
          wp_apply hWrite $$ [Hd Hval] as ⟨Hd, Hval⟩
          · iframe Ht; iframe
          iapply HΦ
          iframe Hh Hkeep Hkey Hval
          iunfold mvcc.kvHasherOk
          iexists d, tab, _
          iframe Hd Ht
          ipureintro; exact Hhash
      · rw [Hhash]
        wp_auto
        wp_apply hWrite $$ [Hd Hkey] as ⟨Hd, Hkey⟩
        · iframe Ht; iframe
        wp_auto
        rw [Hhash]
        wp_auto
        wp_apply hWrite $$ [Hd Hval] as ⟨Hd, Hval⟩
        · iframe Ht; iframe
        iapply HΦ
        iframe Hh Hkeep Hkey Hval
        iunfold mvcc.kvHasherOk
        iexists d, tab, _
        iframe Hd Ht
        ipureintro; exact Hhash

end proof

end EtcdGrove
end Perennial
