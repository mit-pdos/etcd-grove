/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/store__Commit.lean` (D22 S-l's sender items,
2026-10-22). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Commit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.mu.Lock()` gives the whole of `s.mu`'s resource, whose share of the fields the writer's
fragment pins at `γ`'s names: `s.b` is the backend of `γ`'s contract (`physOk`), whose
`ForceCommit()` takes the writer's reader token and a write session's token. -/
theorem mvcc.store.Commit.wp_proof : mvcc.store.Commit.spec (GF := GF) (hG := hG) := by
  intro s γ X Y
  wp_start as ⟨#Hs, Hfr, Hro, Hwt, HX, #Hrq⟩
  ihave #Hs' := Hs
  iunfold mvcc.isStore at Hs'
  iNamed Hs'
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_Lock_guard $$ [$Hmu] as ⟨Hwl, HmuP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.muInv s γ 1)) $$ Hlc1 HmuP with HmuP
  iunfold mvcc.muInv at HmuP
  icases HmuP with ⟨%c, Hmi, Hwr, Hfs⟩
  -- the writer's fragment pins the fields' share at `γ`'s names
  iunfold mvcc.writerFrag at Hfr
  icases Hfr with ⟨%o, Hpin⟩
  icases mvcc.fieldShare_pin s γ _ _ o $$ [$Hpin $Hfs] with ⟨Hpin, Hfs⟩
  iunfold mvcc.fieldShareAt at Hfs
  iNamed Hfs
  iunfold mvcc.storeFields at Hflds
  iNamed Hflds
  ihave #Hph' := Hph
  iunfold mvcc.physOk at Hph'
  iNamed Hph'
  iunfold mvcc.isKeyBackendG at Hbk
  icases Hbk with ⟨%bi, %Hbi, -, -, -, #HForce, -⟩
  (try wp_auto)
  rw [Hbi]
  (try wp_auto)
  -- `s.b.ForceCommit()`
  wp_bind (App (Val #(methods bi.ty go!"ForceCommit" bi.v)) (Val #()))
  iapply HForce $$ %X %Y [Hro Hwt HX] [-]
  · iunfold mvcc.writerOwn at Hro
    iframe Hro Hwt HX
    iframe #
  inext
  iintro ⟨Hro, HY⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hmi Hwr Hcur Hfb Hfidx Hfsch Hfstop Hfrst]
  · inext
    iunfold mvcc.muInv
    iexists c
    iframe Hmi Hwr
    iapply mvcc.fieldShare_of_at
    iunfold mvcc.fieldShareAt
    iframe Hcur Hfrst Hph
    iunfold mvcc.storeFields
    simp only [named]
    rw [Hbi]
    iframe Hfb Hfidx Hfsch Hfstop
  (try wp_auto)
  iapply HΦ
  iunfold mvcc.writerOwn
  iframe Hro HY
  iunfold mvcc.writerFrag
  iexists o
  iexact Hpin

end proof

end EtcdGrove
end Perennial
