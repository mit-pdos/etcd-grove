/- Lean-first (no Rocq counterpart). The proof of `db.Get()`.

A Go load is not atomic (every byte is a `StartRead` and a `FinishRead`), so the reader borrows
the cells it loads from the mapping's invariant (`MapLoan.lean`): under `metalock`, the meta cells
whole (`meta_borrow`), which it views as the two typed metas for `DB.meta`'s spec and the copy
`*db.meta()`, and gives back before unlocking (`meta_return`); and a share of the root page's cells
(`page_borrow`, still under `metalock`, where the meta pages name the root page), from which it
loads the page's `count` (a typed `Page` view) and value (a `uint64` view), and which it gives back
before `RUnlock` (`page_return`). The root page's bytes are those `metaR` records (`pageIs_agree`),
so the result is `dbTx` of the current transaction.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__Get
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__meta
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.pageAt
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.MapLoan
public import Perennial.Proof.sync.Results
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__GetLemmas

@[expose] public section

noncomputable section

namespace Perennial

open Fs
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

section proof
-- `curMeta`'s body is an `if` on both meta pages: unfolded by `wp_auto` when it loads a field of
-- `m ↦ curMeta mp`, it was then unified against `curMeta mp` by unfolding again (97s to 9s)
attribute [local irreducible] curMeta
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

/-- `DB.Get.wp_reader`, the reader slot borrowed from `isDB`'s pool with the thread token and
given back after. -/
theorem DB.Get.wp_proof (wp_meta : DB.«meta».spec (GF := GF) (hG := hG))
    (wp_pageAt : pageAt.spec (GF := GF) (hG := hG)) :
    DB.Get.spec (GF := GF) (hG := hG) := by
  intro γ db t o
  wp_start_folded as ⟨#Hdb, Htok, Hlast, Hoo⟩
  iapply wp_fupd
  iapply fupd_wp
  imod dbReader_borrow γ db $$ [Htok] with ⟨Hrd, Hloan⟩
  · iframe; iframe #
  imodintro
  wp_apply DB.Get.wp_reader wp_meta wp_pageAt γ db t o $$ [$Hdb $Hrd $Hlast $Hoo]
    as %txid %v %has %err ⟨Hrd, Hoo, Hres⟩
  imod dbReader_giveBack γ db $$ [Hloan Hrd] with Htok
  · iframe
  imodintro
  iapply HΦ
  iframe

end proof

end osfs_bboltfs
end EtcdGrove
end Perennial
