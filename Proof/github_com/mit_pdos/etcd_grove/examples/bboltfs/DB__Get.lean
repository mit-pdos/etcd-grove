/- Lean-first (no Rocq counterpart). The proof of `db.Get()`.

Proved: every error path (a failed handle; no mapping, `meta0 == nil`). Not proved (`sorry`):
the success path, which needs changes in `DB.lean`:
- the mapped cells the reader loads (the two metas in `db.meta()` and `*db.meta()`, the root
  page's `count` and value) are in the mapping's invariant (`mapInv`, an `inv`), but a Go load
  is not atomic: every byte is a `Read`, a `StartRead` and a `FinishRead` (two atomic steps,
  `_internal_wp_untyped_read`), and a scalar or struct load reads byte after byte
  (`wp_readBytes`), `db.meta()` many loads; so the invariant cannot be opened around a load. The
  reader needs fractions of those cells for the duration of its loads (lent by the invariant
  while it holds the read lock, and the meta cells while it also holds `metalock`);
- `metaR` gives only `T !! txid = some (pageVal B)` with `ghostMapAuth γ.txs`, from which no
  `dbTx γ txid _` (a fragment) can be made: `metaR` needs `dbTx` of the current transaction;
- `dbReader` does not pin the path: its `mapR γ db f' fd' p'` may name another path than
  `isDB`'s, and the root page's bytes in the invariant (`pageIs p' r B'`) cannot be related to
  `metaR`'s (`pageIs p r B`) without `p = p'`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__Get
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__meta
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.pageAt
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

theorem DB.Get.wp_proof (wp_meta : DB.«meta».spec (GF := GF) (hG := hG))
    (wp_pageAt : pageAt.spec (GF := GF) (hG := hG)) :
    DB.Get.spec (GF := GF) (hG := hG) := by
  intro γ db t
  wp_start as ⟨Hdb, Hrd, Hlast⟩
  iunfold isDB at Hdb
  icases Hdb with ⟨%f, %fd, %p, #Hpkg, #Hos, #Hfile, #Hpath, #Hrw, #Hmeta, #Hguard⟩
  iunfold dbReader at Hrd
  icases Hrd with ⟨%f', %fd', %p', #Hfile', #Hpath', Hrd⟩
  iunfold pkgFacts at Hpkg
  icases Hpkg with ⟨#Hsync, %e1, %e2, #He1, #He2, %He, %eof, #Heof, %Heof⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock db.[DB, go!"metalock"] (metaR (GF := GF) γ db p) $$ [$Hmeta $Hsync]
    as ⟨Hlocked, HR⟩
  iunfold metaR at HR
  icases HR with ⟨%b, %mp, %mx, %hwm, %mxc, %T, Hfl, Hcur, Hmb, %Hmx, Hauth, Hout, Hrest⟩
  wp_auto
  cases b with
  | true =>
    wp_auto
    wp_apply sync.Mutex.wp_Unlock db.[DB, go!"metalock"] (metaR (GF := GF) γ db p)
      $$ [$Hmeta $Hsync $Hlocked Hfl Hcur Hmb Hauth Hout Hrest]
    · iunfold metaR
      iexists true, mp, mx, hwm, mxc, T
      iframe
      ipureintro; exact Hmx
    (try wp_auto)
    iapply HΦ
    isplitl [Hrd]
    · iunfold dbReader; iexists f', fd', p'; iframe; iframe #
    iright; ipureintro; exact He.1
  | false =>
    wp_auto
    wp_apply sync.RWMutex.wp_RLock db.[DB, go!"mmaplock"] (mapR (GF := GF) γ db f' fd' p')
      $$ [$Hrd $Hsync] as ⟨Hrl, HM⟩
    iunfold mapR at HM
    icases HM with ⟨%st, HM⟩
    iunfold mapBody at HM
    icases HM with ⟨Hmap, Hflds, Hmr⟩
    rcases st with _ | ⟨base, len, γm⟩
    · dsimp only [mapFields, mapRest]
      icases Hflds with ⟨Hd, H0, H1⟩
      wp_auto
      wp_apply sync.RWMutex.wp_RUnlock db.[DB, go!"mmaplock"] (mapR (GF := GF) γ db f' fd' p')
        $$ [$Hrl $Hsync Hmap Hd H0 H1] as Hrd
      · iunfold mapR; iexists none; iunfold mapBody
        dsimp only [mapFields, mapRest]
        iframe
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock db.[DB, go!"metalock"] (metaR (GF := GF) γ db p)
        $$ [$Hmeta $Hsync $Hlocked Hfl Hcur Hmb Hauth Hout Hrest]
      · iunfold metaR
        iexists false, mp, mx, hwm, mxc, T
        iframe
        ipureintro; exact Hmx
      (try wp_auto)
      iapply HΦ
      isplitl [Hrd]
      · iunfold dbReader; iexists f', fd', p'; iframe; iframe #
      iright; ipureintro; exact He.1
    · dsimp only [mapFields, mapRest]
      icases Hflds with ⟨Hd, H0, H1⟩
      icases Hmr with ⟨%Hbase, Htok, #Hinv, Hf, Hfd⟩
      wp_auto
      -- The meta copy `*db.meta()` is blocked on `DB.lean` (see the file header).
      sorry

end proof

end bboltfs
end EtcdGrove
end Perennial
