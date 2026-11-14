/- Lean-first (no Rocq counterpart).

# The segments' size bound (`WalsBounded`'s other half; the plan's W1 log, fifteenth session)

The decoder's reads need `|g.bs| + 2^12 < 2^62` for every segment a reader opens
(`walDecFiles_mk`). No invariant conjunct holds it: the bound is the model's (no file is larger than
ext4's `s_maxbytes` on configuration C, `0xffffffff000`), read off a segment's `OsMeta` before a step.

**`OsMetaSizeLaw`** (a named hypothesis, the coordinator's decision of 2026-11-14) is that rule, with
the statement of `wal-maxb14`'s `Fs.wp_osMeta_size` (`GooseLang/Ext/Fs/Specs.lean` there,
`maxBytes = 0xffffffff000`): once that lands, it is discharged by that lemma and goes. It bounds the
page cache's size, `g.om.size`, which a pinned segment has equal to `|g.bs|` (`WalAbsD.metas`); it is
read at the step, so nothing has to keep it across writes, resizes or crashes (the bound on `g.om.hi`
the thirteenth session's design kept in the invariant is not needed).

`wp_segs_size` reads it off a list of segments' `segRes`.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- **No file is larger than `0xffffffff000`** (hypothesis; see the file header): before any step of
a non-value `e`, an `OsMeta` at hand has its size at most ext4's `s_maxbytes` on C. -/
def OsMetaSizeLaw : Prop :=
  ∀ (s : Stuckness) (E : CoPset) (e : Expr) (Φ : val → IProp GF), toVal e = none →
    ∀ (i : Ino) (dq : DFrac) (m : OsMeta),
    ⊢ osMeta (L := L) i dq m -∗
      (⌜m.size ≤ 0xffffffff000⌝ -∗ osMeta (L := L) i dq m -∗ WP e @ s; E {{ Φ }}) -∗
      WP e @ s; E {{ Φ }}

/-- **The segments' size bound before a step** (`OsMetaSizeLaw` over a list of segments). -/
theorem wp_segs_size (hlaw : OsMetaSizeLaw (L := L)) (s : Stuckness) (E : CoPset) (e : Expr)
    (Φ : val → IProp GF) (he : toVal e = none) (gs : List SegG) :
    ⊢ ([∗list] g ∈ gs, segRes (L := L) g) -∗
      (⌜∀ g ∈ gs, g.om.size ≤ 0xffffffff000⌝ -∗ ([∗list] g ∈ gs, segRes (L := L) g) -∗
        WP e @ s; E {{ Φ }}) -∗
      WP e @ s; E {{ Φ }} := by
  induction gs with
  | nil =>
    iintro Hs Hk
    iapply Hk $$ [] Hs
    ipureintro; intro g hg; simp at hg
  | cons g gs ih =>
    iintro Hs Hk
    icases (BigSepL.bigSepL_cons (Φ := fun _ x => segRes (L := L) x)).1 $$ Hs with ⟨Hg, Hs⟩
    iunfold segRes at Hg
    icases Hg with ⟨Hm, Hb⟩
    iapply hlaw s E e Φ he g.ino _ g.om $$ Hm
    iintro %hg Hm
    iapply ih $$ Hs
    iintro %hgs Hs
    iapply Hk
    · ipureintro
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hg
      · exact hgs x hx
    iapply (BigSepL.bigSepL_cons (Φ := fun _ x => segRes (L := L) x)).2
    iframe Hs
    unfold segRes
    iframe

end iris

end WalFs
end EtcdGrove
end Perennial

end
