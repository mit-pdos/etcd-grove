/- Lean-first (no Rocq counterpart).

# The pure facts of a cut's rename commit (W2, `notes/wal-fsext-plan.md`, "W2 implementation log")

`cut`'s rename (`os.Rename(N.tmp, fpath)`, `os.Rename.specFileSnc`) of the pipeline's file `tmp` (in
its claim `(j, .only [tmp], ht)`) onto the free `.wal` name `bt` of the WAL directory `j` (the
invariant's claim `(j, .except X, hj)`, `tmp ∈ X`), the new segment `g`. The WAL state `s` is
unchanged; the claim is replaced by its logged successor (`cutClaim`), the WAL's layout by
`cutLay lay |H| g wr` (`Cut.lean`), with the old layout as the crash alternative, and the pending-cut
flag goes to `some dir` (`DirKeysOk … (some dir)`: the other WALs keep `alt = none`).

`cutCommit_pure` bundles what `walInvBody`'s pure conjuncts need after the commit (`CutAu.lean`'s
`walCut_osAUnc`). **Unfinished (`sorry`)**; its plan, per conjunct:
- `WalsOk`, the cut WAL: `WalDirClaim` at the new claim (`claimCoh_log`, the rename writes only `tmp`,
  in `X`, and `bt`); `cutLay_abs` (the old `WalAbsD` over `hj.cur`: the WAL's claim is the key's, since
  no other claim of `j` holds a `.wal` name; `hents`: `bt` the largest `.wal` name of `hj.cur`, from
  `nm0 < bt` and `nm0` the last segment's name: `walInos` of the sorted `.wal` names, the inodes
  `Nodup`); `CrashOkW` at `alt = some lay` (`altOk_cut`, `crashOkA_cut` from `DirKeysOk`'s `CrashOkA
  … none`, `c = none`). The other WALs: their directories are not `j` (their claims would be the key's,
  and their segments would share inodes); their crash conditions over the replaced claims as
  `crashOkW_create_other` (a crash keeping the rename is one of `cl` on `treeDel m' j bt`, which their
  directories and `jr` do not see). The inodes stay `Nodup` (`hino`). `AbsentOk` from `AbsentNone`
  (`absentOk_of_absentNone`); `DirsOk`: a lookup succeeding in `treeDel m' j bt` reads no `(j, bt)`.
- `WalsCreateOk`, `CreatingOk`, `AbsentNone`: claims of `jr` unchanged (`j ≠ jr`); a creating entry's
  `J` is not `j` (`CreatingNew`: no claim of `J` holds a `.wal` name).
- `WalsNamed`: the new segment at `bt` in the new claim; in a crash keeping the rename, the names as
  the new claim has them; in one dropping it, `g.ino` is in no `.wal` entry of `j` (the old crash
  condition puts the old segments' inodes there, the WAL named: `d.named`).
- `DirKeysOk`: the key's claim replaced, once (`claimOnce_repl`), coherent, still exclusive; the
  other WALs' `CrashOkA … none` as above.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateKeys
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutTail

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Fs WalEnc

section pure
variable [GooseExts]

/-- **The WAL directory's claim after the cut's rename** (logged at `x` by a call begun at `s0`):
`bt` now holds the new segment `i`. -/
def cutClaim (j : Ino) (X : List GoString) (hj : NamesH) (tmp bt : GoString) (i : Ino) (x s0 : Nat) :
    Claim :=
  (j, .except X, hj.log x (renFileEnt j tmp j bt i hj s0) (<[bt := .file i]> hj.cur))

/-- **`Create`'s claim of the area survives a claim of another directory replaced.** -/
theorem walsCreateOk_cut {jr : Ino} {cl : List Claim} {c0 c1 : Claim} (h0 : c0.1 ≠ jr)
    (h : WalsCreateOk jr cl) : WalsCreateOk jr (replClaim c0 c1 cl) := by
  classical
  intro nm hnm
  obtain ⟨N, hN, hm, hMem⟩ := h nm hnm
  refine ⟨N, hN, ?_, hMem⟩
  have := mem_replClaim (c0 := c0) (c1 := c1) hm
  rwa [if_neg (fun e => h0 (by rw [← e]))] at this

/-- **The pure facts after a cut's rename commit** (see the file header). The old state: the
invariant's pure conjuncts (`hW` … `hDK`, no cut pending), the WAL `d` of `dir` with its layout `lay`
(the last segment `g0`), its key `(j, X)` and claim `(j, .except X, hj)`. The old tail synced and
truncated (`hm`, `hlast0`), the cuts below `|H|`. The names: `nm0` holds the old tail, `bt` (free, a
`.wal` name past `nm0`, its index past the history's) the new segment. The new segment `g`: its bytes
the stream of the new segment (`wr` bytes) then zeros, durable, its `OsMeta` sized to them, a fresh
inode. The rename: `tmp ∈ X`, begun after the claim's last entry. -/
theorem cutCommit_pure {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat}
    {CR : GMap GoString (NameSet × NamesH × Ino)} {K : GMap GoString (Ino × List GoString)}
    {dir : GoString} {d : WalDur} {lay : WalLay} {g0 g : SegG} {j : Ino} {X : List GoString}
    {hj : NamesH} {tmp bt nm0 : GoString} {x s0 wr sq ix : Nat}
    (hW : WalsOk C Mr R jr s Ls cl n) (hWC : WalsCreateOk jr cl) (hCO : CreatingOk jr cl CR)
    (hAN : AbsentNone s jr cl n) (hDA : DirsAvoid R jr s) (hNm : WalsNamed Ls cl n)
    (hDK : DirKeysOk C Mr jr s Ls cl n K none) (hK : K !! dir = some (j, X))
    (hd : s.wal !! dir = some d) (hl : Ls !! dir = some lay) (hg0 : lay.segs.getLast? = some g0)
    (hc0 : ClaimOnce (j, .except X, hj) cl)
    (hm : d.m = d.H.length) (hnamed : d.named = true)
    (hlast0 : g0.bs = (segStream C Mr d lay.cuts lay.cuts.length).map durB)
    (hcuts : ∀ b ∈ lay.cuts, b < d.H.length)
    (hnm0 : walNameP nm0 = true ∧ hj.cur !! nm0 = some (.file g0.ino))
    (hbt : bt = walFileName sq ix ∧ walLastIdx (histM d) + 1 ≤ ix ∧ go.GoStringLt nm0 bt)
    (hbtw : walNameP bt = true) (hcur : hj.cur !! bt = none)
    (hwr : wr = (segStream C Mr d (lay.cuts ++ [d.H.length]) (lay.cuts.length + 1)).length)
    (hbs : g.bs = ((segStream C Mr d (lay.cuts ++ [d.H.length]) (lay.cuts.length + 1)) ++
      List.replicate (g.bs.length - wr) 0).map durB ∧ wr ≤ g.bs.length)
    (hmeta : g.om.size = g.bs.length ∧ g.om.cut = none ∧ g.om.lo = g.bs.length ∧
      g.om.hi = g.bs.length)
    (hfit : RecsFit C (recsOfSegs C Mr d.metadata (segsOf (histM d) (lay.cuts ++ [d.H.length]))))
    (hz : g.bs.length - wr = 0 ∨ 8 ≤ g.bs.length - wr)
    (hino : ∀ g' ∈ segsAll Ls, g'.ino ≠ g.ino) (hgname : g.name = bt)
    (htmpX : tmp ∈ X) (hs0 : hj.next ≤ s0) (hsx : s0 ≤ x) :
    WalsOk C Mr R jr s (<[dir := cutLay lay d.H.length g wr]> Ls)
        (replClaim (j, .except X, hj) (cutClaim j X hj tmp bt g.ino x s0) cl) n ∧
      WalsCreateOk jr (replClaim (j, .except X, hj) (cutClaim j X hj tmp bt g.ino x s0) cl) ∧
      CreatingOk jr (replClaim (j, .except X, hj) (cutClaim j X hj tmp bt g.ino x s0) cl) CR ∧
      AbsentNone s jr (replClaim (j, .except X, hj) (cutClaim j X hj tmp bt g.ino x s0) cl) n ∧
      WalsNamed (<[dir := cutLay lay d.H.length g wr]> Ls)
        (replClaim (j, .except X, hj) (cutClaim j X hj tmp bt g.ino x s0) cl) n ∧
      DirKeysOk C Mr jr s (<[dir := cutLay lay d.H.length g wr]> Ls)
        (replClaim (j, .except X, hj) (cutClaim j X hj tmp bt g.ino x s0) cl) n K (some dir) := by
  obtain ⟨-, -, -, -, hjjr, -⟩ := hDK.1 dir j X hK
  exact ⟨sorry, walsCreateOk_cut hjjr hWC, sorry, sorry, sorry, sorry⟩

end pure

end WalFs
end EtcdGrove
end Perennial

end
