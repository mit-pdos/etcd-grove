/-
Lean-first (no Rocq counterpart).

# The client closure of `Run` (2026-10-30, kvreconf-final, helper TOP)

kv's `Check.lean` on kvreconf's masks. `lintest.Run`'s `applySpec` hands `apply` a one-shot update
(Perennial's atomic-fupd style: it cannot be closed without committing), but the store's operations
take an Iris atomic update (`AU`), which they may open and abort. So the library's state `libState`
is not the store's client half `rkvVal γr` itself but a copy `rkvVal γd` (a second ghost variable
holding the same history), and the invariant `checkN` holds the client half with the other half of
the copy. The store's `AU` (`kvrAu_of_run`) opens that invariant (abort closes it back); its commit
runs `Run`'s update on the copy, at the mask `⊤ \ checkMask` (`Run`'s `Eapp` is `checkMask`, all but
`kvrMask \ checkN`: what the store's updates may open less the invariant).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.DefsCluster
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ModelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3
open github_com.anishathalye.porcupine

/-- The invariant's namespace: the store's client half, with the driver's copy. -/
abbrev checkN : Namespace := nroot.@"kvreconf_check"

/-- The library's mask (`Run`'s `Eapp`): all but what the store's updates may open, less
`checkN`. -/
def checkMask : CoPset := ⊤ \ (kvrMask \ ↑checkN)

theorem checkMask_sub : ⊤ \ checkMask ⊆ kvrMask \ ↑checkN := by
  intro p hp
  unfold checkMask at hp
  rw [LawfulSet.mem_diff, LawfulSet.mem_diff] at hp
  exact Classical.byContradiction fun h => hp.2 ⟨CoPset.mem_full, h⟩

/-- `nroot.@a`'s and `nroot.@b`'s masks are disjoint, for distinct names. -/
theorem ndot_disj (a b : String) (h : a ≠ b) (p : Pos) (hp : p ∈ (↑(nroot.@a) : CoPset)) :
    p ∉ (↑(nroot.@b) : CoPset) := by
  intro h'
  have := mask_ndot_ne' nroot a b h _ hp
  rw [LawfulSet.mem_diff] at this
  exact this.2 h'

/-- `nroot.@a`'s mask is in `kvrMask`, for a name none of the store's. -/
theorem ndot_kvrMask (a : String) (h1 : a ≠ "kvreconf_raft") (h2 : a ≠ "kvreconf_rkv")
    (h3 : a ≠ "kvreconf_snaps") (h4 : a ≠ "kvreconf_conf") :
    (↑(nroot.@a) : CoPset) ⊆ kvrMask := by
  intro p hp
  unfold kvrMask kvrRaftN rkvN kvrSnapN kvrConfN
  simp only [LawfulSet.mem_diff]
  exact ⟨⟨⟨⟨CoPset.mem_full, ndot_disj _ _ h1 p hp⟩, ndot_disj _ _ h2 p hp⟩,
    ndot_disj _ _ h3 p hp⟩, ndot_disj _ _ h4 p hp⟩

theorem checkN_sub : (↑checkN : CoPset) ⊆ kvrMask :=
  ndot_kvrMask "kvreconf_check" (by decide) (by decide) (by decide) (by decide)

theorem lintestN_checkMask : (↑lintest.lintestN : CoPset) ⊆ ⊤ \ checkMask := by
  intro p hp
  unfold checkMask
  simp only [LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, fun h => h.2 ⟨?_, ndot_disj "lintest" "kvreconf_check" (by decide) p hp⟩⟩
  exact ndot_kvrMask "lintest" (by decide) (by decide) (by decide) (by decide) p hp

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [StorageModel GF]

instance rkvVal_timeless (γr : RNames) (x : KVMap) : Timeless (rkvVal (GF := GF) γr x) := by
  unfold rkvVal; infer_instance

/-- The store's atomic update, for the input `xin` (whose operation takes the state `x` to
`g x`, answering `out x`), from `Run`'s one-shot update: opened, it lends the store's client half
from the invariant `checkN` (so it can be closed back); committed, it runs `Run`'s update, moving
the driver's copy along. -/
theorem kvrAu_of_run (γr γd : RNames) (xin : KVInput) (g : KVMap → KVMap)
    (out : KVMap → GoString) (Ψ : GoInterface → IProp GF)
    (Hg : ∀ s, inStep xin s = g s) (Hout : ∀ s, inOut xin s = out s) :
    ⊢ inv checkN iprop(∃ x, rkvVal (GF := GF) γr x ∗ rkvVal γd x) -∗
      (|={⊤ \ checkMask, ∅}=> ∃ s, rkvVal γd s ∗
        ∀ s' o, rkvVal γd s' ∗ ⌜kvS (GF := GF).M.step s (boxIn xin, o) = some s'⌝ ={∅, ⊤ \ checkMask}=∗
          Ψ o) -∗
      AU <{ ∃∃ (x : KVMap), rkvVal γr x }> @ kvrMask, ∅
        <{ rkvVal γr (g x), COMM Ψ (boxS (out x)) }> := by
  iintro #Hinv HAU
  iauintro
  unfold atomic_acc
  iinv Hinv with ⟨%x, >Hr, >Hd⟩ Hclose
  · exact checkN_sub
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ kvrMask \ ↑checkN from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists x
  iframe Hr
  isplit
  · -- abort
    iintro Hr
    imod Hclose2 with -
    imod Hclose $$ [Hr Hd] with -
    · inext
      iexists x
      iframe
    imodintro
    iframe
  · -- commit
    iintro Hr
    imod Hclose2 with -
    imod fupd_mask_subseteq checkMask_sub with Hclose3
    imod HAU with ⟨%s, Hds, Hcommit⟩
    unfold rkvVal
    icases Hd with ⟨%Hx, Hd, %Hdx⟩
    icases Hds with ⟨%Hs, Hds, %Hss⟩
    icombine Hd Hds gives % ⟨_, Heq⟩
    subst Heq
    have Hsx : s = x := Hss.symm.trans Hdx
    subst Hsx
    icases Hr with ⟨%Hg', Hr, %Hgx⟩
    imod ghostVar_update_halves Hg' γd.val _ _ $$ Hd Hds with ⟨Hd, Hds⟩
    imod Hcommit $$ %(g s) %(boxS (out s)) [Hds] with HΨ
    · isplitl
      · iexists Hg'
        iframe
        ipureintro; exact Hgx
      · ipureintro
        simp only [kvS]
        rw [kvM_step_box, Hout, Hg, ite_eq_left rfl]
    imod Hclose3 with -
    imod Hclose $$ [Hr Hd] with -
    · inext
      iexists g s
      isplitl [Hr]
      · iexists Hg'; iframe; ipureintro; exact Hgx
      · iexists Hg'; iframe; ipureintro; exact Hgx
    imodintro
    iexact HΨ

end proof

end kvreconf
end EtcdGrove
end Perennial
