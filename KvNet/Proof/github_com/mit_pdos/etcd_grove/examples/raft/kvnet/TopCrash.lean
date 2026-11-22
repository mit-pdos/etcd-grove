/-
# kvnet's top level: a replica's file across a crash before its generation switched (2026-11-22)

A generation of a replica's machine starts in the Linux file extension's legacy mode (the bridge
`robust_of_netFsBoot`'s `fsStartRes`, or the crash's `crashRest`), and switches to the shared mode at
its program's first step (`Fs.wp_osShareE_upd`), where `durable`'s boot allocates the file's
invariant. A crash may come before that step: `durFound_crash_legacy` is that crash, for `durable`'s
file: from half of the generation's history (kept in the generation's invariant, `TopGen.lean`), what
it found at the file's two names and the crash's rest, the next generation's history (the same:
nothing was logged) and what it finds at the file's names (the same contents). `durable`'s own crash
lemmas (`durCrash_name`, `durCrash_tmp`) do the work; the tree's well-formedness (unique naming) is
the caller's, kept from the first start (`FsInit`) and from every switched generation's crash
(`crashRest_treeWf`).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Crash

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Fs DurFs

section crash
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

/-- A crash of a history with nothing logged leaves it as it was. -/
theorem treeCrashed_nil {V V' : Hist} (hV : V.2 = []) (h : TreeCrashed V V') : V' = V := by
  obtain ⟨n, -, rfl⟩ := h
  obtain ⟨m, l⟩ := V
  simp only at hV
  subst hV
  simp [replay]

/-- What the generation found at the temporary's name is not a directory. -/
theorem durFoundTmp_noDir (L : GooseLocalGS GF) (f : DFile) (m : Tree) :
    ⊢ durFoundTmp (L := L) f m -∗ ⌜∀ J, m.entry f.J f.tb ≠ some (.dir J)⌝ := by
  iintro Ht
  unfold durFoundTmp
  cases he : m.entry f.J f.tb with
  | none => ipureintro; intro J h; cases h
  | some n =>
    cases n with
    | file i => ipureintro; intro J h; cases h
    | dir J0 =>
      simp only
      icases Ht with %h
      exact h.elim

/-- **A replica's file across a crash before the switch** (see the file header). -/
theorem durFound_crash_legacy (L L' : GooseLocalGS GF) (f : DFile) (R : Roots) (V V' : Hist)
    (v : Option GoString) (hV : V.2 = []) (hwf : TreeWf R V.now) :
    ⊢ osTree (L := L) (DFrac.own (1 : Qp).half) R V -∗ durFound (L := L) f V.now v -∗
      durFoundTmp (L := L) f V.now -∗
      crashRest (fun _ _ => True) (gooseOsGS (L := L)) (gooseOsGS (L := L')) [] false V' -∗
      ⌜V' = V⌝ ∗ osTree (L := L') (DFrac.own 1) R V' ∗ durFound (L := L') f V'.now v ∗
        durFoundTmp (L := L') f V'.now := by
  unfold osTree
  iintro Hh Hf Ht Hcr
  icases crashRest_tree (hL := gooseOsGS (L := L)) (fun _ _ => True) (gooseOsGS (L := L')) []
    V' (DFrac.own (1 : Qp).half) R V $$ Hcr Hh with ⟨%hc, Hh', Hcr, -⟩
  have hVV := treeCrashed_nil hV hc
  subst V'
  icases durFoundTmp_noDir L f V.now $$ Ht with %htd
  icases durFound_cands L f V v $$ Hf with ⟨%cs, %hcs, Hc1, -⟩
  have hout : OutOk ⟨v, none⟩ cs (V.now.entry f.J f.b) := by
    rcases hcs with ⟨he, hv, -⟩ | ⟨c, he, hv, hcs, -⟩
    · rw [he]; exact Or.inl hv
    · rw [he, hcs]; exact ⟨c, List.mem_singleton_self _, rfl, Or.inl hv⟩
  have hok : ∀ c ∈ cs, c.Ok := by
    rcases hcs with ⟨-, -, rfl⟩ | ⟨c, -, -, rfl, hc⟩
    · intro c hc; cases hc
    · intro c' hc'; rw [List.mem_singleton.1 hc']; exact hc
  icases durCrash_name (fun _ _ => True) L L' f [] true V ⟨v, none⟩ cs hout hok
    (fun i hi => by cases hi) $$ Hc1 Hcr with ⟨%v', %D1, ⟨%hv', %hD1⟩, Hf', Hcr⟩
  have hvv : v' = v := by
    rcases hv' with h | h
    · exact h
    · cases h
  subst hvv
  have hu := hwf.2.2.2.2
  icases durCrash_tmp (fun _ _ => True) L L' f (D1 ++ []) true V htd
    (fun i hi he => by
      rw [List.append_nil] at hi
      exact f.tb_ne (hu _ _ _ _ _ he (hD1 i hi)).2) $$ Hcr with ⟨%D2, -, Ht', -⟩
  iframe Hh' Hf' Ht'
  ipureintro; rfl

end crash

end raft_kvnet
end EtcdGrove
end Perennial
