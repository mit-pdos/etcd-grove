/-
**Crash mode is on for a database that syncs** (W1 of `plans/bbolt-crash-plan.md` §7; Lean-first, no
Rocq counterpart): what C-I1's `dbCrashKeep_new` will open. A database `γ` whose options are
`NoSync = NoGrowSync = false` (`boltSyncs γ`, C-I1's `dbOpts`), in a run where the file system does
not fail (`FsNoErr`), has its file in the crash invariant `crashN γ.ns` closed by `boltState`'s
token (`isBoltCoreP`'s `bMode`, `Open/Mode.lean`) — but for one interim case: `Open` enters crash
mode only for a file whose meta tails are zero (the crash invariant's reference image needs them),
which the opened file is not yet known to have (the second disjunct, which goes once it is).
-/
module

public import Spec.go_etcd_io.bbolt.Api
public import Proof.go_etcd_io.bbolt.Inv.Bolt
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section mode
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Crash mode is on** (see the file header). -/
theorem crashMode_of (db : Loc) (γ : BoltName) :
    boltSyncs (GF := GF) γ ∗ ⌜FsNoErr⌝ ∗ isBolt db γ ⊢
      ∃ (p : BFile) (sp : Loc) (t0 : Nat), isBoltP (bnsOf γ.gs) γ.ns db p sp t0 ∗
        ⌜(∃ c, p.cs = some c ∧ c.N = crashN γ.ns ∧ c.gc = (bnsOf γ.gs).bq) ∨
          (p.cs = none ∧ ∃ X0 : List w8, ¬ metaTailsZero X0)⌝ := by
  unfold boltSyncs isBolt isBoltDef
  iintro ⟨⟨%db', Hdl', Hns, Hngs⟩, %hfs, %p, %sp, %t0, Hb⟩
  iunfold isBoltP at Hb
  icases Hb with ⟨#Hc, #Hrw, #Hpool, #Hopn⟩
  iexists p, sp, t0
  isplitr [Hdl' Hns Hngs]
  · unfold isBoltP; iframe #
  ihave Hdl : dblAt (GF := GF) (bnsOf γ.gs) db $$ []
  · unfold isBoltCoreP; icases Hc with ⟨$, -⟩
  unfold dblAt
  icombine Hdl Hdl' gives %hdb
  have hdb' : db = db' := hdb.2
  subst hdb'
  ihave #Hm := isBoltCoreP_mode _ _ _ _ _ _ $$ Hc
  unfold bMode
  cases hc : p.cs with
  | none =>
    dsimp only
    icases Hm with ⟨⟨%ns, %ngs, %X0, Hns', Hngs', %hm⟩, -⟩
    ihave %e1 := typedPointsto_agree_wand _ _ _ _ _ $$ Hns Hns'
    ihave %e2 := typedPointsto_agree_wand _ _ _ _ _ $$ Hngs Hngs'
    subst e1 e2
    ipureintro
    refine Or.inr ⟨rfl, X0, fun htz => ?_⟩
    rcases hm.1 hfs htz with h | h <;> cases h
  | some c =>
    dsimp only
    icases Hm with ⟨%hcn, -, -⟩
    ipureintro
    exact Or.inl ⟨c, rfl, hcn.2.1, hcn.1⟩

/-- `TailsZeroOnOpen` (`Spec/go_etcd_io/bbolt/ApiCrash.lean`, the one interim hypothesis of C-I1's
laws, W3) over `fileOK`: every database image `Open` accepts has zero meta tails. -/
def tailsZeroOnOpenI : Prop :=
  ∀ (X0 : List w8) (D : Data), fileOK X0 X0.length D → X0.length < 2 ^ 62 →
    X0.length % 4096 = 0 → metaTailsZero X0

/-- **Crash mode is on** (`crashMode_of` without its interim disjunct), from `TailsZeroOnOpen`: a
database that syncs, in a run where the file system does not fail, has its file in the crash
invariant `crashN γ.ns` with bbolt's closing token. The one use of the tails hypothesis. -/
theorem crashMode_on (hT : tailsZeroOnOpenI) (B : BNs) (N : Namespace) (db db' : Loc) (p : BFile)
    (sp : Loc) (t0 : Nat) :
    dblAt (GF := GF) B db' ∗ db'.[DB, go!"NoSync"] ↦□ false ∗ db'.[DB, go!"NoGrowSync"] ↦□ false ∗
      ⌜FsNoErr⌝ ∗ isBoltCoreP B N db p sp t0 ⊢
      ⌜∃ c, p.cs = some c ∧ c.N = crashN N ∧ c.gc = B.bq⌝ := by
  iintro ⟨Hdl', Hns, Hngs, %hfs, #Hc⟩
  ihave Hdl : dblAt (GF := GF) B db $$ []
  · unfold isBoltCoreP; icases Hc with ⟨$, -⟩
  unfold dblAt
  icombine Hdl Hdl' gives %hdb
  have hdb' : db = db' := hdb.2
  subst hdb'
  ihave #Hm := isBoltCoreP_mode _ _ _ _ _ _ $$ Hc
  unfold bMode
  cases hc : p.cs with
  | none =>
    dsimp only
    icases Hm with ⟨⟨%ns, %ngs, %X0, Hns', Hngs', %hm⟩, -⟩
    ihave %e1 := typedPointsto_agree_wand _ _ _ _ _ $$ Hns Hns'
    ihave %e2 := typedPointsto_agree_wand _ _ _ _ _ $$ Hngs Hngs'
    subst e1 e2
    obtain ⟨D, hD, hl1, hl2⟩ := hm.2
    rcases hm.1 hfs (hT X0 D hD hl1 hl2) with h | h <;> cases h
  | some c =>
    dsimp only
    icases Hm with ⟨%hcn, -, -⟩
    ipureintro
    exact ⟨c, rfl, hcn.2.1, hcn.1⟩

end mode

end bbolt
end EtcdGrove
end Perennial
