/-
The page pool's lease from a commit update (U11i, `notes/bbolt-proof-plan.md`): a resource that
gives the client's commit update over `boltState` (`Commit_err`'s `P`) is a `poolR` (`Inv/Bolt`):
opening the update gives the whole of `boltState`, so the whole validity token `B.bq`, which
excludes another whole token. `Commit` lends it to `spill` and `commitFreelist`, whose
`allocate` lends it to the page pool's `New`.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Bolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section poolr
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A commit update excludes a whole validity token**: open it, its `boltState` holds `B.bq`
whole. -/
theorem au_excl_bq (B : BNs) (N : Namespace) (β : Data → IProp GF) (Q : IProp GF) :
    AU <{ ∃∃ (D' : Data), boltStateDef (GF := GF) B 1 D' }> @ ⊤ \ ↑N, ∅
        <{ β D', COMM Q }> ∗ ghostVar B.bq 1 () ={⊤ \ ↑N}=∗ False := by
  iintro ⟨Hau, Hbq⟩
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%D', Hx, -⟩
  unfold boltStateDef
  icases Hx with ⟨-, Hbq'⟩
  ihave %h := ghostVar_valid_2 B.bq () 1 () 1 $$ Hbq Hbq'
  exfalso
  have h1 := h.1
  rw [Qp.le_iff, Qp.val_add, Qp.val_one] at h1
  grind

/-- **A carrier of a commit update is a page-pool lease** (`poolR`). -/
theorem poolR_of_au (B : BNs) (N : Namespace) (β : Data → IProp GF) (Q P : IProp GF)
    (hP : P ⊢ AU <{ ∃∃ (D' : Data), boltStateDef (GF := GF) B 1 D' }> @ ⊤ \ ↑N, ∅
        <{ β D', COMM Q }>) :
    P ⊢ poolR B.bq N P := by
  iintro HP
  unfold poolR
  iframe HP
  imodintro
  iintro ⟨HP, Hbq⟩
  ihave Hau := hP $$ HP
  iapply au_excl_bq B N β Q $$ [Hau Hbq]
  iframe

end poolr

end bbolt
end EtcdGrove
end Perennial
