/-
A law of bbolt's API (`Spec/go_etcd_io/bbolt/Api.lean`), in a module of its own (S5, 2026-11-18,
`notes/bbolt-integration-plan.md`): **a database's file is one inode** (`boltIno_agree`). The
backend's client keeps the claim on the database file's name, which names the inode `Open` opened,
and `Close` gives the inode back (`DB.Close.spec`'s `fileHoldsM i D`); joining the two needs the two
`boltIno`s to agree. Proved from `boltIno`'s definition (`t0At`, an agreeing ghost-map element); a
module of its own so that bbolt's proofs, which import `Api.lean`, do not rebuild.
-/
module

public import Spec.go_etcd_io.bbolt.Api
import all Spec.go_etcd_io.bbolt.Api
import Proof.go_etcd_io.bbolt.Inv.Bolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A database's file is one inode**: two `boltIno`s of one database agree. -/
theorem boltIno_agree (γ : BoltName) (i i' : Ino) :
    boltIno (GF := GF) γ i ∗ boltIno γ i' ⊢ ⌜i = i'⌝ := by
  unfold boltIno t0At
  iintro ⟨⟨%t0, H1⟩, ⟨%t0', H2⟩⟩
  ihave %h := ghostMapElem_agree (GF := GF) () (bnsOf γ.gs).t0 DFrac.discard DFrac.discard
    (t0, i) (t0', i') $$ H1 H2
  ipureintro
  exact (Prod.mk.inj h).2

end vocab

end bbolt
end EtcdGrove
end Perennial
