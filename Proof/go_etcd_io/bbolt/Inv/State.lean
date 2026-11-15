/-
The client's committed data (U0a of `notes/bbolt-proof-plan.md`; design §3.3): `boltStateDef`,
what `boltState` is sealed to, and its laws restated over it.

The client holds half of `st` (at its fraction `q`) and `bq` at `q` (for validity); the library
holds the other half (¼ `metaR`, ¼ `rwR`/the writer), always the data of the committed state.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Names
public import GeneratedProof.go_etcd_io.bbolt
public import Perennial.Proof.ProofPrelude
public import Perennial.Ghost.GhostVar
public import Iris.BI.Lib.Atomic
public import GooseLang.Ext.Fs.Specs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode

section state
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The committed data is `D`**, at fraction `q` (`boltState γ q D`, with `B = bnsOf γ.gs`). -/
def boltStateDef (B : BNs) (q : Qp) (D : Data) : IProp GF :=
  iprop(ghostVar B.st q.half D ∗ ghostVar B.bq q ())

instance boltStateDef_timeless (B : BNs) (q : Qp) (D : Data) :
    Timeless (boltStateDef (GF := GF) B q D) := by
  unfold boltStateDef; infer_instance

theorem boltStateDef_fractional (B : BNs) (D : Data) :
    Fractional (fun q => boltStateDef (GF := GF) B q D) := by
  unfold boltStateDef
  have h1 := ghostVar_half_fractional (GF := GF) B.st D
  have h2 := ghostVar_fractional (GF := GF) B.bq ()
  exact ⟨fun p q => (sep_congr (h1.fractional p q) (h2.fractional p q)).trans sep_sep_sep_comm⟩


theorem boltStateDef_agree (B : BNs) (q1 q2 : Qp) (D1 D2 : Data) :
    boltStateDef (GF := GF) B q1 D1 ∗ boltStateDef B q2 D2 ⊢ ⌜D1 = D2⌝ := by
  unfold boltStateDef
  iintro ⟨⟨H1, -⟩, H2, -⟩
  icombine H1 H2 gives %h
  ipureintro; exact h.2


theorem boltStateDef_valid (B : BNs) (q : Qp) (D : Data) :
    boltStateDef (GF := GF) B q D ⊢ ⌜q ≤ 1⌝ := by
  unfold boltStateDef
  iintro ⟨-, H⟩
  ihave ⟨H1, H2⟩ := (ghostVar_split_half B.bq q ()).1 $$ H
  icombine H1 H2 gives %h
  ipureintro; rw [Qp.half_add_half] at h; exact h.1


/-- The library's quarter agrees with the client's data (any fraction). Used by U10 (the commit
point opens the AU) and U5 (`Begin`'s AUs, `boltTx_base`). -/
theorem boltStateDef_agree_lib (B : BNs) (q : Qp) (D D' : Data) :
    boltStateDef (GF := GF) B q D ∗ ghostVar B.st (1 : Qp).half.half D' ⊢ ⌜D = D'⌝ := by
  unfold boltStateDef
  iintro ⟨⟨H1, -⟩, H2⟩
  icombine H1 H2 gives %h
  ipureintro; exact h.2


/-- **The three-way update at the commit point** (design §3.11, `writeMeta`): the client's whole
(`boltState 1`), `metaR`'s quarter and the writer's quarter of `st` move together from `D` to
`D'`. Used by U10. -/
theorem st_update (B : BNs) (D D1 D2 D' : Data) :
    boltStateDef (GF := GF) B 1 D ∗ ghostVar B.st (1 : Qp).half.half D1 ∗
      ghostVar B.st (1 : Qp).half.half D2 ⊢
    |==> (boltStateDef B 1 D' ∗ ghostVar B.st (1 : Qp).half.half D' ∗
      ghostVar B.st (1 : Qp).half.half D') := by
  unfold boltStateDef
  iintro ⟨⟨H, Hb⟩, H1, H2⟩
  icombine H1 H2 gives %h
  obtain ⟨-, rfl⟩ := h
  icombine H1 H2 as H12
  ihave Hu := ghostVar_update_halves D' B.st _ _ $$ H H12
  imod Hu
  icases Hu with ⟨H, H12⟩
  imodintro
  iframe H Hb
  iapply (ghostVar_split_half B.st _ D').1 $$ H12


/-- `boltState_read_au` over the definition. -/
theorem boltState_read_au' (B : BNs) (N : Namespace) (D : Data) :
    boltStateDef (GF := GF) B 1 D ⊢
      AU <{ ∃∃ (q : Qp) (D' : Data), boltStateDef B q D' }> @ ⊤ \ ↑N, ∅
        <{ boltStateDef B q D', COMM boltStateDef B 1 D ∗ ⌜D' = D⌝ }> := by
  iintro H
  iauintro
  unfold atomic_acc
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hcl
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists 1, D
  iframe H
  isplit
  · iintro H; imod Hcl with -; imodintro; iexact H
  · iintro H; imod Hcl with -; imodintro; iframe H; ipureintro; rfl


/-- `boltState_commit_au` over the definition. -/
theorem boltState_commit_au' (B : BNs) (N : Namespace) (D S : Data) :
    boltStateDef (GF := GF) B 1 D ⊢
      AU <{ ∃∃ (D' : Data), boltStateDef B 1 D' }> @ ⊤ \ ↑N, ∅
        <{ ⌜D' = D⌝ ∗ boltStateDef B 1 S, COMM boltStateDef B 1 S }> := by
  iintro H
  iauintro
  unfold atomic_acc
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hcl
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists D
  iframe H
  isplit
  · iintro H; imod Hcl with -; imodintro; iexact H
  · iintro ⟨-, H⟩; imod Hcl with -; imodintro; iexact H

end state

end bbolt
end EtcdGrove
end Perennial
