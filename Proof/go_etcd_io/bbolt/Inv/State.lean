/-
The client's committed data (U0a of `notes/bbolt-proof-plan.md`; design §3.3): `boltStateDef`,
what `boltState` is sealed to, and its laws restated over it.

The client holds half of `st` (at its fraction `q`) and `bq` at `q` (for validity); the library
holds the other half (¼ `metaR`, ¼ `rwR`/the writer), always the data of the committed state and
its version (the committed txid, `boltStateVDef`).
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

/-- **The committed data is `D` at version `ν`**, at fraction `q` (`boltStateV γ q D ν`, with
`B = bnsOf γ.gs`): the version is the committed state's txid (`metaR`'s and the writer's quarters
hold `(treeData C, C.txid)`), so it moves by exactly one at each commit point. -/
def boltStateVDef (B : BNs) (q : Qp) (D : Data) (ν : Nat) : IProp GF :=
  iprop(ghostVar B.st q.half (D, ν) ∗ ghostVar B.bq q ())

/-- **The committed data is `D`**, at fraction `q` (`boltState γ q D`, with `B = bnsOf γ.gs`), at
some version. -/
def boltStateDef (B : BNs) (q : Qp) (D : Data) : IProp GF :=
  iprop(∃ ν : Nat, boltStateVDef B q D ν)

instance boltStateVDef_timeless (B : BNs) (q : Qp) (D : Data) (ν : Nat) :
    Timeless (boltStateVDef (GF := GF) B q D ν) := by
  unfold boltStateVDef; infer_instance

instance boltStateDef_timeless (B : BNs) (q : Qp) (D : Data) :
    Timeless (boltStateDef (GF := GF) B q D) := by
  unfold boltStateDef; infer_instance

theorem boltStateVDef_fractional (B : BNs) (D : Data) (ν : Nat) :
    Fractional (fun q => boltStateVDef (GF := GF) B q D ν) := by
  unfold boltStateVDef
  have h1 := ghostVar_half_fractional (GF := GF) B.st (D, ν)
  have h2 := ghostVar_fractional (GF := GF) B.bq ()
  exact ⟨fun p q => (sep_congr (h1.fractional p q) (h2.fractional p q)).trans sep_sep_sep_comm⟩

theorem boltStateVDef_agree (B : BNs) (q1 q2 : Qp) (D1 D2 : Data) (ν1 ν2 : Nat) :
    boltStateVDef (GF := GF) B q1 D1 ν1 ∗ boltStateVDef B q2 D2 ν2 ⊢ ⌜D1 = D2 ∧ ν1 = ν2⌝ := by
  unfold boltStateVDef
  iintro ⟨⟨H1, -⟩, H2, -⟩
  icombine H1 H2 gives %h
  ipureintro; exact Prod.mk.inj h.2

theorem boltStateDef_fractional (B : BNs) (D : Data) :
    Fractional (fun q => boltStateDef (GF := GF) B q D) := by
  refine ⟨fun p q => ⟨?_, ?_⟩⟩
  · unfold boltStateDef
    iintro ⟨%ν, H⟩
    icases ((boltStateVDef_fractional (GF := GF) B D ν).fractional p q).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexists ν; iexact H1
    · iexists ν; iexact H2
  · unfold boltStateDef
    iintro ⟨⟨%ν1, H1⟩, ⟨%ν2, H2⟩⟩
    ihave %h := boltStateVDef_agree B p q D D ν1 ν2 $$ [H1 H2]
    · iframe
    obtain ⟨-, rfl⟩ := h
    iexists ν1
    iapply ((boltStateVDef_fractional (GF := GF) B D ν1).fractional p q).2
    iframe

theorem boltStateDef_agree (B : BNs) (q1 q2 : Qp) (D1 D2 : Data) :
    boltStateDef (GF := GF) B q1 D1 ∗ boltStateDef B q2 D2 ⊢ ⌜D1 = D2⌝ := by
  unfold boltStateDef
  iintro ⟨⟨%ν1, H1⟩, ⟨%ν2, H2⟩⟩
  ihave %h := boltStateVDef_agree B q1 q2 D1 D2 ν1 ν2 $$ [H1 H2]
  · iframe
  ipureintro; exact h.1

theorem boltStateVDef_valid (B : BNs) (q : Qp) (D : Data) (ν : Nat) :
    boltStateVDef (GF := GF) B q D ν ⊢ ⌜q ≤ 1⌝ := by
  unfold boltStateVDef
  iintro ⟨-, H⟩
  ihave ⟨H1, H2⟩ := (ghostVar_split_half B.bq q ()).1 $$ H
  icombine H1 H2 gives %h
  ipureintro; rw [Qp.half_add_half] at h; exact h.1

theorem boltStateDef_valid (B : BNs) (q : Qp) (D : Data) :
    boltStateDef (GF := GF) B q D ⊢ ⌜q ≤ 1⌝ := by
  unfold boltStateDef
  iintro ⟨%ν, H⟩
  iapply boltStateVDef_valid $$ H

/-- The library's quarter agrees with the client's data and version (any fraction). -/
theorem boltStateVDef_agree_lib (B : BNs) (q : Qp) (D D' : Data) (ν ν' : Nat) :
    boltStateVDef (GF := GF) B q D ν ∗ ghostVar B.st (1 : Qp).half.half (D', ν') ⊢
      ⌜D = D' ∧ ν = ν'⌝ := by
  unfold boltStateVDef
  iintro ⟨⟨H1, -⟩, H2⟩
  icombine H1 H2 gives %h
  ipureintro; exact Prod.mk.inj h.2

/-- The library's quarter agrees with the client's data (any fraction). Used by U10 (the commit
point opens the AU) and U5 (`Begin`'s AUs, `boltTx_base`). -/
theorem boltStateDef_agree_lib (B : BNs) (q : Qp) (D D' : Data) (ν' : Nat) :
    boltStateDef (GF := GF) B q D ∗ ghostVar B.st (1 : Qp).half.half (D', ν') ⊢ ⌜D = D'⌝ := by
  unfold boltStateDef
  iintro ⟨⟨%ν, H1⟩, H2⟩
  ihave %h := boltStateVDef_agree_lib B q D D' ν ν' $$ [H1 H2]
  · iframe
  ipureintro; exact h.1

/-- **The three-way update at the commit point** (design §3.11, `writeMeta`): the client's whole
(`boltStateV 1`), `metaR`'s quarter and the writer's quarter of `st` move together from `(D, ν)` to
`(D', ν')`. -/
theorem st_update (B : BNs) (D D' : Data) (ν ν1 ν2 ν' : Nat) (D1 D2 : Data) :
    boltStateVDef (GF := GF) B 1 D ν ∗ ghostVar B.st (1 : Qp).half.half (D1, ν1) ∗
      ghostVar B.st (1 : Qp).half.half (D2, ν2) ⊢
    |==> (boltStateVDef B 1 D' ν' ∗ ghostVar B.st (1 : Qp).half.half (D', ν') ∗
      ghostVar B.st (1 : Qp).half.half (D', ν')) := by
  unfold boltStateVDef
  iintro ⟨⟨H, Hb⟩, H1, H2⟩
  icombine H1 H2 gives %h
  obtain ⟨-, h⟩ := h
  cases h
  icombine H1 H2 as H12
  ihave Hu := ghostVar_update_halves (D', ν') B.st _ _ $$ H H12
  imod Hu
  icases Hu with ⟨H, H12⟩
  imodintro
  iframe H Hb
  iapply (ghostVar_split_half B.st _ (D', ν')).1 $$ H12

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

/-- `boltState_commit_au` over the definition: the versioned commit update, at the version of the
client's state. -/
theorem boltState_commit_au' (B : BNs) (N : Namespace) (D S : Data) :
    boltStateDef (GF := GF) B 1 D ⊢
      AU <{ ∃∃ (D' : Data) (ν' : Nat), boltStateVDef B 1 D' ν' }> @ ⊤ \ ↑N, ∅
        <{ ⌜D' = D⌝ ∗ boltStateVDef B 1 S (ν' + 1), COMM boltStateDef B 1 S }> := by
  unfold boltStateDef
  iintro ⟨%ν, H⟩
  iauintro
  unfold atomic_acc
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hcl
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists D, ν
  iframe H
  isplit
  · iintro H; imod Hcl with -; imodintro; iexact H
  · iintro ⟨-, H⟩; imod Hcl with -; imodintro; iexists (ν + 1); iexact H

/-- **A commit update over the data alone is one over the versioned state** (the client-side
conversion: a caller holding `boltState`'s update gives `Tx.Commit` the versioned one). -/
theorem commitAU_versioned (B : BNs) (N : Namespace) (Db Dn : Data) (Q : IProp GF) :
    AU <{ ∃∃ (D' : Data), boltStateDef B 1 D' }> @ ⊤ \ ↑N, ∅
        <{ ⌜D' = Db⌝ ∗ boltStateDef B 1 Dn, COMM Q }> ⊢
      AU <{ ∃∃ (D' : Data) (ν : Nat), boltStateVDef B 1 D' ν }> @ ⊤ \ ↑N, ∅
        <{ ⌜D' = Db⌝ ∗ boltStateVDef B 1 Dn (ν + 1), COMM Q }> := by
  iintro Hau
  iauintro
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%D', Hx, Hcl⟩
  unfold boltStateDef
  icases Hx with ⟨%ν, Hx⟩
  imodintro
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists D', ν
  iframe Hx
  isplit
  · iintro Hx
    icases Hcl with ⟨Hab, -⟩
    iapply Hab
    iexists ν; iexact Hx
  · iintro ⟨%hD, Hx⟩
    icases Hcl with ⟨-, Hco⟩
    iapply Hco
    isplitr
    · ipureintro; exact hD
    iexists (ν + 1); iexact Hx

end state

end bbolt
end EtcdGrove
end Perennial
