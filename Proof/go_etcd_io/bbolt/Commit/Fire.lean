/-
`Commit`'s linearization point (U10 of `notes/bbolt-proof-plan.md`; design §3.11, Commit step 7):
with the data's two quarters (`metalock`'s and the writer's), the client's update commits: the
data moves from `D` (the transaction's base) to `Dn` (its contents).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.State

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section fire
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The commit update fired** (the meta page written whole, or, in crash mode, at the early commit
point): with the data's two quarters at `(D, ν)` (the committed data and its version, the committed
txid), the client's update (whose data is `D`: the writer holds `rwlock`) commits, and the data is
`Dn` at version `ν + 1`; the committed data's crash part moves by `U` (W3: in crash mode the crash
invariant's half of the version variable and its history, `Y` what is left of them; outside it
nothing). At any mask `E` the update's allows. -/
theorem au_commit_fire (B : BNs) (N : Namespace) (D Dn : Data) (ν : Nat) (Q Y : IProp GF)
    (E : CoPset) (hE : ⊤ \ ↑N ⊆ E) :
    ghostVar B.st (1 : Qp).half.half (D, ν) ∗ ghostVar B.st (1 : Qp).half.half (D, ν) ∗
      iprop(∀ o, cnReg B o -∗ cpart o 1 D ν ==∗ cpart o 1 Dn (ν + 1) ∗ Y) ∗
      AU <{ ∃∃ (D' : Data) (ν' : Nat), boltStateVDef B 1 D' ν' }> @ ⊤ \ ↑N, ∅
        <{ ⌜D' = D⌝ ∗ boltStateVDef B 1 Dn (ν' + 1), COMM Q }> ⊢
    |={E}=> ghostVar B.st (1 : Qp).half.half (Dn, ν + 1) ∗
      ghostVar B.st (1 : Qp).half.half (Dn, ν + 1) ∗ Q ∗ Y := by
  iintro ⟨H1, H2, HU, Hau⟩
  ihave Hau := atomic_update_mask_weaken (Eo2 := E) hE $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%D', %ν', Hx, Hucl⟩
  ihave %Hd := boltStateVDef_agree_lib B 1 D' D ν' ν $$ [Hx H1]
  · iframe
  obtain ⟨rfl, rfl⟩ := Hd
  unfold boltStateVDef
  icases Hx with ⟨Hs, Hbq, Hcp⟩
  unfold crashPart
  icases Hcp with ⟨%o, #Hr, Hc⟩
  imod HU $$ %o Hr Hc with ⟨Hc, HY⟩
  ihave H12 := (ghostVar_split_half B.st (1 : Qp).half (D', ν')).2 $$ [H1 H2]
  · iframe
  ihave Hall := (ghostVar_split_half B.st 1 (D', ν')).2 $$ [Hs H12]
  · iframe
  imod ghostVar_update (Dn, ν' + 1) B.st (D', ν') $$ Hall with Hall
  icases (ghostVar_split_half B.st 1 (Dn, ν' + 1)).1 $$ Hall with ⟨Hs, H12⟩
  icases (ghostVar_split_half B.st (1 : Qp).half (Dn, ν' + 1)).1 $$ H12 with ⟨H1, H2⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  imod Hcommit $$ [Hs Hbq Hc] with HQ
  · isplitr
    · ipureintro; trivial
    iframe Hs Hbq
    iexists o; iframe; iframe #
  imodintro
  iframe

/-- **Outside crash mode the crash part does not move** (`au_commit_fire`'s `U`, registered names
`none`). -/
theorem cpart_none_upd (B : BNs) (D Dn : Data) (ν : Nat) :
    ⊢ cnReg (GF := GF) B none -∗ iprop(∀ o, cnReg B o -∗ cpart o 1 D ν ==∗ cpart o 1 Dn (ν + 1) ∗ emp) := by
  iintro #Hn %o #Hr Hc
  ihave %ho := cnReg_agree B none o $$ [Hn Hr]
  · iframe #
  subst ho
  unfold cpart
  imodintro; iframe

end fire

end bbolt
end EtcdGrove
end Perennial
