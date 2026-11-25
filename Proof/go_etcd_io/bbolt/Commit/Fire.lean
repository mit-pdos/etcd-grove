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

/-- **The commit update fired** (the meta page written whole): with the data's two quarters at
`(D, ν)` (the committed data and its version, the committed txid), the client's update (whose data
is `D`: the writer holds `rwlock`) commits, and the data is `Dn` at version `ν + 1`. -/
theorem au_commit_fire (B : BNs) (N : Namespace) (D Dn : Data) (ν : Nat) (Q : IProp GF) :
    ghostVar B.st (1 : Qp).half.half (D, ν) ∗ ghostVar B.st (1 : Qp).half.half (D, ν) ∗
      AU <{ ∃∃ (D' : Data) (ν' : Nat), boltStateVDef B 1 D' ν' }> @ ⊤ \ ↑N, ∅
        <{ ⌜D' = D⌝ ∗ boltStateVDef B 1 Dn (ν' + 1), COMM Q }> ⊢
    |={⊤}=> ghostVar B.st (1 : Qp).half.half (Dn, ν + 1) ∗
      ghostVar B.st (1 : Qp).half.half (Dn, ν + 1) ∗ Q := by
  iintro ⟨H1, H2, Hau⟩
  ihave Hau := atomic_update_mask_weaken (Eo2 := ⊤) (fun _ _ => CoPset.mem_full) $$ Hau
  ihave Hacc := aupd_aacc $$ Hau
  unfold atomic_acc
  imod Hacc with Hacc
  isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
  icases Hacc with ⟨%D', %ν', Hx, Hucl⟩
  ihave %Hd := boltStateVDef_agree_lib B 1 D' D ν' ν $$ [Hx H1]
  · iframe
  obtain ⟨rfl, rfl⟩ := Hd
  unfold boltStateVDef
  icases Hx with ⟨Hs, Hbq⟩
  ihave H12 := (ghostVar_split_half B.st (1 : Qp).half (D', ν')).2 $$ [H1 H2]
  · iframe
  ihave Hall := (ghostVar_split_half B.st 1 (D', ν')).2 $$ [Hs H12]
  · iframe
  imod ghostVar_update (Dn, ν' + 1) B.st (D', ν') $$ Hall with Hall
  icases (ghostVar_split_half B.st 1 (Dn, ν' + 1)).1 $$ Hall with ⟨Hs, H12⟩
  icases (ghostVar_split_half B.st (1 : Qp).half (Dn, ν' + 1)).1 $$ H12 with ⟨H1, H2⟩
  icases Hucl with ⟨-, Hcommit⟩
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
  imod Hcommit $$ [Hs Hbq] with HQ
  · iframe
  imodintro
  iframe

end fire

end bbolt
end EtcdGrove
end Perennial
