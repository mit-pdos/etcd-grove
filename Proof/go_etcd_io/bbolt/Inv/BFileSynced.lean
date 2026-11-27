/-
**The synced mark of the committed version** (W3 of `plans/bbolt-crash-plan.md`; Lean-first, no Rocq
counterpart): the writer's share of the file at the committed state `C` (`bMeta`, the crash
invariant's value idle at `C`: the commit that made `C` finished both its syncs) mints `syncedB B C.txid`.
In crash mode it opens the crash invariant (`csOwnILR_upd`): the value's previous state becomes `C`
itself (`BDur` of an idle value reads no previous state) and the synced mark moves up to `C.txid`
(`bRFacts`' `y ≤ prev.txid`), whose lower bound is `syncedE`; outside crash mode it is `True`.
`beginRWTx` puts it in the writer's registration (`reg`'s `regX`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Bolt
public import Proof.go_etcd_io.bbolt.Inv.BFileOps

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
open Iris Iris.BI Iris.ProofMode

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The mode's crash invariant (`True` outside crash mode). -/
theorem bMode_bCsInv (B : BNs) (N : Namespace) (db : Loc) (p : BFile) :
    bMode (GF := GF) B.bq B.cn N db p ⊢ bCsInv p := by
  unfold bMode
  cases hc : p.cs with
  | none => iintro -; iapply bCsInv_none hc
  | some c => dsimp only; iintro ⟨-, #H, -⟩; iexact H

/-- **The synced mark of the committed version** (see the file header). -/
theorem bMeta_syncedB (B : BNs) (N : Namespace) (db : Loc) (p : BFile) (C : CommitSt)
    (L : List (Nat × Nat)) (m : OsMeta) :
    ⊢ bMode (GF := GF) B.bq B.cn N db p -∗ bMeta p C L m ={⊤}=∗ bMeta p C L m ∗ syncedB B C.txid := by
  iintro #Hmd Hm
  cases hc : p.cs with
  | none =>
    ihave #Hreg := bMode_none B N db p hc $$ Hmd
    imodintro
    iframe Hm
    unfold syncedB
    iexists none
    iframe Hreg
    unfold syncedM; itrivial
  | some c =>
    icases bMode_some B N db p c hc $$ Hmd with ⟨-, #Hreg⟩
    ihave #Hinv := bMode_bCsInv B N db p $$ Hmd
    ihave #Hci := bCsInv_some p c hc $$ Hinv
    icases bMeta_own p c hc C L m $$ Hm with ⟨%bs, %a, Hown, Ha, %Hf⟩
    obtain ⟨hph, hcur, hdur, hfs, hone⟩ := Hf
    let a' : BAbs := ⟨a.cur, a.cur, a.xcur, a.xcur, a.phase⟩
    imod csOwnILR_upd (bR c.cg) c.N p.ino c.g c.ga c.gc bCsOk ⟨m, bs, 0, 0, .idle⟩ a a' ⊤
      CoPset.subseteq_top
      (fun h hf => by
        obtain ⟨hw, hI⟩ := h hf
        refine ⟨hw, ?_⟩
        show (match a.phase with
          | .idle => IdleOk a.cur a.xcur _
          | .committing => CommitOk a.cur a.cur a.xcur a.xcur _
          | .init => InitOk _)
        rw [hph] at hI ⊢; exact hI)
      (syncedE c.cg C.txid) $$ Hci Hown [] with ⟨Hown, #Hsy⟩
    · iintro HR
      unfold bR
      icases HR with ⟨Hcv, ⟨%H, %y, Hh, Hy, %Hfacts⟩, #Hrc⟩
      obtain ⟨hHc, -, hHle, hy, hpc, hni⟩ := Hfacts
      have hyC : y ≤ C.txid := by
        rw [← hcur]
        rcases hpc with h | h
        · omega
        · rw [h] at hy; exact hy
      imod mono_nat_own_update C.txid hyC $$ Hy with ⟨Hy, #Hlb⟩
      imodintro
      iframe Hcv Hrc
      isplitl
      · iexists H, C.txid
        iframe Hh Hy
        ipureintro
        exact ⟨hHc, hHc, hHle, by show C.txid ≤ a.cur.txid; rw [hcur]; exact Nat.le_refl _, .inr rfl, hni⟩
      · unfold syncedE; iexact Hlb
    imodintro
    isplitl [Hown Ha]
    · iapply bMeta_of_own p c hc C L m bs a' ⟨hph, hcur, hdur, hfs, hone⟩ $$ [Hown Ha]
      iframe
    unfold syncedB
    iexists (some c.cg)
    iframe Hreg
    unfold syncedM; iexact Hsy

end res

end bbolt
end EtcdGrove
end Perennial
