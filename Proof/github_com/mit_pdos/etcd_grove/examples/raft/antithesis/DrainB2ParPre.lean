/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E: **`node.parallel`'s storage
prerequisites** (`node.drain`'s, B1, as lemmas: `node.drain` is a proof module, which a proof does not
import): the `Ready`'s entries' indices consecutive from the first's, and the storage's slot for them
(`append_preB1` with the bounds `parWriteB2` takes).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1Store
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessDur
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Send

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- A `Ready`'s entries, the suffix of a log with consecutive indices from the first's
(`node.drain`'s `readyEnts_idx_d`). -/
theorem readyEnts_idx_b2 {l es : List EntryM} (hl : AntSim.LogIdx l)
    (hd : ∀ e0 ∈ es.head?, l.drop (uint.nat e0.Index' - 1) = es) (k : Nat)
    (hk : ∀ e0 ∈ es.head?, k = uint.nat e0.Index') :
    ∀ (i : Nat) (e : EntryM), es[i]? = some e → uint.nat e.Index' = k + i := by
  intro i e he
  cases hes : es with
  | nil => rw [hes] at he; simp at he
  | cons e0 t =>
    have hd0 := hd e0 (by rw [hes]; rfl)
    have hk0 := hk e0 (by rw [hes]; rfl)
    rw [hes] at hd0 he
    have h0 : l[uint.nat e0.Index' - 1 + 0]? = some e0 := by
      rw [← List.getElem?_drop, hd0]; rfl
    have hi : l[uint.nat e0.Index' - 1 + i]? = some e := by
      rw [← List.getElem?_drop, hd0]; exact he
    have a0 := hl _ _ h0
    have ai := hl _ _ hi
    have : uint.nat e0.Index' = (uint.Z e0.Index').toNat := rfl
    have : uint.nat e.Index' = (uint.Z e.Index').toNat := rfl
    omega

/-- `ReachIn` does not read `told` (`reportCause` sets it; `reach_told_b1`'s). -/
theorem reachIn_told_b2 {msk : AntSim.SimMask} {R : AntSim.RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} {net : List Msg} {xnet : List XMsg} {n : Fin R.N}
    {v : AntSim.NodeView} {r₁ : RState} (b : Bool)
    (h : AntSim.ReachIn msk R dec Adm net xnet n v r₁) :
    AntSim.ReachIn msk R dec Adm net xnet n { v with told := b } r₁ := by
  cases h with
  | stay hI hb => exact .stay { v with told := b } hI hb
  | input inp r₁ h0 hI h1 h2 h3 h4 h5 h6 => exact .input _ inp _ h0 hI h1 h2 h3 h4 h5 h6
  | advance r₁ h1 h2 h3 h4 h5 h6 h7 => exact .advance _ _ h1 h2 h3 h4 h5 h6 h7

/-- The request loop's end: only the other messages pending. -/
theorem reqPend_end (ms : List QMsg) :
    reqPend ms ms.length =
      (ms.filter (fun m => !isRequestTy m.st.msg.Type')).filterMap (fun m => absMsgOf m.st) := by
  simp [reqPend]

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]

/-- **The storage's slot for a `Ready`'s entries** (`append_preB1`, with `parWriteB2`'s bounds): the
entries a suffix of a log with indices from `1` (`LogIdx`), each index below `2 ^ 61`. -/
theorem parStorPre (st : Storage) (γs : MemStorNames) (es l : List EntryM) (hl : AntSim.LogIdx l)
    (hd : ∀ e0 ∈ es.head?, l.drop (uint.nat e0.Index' - 1) = es)
    (hN : ∀ e ∈ es, uint.Z e.Index' < 2 ^ 61) :
    antStorBridge (GF := GF) st γs ∗ appendRight st es ⊢
      ∃ (k : Nat) (old : List EntryM), ⌜∀ e0 ∈ es.head?, k = uint.nat e0.Index'⌝ ∗
        ⌜∀ (i : Nat) (e : EntryM), es[i]? = some e → uint.nat e.Index' = k + i⌝ ∗
        ⌜k + es.length ≤ 2 ^ 61⌝ ∗
        (if es = [] then emp else memLog γs k (DFrac.own 1) old ∗ memEnd γs (k + old.length)) := by
  iintro ⟨#Hb, Happ⟩
  by_cases hes : es = []
  · iexists 0, []
    isplitr
    · ipureintro; intro e0 he0; rw [hes] at he0; cases he0
    isplitr
    · ipureintro; intro i e he; rw [hes] at he; simp at he
    isplitr
    · ipureintro; rw [hes]; simp
    rw [ite_eq_left hes]
    iempintro
  · icases append_preB1 st γs es $$ [$Hb $Happ] with ⟨%k, %old, %Hk, Hpre⟩
    have hidx := readyEnts_idx_b2 hl hd k Hk
    iexists k, old
    iframe Hpre
    ipureintro
    refine ⟨Hk, hidx, ?_⟩
    have hlt : es.length - 1 < es.length := by
      cases es with
      | nil => exact absurd rfl hes
      | cons a b => simp
    have h1 := hidx _ _ (List.getElem?_eq_getElem hlt)
    have h2 := hN _ (List.getElem_mem hlt)
    have : uint.nat (es[es.length - 1]).Index' = (uint.Z (es[es.length - 1]).Index').toNat := rfl
    omega

end proof

end AntHarness
end EtcdGrove
end Perennial
