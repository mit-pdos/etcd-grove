/-
`node.spill` after its children's loop (U9l, `notes/bbolt-proof-plan.md`): **a live node's inodes'
bytes for `node.write`** (`wOwns_write_acc`): from its entries' sources (`wOwn`, persistent) and
the view's cells, every inode's key and value bytes at a fraction of its own (`qk`, `qv`: a share
of the cells for a view-backed slice, persistent bytes otherwise), as `node.write`'s premise, and
back.
-/
module

public import Proof.go_etcd_io.bbolt.Read.Src
public import Proof.go_etcd_io.bbolt.Spill.PageBuf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `node.write`'s premise on the inodes `ins` laid out as `ms`, at the fractions `qk`, `qv`. -/
def insBytes (ins : List Inode) (ms : List InodeM) (qk qv : Nat → DFrac) : IProp GF :=
  iprop([∗list] k ↦ it;m ∈ ins;ms, ⌜it.flags' = m.flags ∧ it.pgid' = m.pgid⌝ ∗
    it.key' ↦*{qk k} m.key ∗ it.value' ↦*{qv k} m.value)

omit package_sem hos in
theorem wOwn_true' (v : View) (it : Inode) (w : WEntry) :
    wOwn (GF := GF) v true it w ⊣⊢ ⌜it.flags' = w.flags ∧ it.pgid' = w.pgid⌝ ∗
      srcOwn v it.key' w.ks w.key ∗ srcOwn v it.value' w.vs w.value := by
  unfold wOwn; simp only [↓reduceIte]; exact .rfl

omit package_sem hos in
/-- A live node's entry's facts are persistent. -/
instance wOwn_true_persistent (v : View) (it : Inode) (w : WEntry) :
    Persistent (wOwn (GF := GF) v true it w) := by
  unfold wOwn; simp only [↓reduceIte]; infer_instance

/-- **A live node's inodes' bytes for `node.write`** (see the module doc). -/
theorem wOwns_write_acc (v : View) (hb : 0 < v.base.addr) :
    ∀ (ins : List Inode) (ws : List WEntry) (q : Qp), wsLive ws →
    ([∗list] it;w ∈ ins;ws, wOwn (GF := GF) v true it w) ∗ viewCells q v ⊢
      ∃ (qk qv : Nat → DFrac), insBytes ins (wsMs ws) qk qv ∗
        (insBytes ins (wsMs ws) qk qv -∗ viewCells q v)
  | [], [], q, _ => by
    iintro ⟨-, Hv⟩
    iexists (fun _ => DFrac.discard), (fun _ => DFrac.discard)
    unfold insBytes
    simp only [wsMs, List.map_nil]
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; iempintro
    · iintro -; iexact Hv
  | [], _ :: _, q, _ => by
    iintro ⟨H, -⟩
    icases BigSepL2.bigSepL2_nil_inv_left $$ H with %H
    cases H
  | _ :: _, [], q, _ => by
    iintro ⟨H, -⟩
    icases BigSepL2.bigSepL2_nil_inv_right $$ H with %H
    cases H
  | it :: ins, w :: ws, q, hl => by
    have hw := hl w List.mem_cons_self
    have hl' : wsLive ws := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have IH := wOwns_write_acc v hb ins ws q.half hl'
    iintro ⟨H, Hv⟩
    icases BigSepL2.bigSepL2_cons.1 $$ H with ⟨Hw, H⟩
    have hs1 := viewCells_split_r (GF := GF) q.half q.half v
    rw [Qp.half_add_half] at hs1
    have hs2 := viewCells_split_r (GF := GF) q.half.half q.half.half v
    rw [Qp.half_add_half] at hs2
    icases hs1.1 $$ Hv with ⟨Hv1, Hv2⟩
    icases hs2.1 $$ Hv1 with ⟨Hk, Hvv⟩
    icases (wOwn_true' v it w).1 $$ Hw with ⟨%Hfp, #Hks, #Hvs⟩
    icases viewCells_src_acc q.half.half v hb it.key' w.ks w.key hw.1 $$ [Hks Hk]
      with ⟨%dk, Hkb, Hkback⟩
    · iframe; iframe #
    icases viewCells_src_acc q.half.half v hb it.value' w.vs w.value hw.2 $$ [Hvs Hvv]
      with ⟨%dv, Hvb, Hvback⟩
    · iframe; iframe #
    icases IH $$ [H Hv2] with ⟨%qk, %qv, Hrest, Hrback⟩
    · iframe
    iexists (fun k => if k = 0 then dk else qk (k - 1)), (fun k => if k = 0 then dv else qv (k - 1))
    unfold insBytes
    simp only [wsMs, List.map_cons]
    isplitl [Hkb Hvb Hrest]
    · iapply BigSepL2.bigSepL2_cons.2
      simp only [↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      iframe
      ipureintro; exact Hfp
    · iintro H
      icases BigSepL2.bigSepL2_cons.1 $$ H with ⟨⟨-, Hkb, Hvb⟩, Hrest⟩
      simp only [↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      ihave Hk := Hkback $$ Hkb
      ihave Hvv := Hvback $$ Hvb
      ihave Hv2 := Hrback $$ [Hrest]
      · iexact Hrest
      iapply hs1.2
      iframe Hv2
      iapply hs2.2
      iframe

end heap

end Spill

end bbolt
end EtcdGrove
end Perennial
