/-
`tx.allocate` over `db.allocate` (`DB__allocate.lean`): the database as the writer's abstract
resource (`dbWR`: `ownDB` with this transaction its writer, over the writer's view), the
transaction's buckets after a dereference (`noView_of_derefRel`, `bs_reattach`), and the fresh
page's header (`fresh_page_split`).
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxAcc
public import Proof.go_etcd_io.bbolt.AllocPage
public import Spec.go_etcd_io.bbolt.DB__allocate

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- A dereferenced transaction keeps no byte of the view. -/
theorem noView_of_derefRel (T T' : WTx) (h : derefRel T T') : noView T' := by
  obtain ⟨-, -, -, -, hdom, hb⟩ := h
  intro bl B' hB'
  obtain ⟨B, hB⟩ := Option.isSome_iff_exists.1 ((hdom bl).2 (by rw [hB']; rfl))
  obtain ⟨-, -, -, -, -, hsrc, hns, -⟩ := hb bl B B' hB hB'
  refine ⟨?_, fun l r' hr' => ?_⟩
  · rw [hsrc]; cases B.isrc <;> simp [staleOf]
  · obtain ⟨r, -, hd⟩ := hns l r' hr'
    obtain ⟨-, hws, -, -, -, hks, -⟩ := hd
    refine ⟨fun w hw => ?_, by rw [hks]; nofun⟩
    rw [hws] at hw
    obtain ⟨w0, -, rfl⟩ := List.mem_map.1 hw
    exact ⟨by simp [ownFresh], by simp [ownFresh]⟩

/-- What `db.allocate` keeps of the database. -/
theorem allocOK_keeps (σ σ' : DBState) (w : Reader) (mv mv' : Meta) (txid id : w64) (n : Nat)
    (h : allocOK σ σ' w mv mv' txid id n) :
    σ'.rwtx = σ.rwtx ∧ σ'.wr = σ.wr ∧ σ'.ps = σ.ps := by
  obtain ⟨-, -, -, -, -, -, h⟩ := h
  rcases h with ⟨-, rfl, -⟩ | ⟨-, -, rfl | ⟨d', sz', -, rfl⟩⟩ <;> exact ⟨rfl, rfl, rfl⟩

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- The database of the writer `txl` with the view `W`, its state `σ` (the resource
`Tx.allocate.wspec` threads). -/
def dbWR (I : FLImpl (GF := GF)) (γ : DBNames) (W : WView) (txl : Loc) (σ : DBState) : IProp GF :=
  iprop(ownDB I W.dbl γ σ ∗ ⌜I.AllocateSpec ∧ σ.rwtx = txl ∧ σ.data = W.data ∧ σ.ps = W.ps ∧
    W.fli = I.iface ∧ ∃ w, σ.wr = some w ∧ w.pages = W.pages ∧ w.q = W.q ∧ w.hwm = W.hwm⌝)

/-- Buckets keeping no byte of the view stand over any view. -/
theorem bs_reattach (W W' : WView) (bs : GMap Loc BRec)
    (h : ∀ bl B, bs !! bl = some B → B.isrc ≠ Src.view ∧
      ∀ l r, B.ns !! l = some r → (∀ w ∈ r.ws, w.ks ≠ Src.view ∧ w.vs ≠ Src.view) ∧
        r.ksrc ≠ Src.view) :
    ([∗map] bl ↦ B ∈ bs, bktOwn (GF := GF) W bl B) ⊢ [∗map] bl ↦ B ∈ bs, bktOwn W' bl B := by
  iintro Hbs
  iapply (BigSepM.bigSepM_mono (M := GMap Loc) (Φ := fun bl B => bktOwn (GF := GF) W bl B)
    (Ψ := fun bl B => bktOwn (GF := GF) W' bl B) ?_) $$ Hbs
  intro bl B hB
  obtain ⟨hi, hn⟩ := h bl B hB
  unfold bktOwn
  iintro ⟨Hbv, Hib, Hnm, Hbm, Hpg, Hns⟩
  iframe Hbv Hib Hnm Hbm
  rw [pageOwn_other W W' B hi]
  iframe Hpg
  iapply (BigSepM.bigSepM_mono (M := GMap Loc) (Φ := fun l r => nodeOwn (GF := GF) W l r)
    (Ψ := fun l r => nodeOwn (GF := GF) W' l r) ?_) $$ Hns
  intro l r hr
  exact nodeOwn_other W W' l r (hn l r hr)

/-- The fresh page: its header (as a `Page`) and zeroes. -/
theorem fresh_page_split (l : Loc) (id : w64) (count ps : Nat) (hl : l.locCar ≠ 0)
    (hc : 0 < count) (hc32 : count ≤ 2 ^ 32) (hps : 16 ≤ count * ps) :
    bytesPointsto (GF := GF) l (DFrac.own 1) (freshPage id count ps) ⊢
      l ↦ Page.mk id (W16 0) (W16 0) (W32 ((count - 1 : Nat) : Int)) ∗
      (l ↦ Page.mk id (W16 0) (W16 0) (W32 ((count - 1 : Nat) : Int)) -∗
        bytesPointsto (GF := GF) l (DFrac.own 1) (freshPage id count ps)) := by
  have hov : (W32 ((count - 1 : Nat) : Int)).toNat = count - 1 := by
    simp; omega
  have hb : pageBytes (Page.mk id (W16 0) (W16 0) (W32 ((count - 1 : Nat) : Int))) =
      leBytes 8 (uint.Z id) ++ leBytes 4 0 ++ leBytes 4 (((count - 1 : Nat) : Int)) := by
    unfold pageBytes
    simp only
    rw [hov, leBytes_zero_4]
    simp [List.append_assoc]
  have hlen : (pageBytes (Page.mk id (W16 0) (W16 0) (W32 ((count - 1 : Nat) : Int)))).length =
      16 := by
    simp [pageBytes, leBytes_length]
  have e : freshPage id count ps =
      pageBytes (Page.mk id (W16 0) (W16 0) (W32 ((count - 1 : Nat) : Int))) ++
        List.replicate (count * ps - 16) 0 := by
    unfold freshPage; rw [hb]
  rw [e]
  iintro Hb
  icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hh, Hz⟩
  rw [hlen]
  ihave Hh := (Page_bytes (hG := hG) l _ _ hl).2 $$ Hh
  iframe Hh
  iintro Hh
  iapply (bytesPointsto_app _ _ _ _).2
  rw [hlen]
  ihave Hh := (Page_bytes (hG := hG) l _ _ hl).1 $$ Hh
  iframe

/-- The page cache's buffers, with a new one. -/
theorem bufs_insert (pm : GMap w64 Loc) (bufs : GMap w64 (List w8)) (id : w64) (p : Loc)
    (bs : List w8) :
    ([∗map] i ↦ q ∈ pm, ∃ b, ⌜bufs !! i = some b⌝ ∗ bytesPointsto (GF := GF) q (DFrac.own 1) b) ∗
      bytesPointsto (GF := GF) p (DFrac.own 1) bs ⊢
    [∗map] i ↦ q ∈ <[id := p]> pm, ∃ b, ⌜(<[id := bs]> bufs) !! i = some b⌝ ∗
      bytesPointsto (GF := GF) q (DFrac.own 1) b := by
  iintro ⟨Hm, Hp⟩
  iapply (BigSepM.bigSepM_insert_delete (M := GMap w64)).2
  isplitl [Hp]
  · iexists bs; iframe; ipureintro; exact GMap.lookup_insert _ _ _
  have Hd : ([∗map] i ↦ q ∈ pm, ∃ b, ⌜bufs !! i = some b⌝ ∗ bytesPointsto (GF := GF) q (DFrac.own 1) b) ⊢
      [∗map] i ↦ q ∈ Std.delete pm id, ∃ b, ⌜bufs !! i = some b⌝ ∗ bytesPointsto (GF := GF) q (DFrac.own 1) b := by
    cases h : pm !! id with
    | none =>
      have : Std.delete pm id = pm := by
        show GMap.delete id pm = pm
        apply GMap.ext; intro k
        by_cases e : k = id
        · subst e; rw [GMap.lookup_delete, h]
        · rw [GMap.lookup_delete_ne _ (Ne.symm e)]
      rw [this]
    | some q =>
      iintro H
      icases (BigSepM.bigSepM_delete (M := GMap w64)
        (Φ := fun i q => iprop(∃ b, ⌜bufs !! i = some b⌝ ∗ bytesPointsto (GF := GF) q (DFrac.own 1) b))
        (show Std.get? pm id = some q from h)).1 $$ H with ⟨-, H⟩
      iexact H
  ihave Hm := Hd $$ Hm
  iapply (BigSepM.bigSepM_mono (M := GMap w64) ?_) $$ Hm
  intro i q hi
  iintro ⟨%b, %hb, Hb⟩
  iexists b
  iframe
  ipureintro
  have hne : i ≠ id := by
    intro e; subst e
    change (GMap.delete i pm) !! i = some q at hi
    rw [GMap.lookup_delete] at hi; cases hi
  rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]; exact hb

end own

end bbolt
end EtcdGrove
end Perennial
