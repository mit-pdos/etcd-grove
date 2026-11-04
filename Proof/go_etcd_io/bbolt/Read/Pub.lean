/-
The public read triples' (U6g, `notes/bbolt-proof-plan.md`) accessors: what a public read takes out
of a reader's `rdTxK` (its statistics token, view and registration), and the full database's
persistence.
-/
module

public import Proof.go_etcd_io.bbolt.Read.Open

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section pub
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isBoltP_persistent_pub (B : BNs) (N : Namespace) (db : Loc) (p : GoString) (sp : Loc)
    (t0 : Nat) : Persistent (isBoltP (GF := GF) B N db p sp t0) := by
  unfold isBoltP; infer_instance

/-- **The reader's statistics token and view**, with its core and registration, out of `rdTxK`
and back (`Bucket.Cursor`'s public triple: the token for `Bucket.Cursor_i`, the view and the
registration for the cursor). -/
theorem rdTxK_cur_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) :
    rdTxK (GF := GF) K tx src q T v ⊢ ∃ r : TxReg, K.core ∗ reg tx K.B r ∗ viewOf r v ∗
      ⌜r.rw = false⌝ ∗ statsTok r true q ∗ (statsTok r true q -∗ rdTxK K tx src q T v) := by
  unfold rdTxK rtxFrac
  iintro ⟨%r, %c, %mv, %k, %Hc, #Hreg, #Hpk, #Hcore, Hv, Hex,
    ⟨%t, Hw, Hm, Hmeta, Hroot, Hfill, Hpages, Hch, Hwf, Hdb, Hmv, Hcells, Hmap, #Hvo, %Hf⟩, Hpool⟩
  iexists r
  iframe Hcore Hreg Hvo
  isplitr
  · ipureintro; exact Hc.2.2.1
  unfold statsTok
  simp only [ite_true]
  iframe Hex
  iintro Hex
  iexists r, c, mv, k
  iframe; iframe #
  isplitr
  · ipureintro; exact Hc
  ipureintro; exact Hf

/-- **A reader's views agree** (U6g): two `viewOf`s of a reader's registration are one view.
What a public reader triple needs to use a handle's view (`boltBktDef`'s, `txBytesDef`'s) with its
`rdTxK`'s. **Not derivable today** (U6g's finding): `viewOf r v` is keyed by `v.base` and a
reader's registry authority is dropped at `beginTx` (`Txn/RdReg.rd_names_alloc`), so two
fragments at different bases cannot be told apart. Proposed fix (shared, `Inv/Tx`): key a reader's
view at a fixed key (`viewOf r v := (if r.rw then v.base else null) ↪[r.n.vw]□ v`), then the two
fragments agree (`ghost_map_elem_agree`). -/
def ViewOfRdAgree : Prop :=
  ∀ (r : TxReg) (v v' : View), r.rw = false → viewOf (GF := GF) r v ∗ viewOf r v' ⊢ ⌜v = v'⌝

/-- **OPEN** (`ViewOfRdAgree`'s docstring: needs the shared `viewOf` fix). -/
theorem viewOfRdAgree_holds : ViewOfRdAgree (GF := GF) := by
  sorry

instance bytesPointsto_discard_persistent_pub (l : Loc) (bs : List w8) :
    Persistent (bytesPointsto (GF := GF) l DFrac.discard bs) :=
  (bytesPointsto_dfractional (GF := GF) l bs).dfractional_persistent

instance ite_persistent_pub {c : Prop} [Decidable c] (P Q : IProp GF) [Persistent P]
    [Persistent Q] : Persistent (if c then P else Q) := by
  split <;> infer_instance

instance rBkt_discard_persistent_pub (v : View) (tx b : Loc) (bv : List w8) :
    Persistent (rBkt (GF := GF) v tx b DFrac.discard bv) := by
  unfold rBkt locOwn; infer_instance

end pub

end bbolt
end EtcdGrove
end Perennial
