/- Reading a segment's lock name through the decoder's open file. -/
module
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenAtTail
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllExit

@[expose] public section
noncomputable section
namespace Perennial.EtcdGrove.WalFs
open Iris Iris.BI Iris.ProofMode Fs

variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go.Semantics] [os.Assumptions] [_root_.Perennial.bufio.Assumptions]

private theorem readAll_fbr_name (IoE : GoInterface → Prop) (eof : GoInterface)
    (F : DecFile GF) (f : Loc) (fd : w64) (name : GoString) (fl : OsFd) (g : SegG)
    (hS : F.S = walFileS f fd name fl g) :
    ∀ (fbrs : List Loc) (fs : List (DecFile GF)) (rs : List (List w8)) (n : Nat),
    fs[n]? = some F → ownFbrs IoE eof fbrs fs rs ⊢ os.fileNamed f name
  | [], [], _, n, hn => by simp at hn
  | [], _ :: _, _, _, _ => by simp only [ownFbrs]; iintro %h; cases h
  | _ :: _, [], _, n, hn => by simp at hn
  | _ :: _, _ :: _, [], _, _ => by simp only [ownFbrs]; iintro %h; cases h
  | b :: bs, F' :: fs, r :: rs, 0, hn => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
    subst F'
    simp only [ownFbrs]
    iintro ⟨Hf, -⟩
    iunfold ownFbr at Hf
    icases Hf with ⟨%br, %fi, %err, -, -, Hr, -⟩
    icases bufio.ownReader_open br F.fr _ _ r $$ Hr with ⟨%q, Hs, -⟩
    rw [hS]
    iunfold walFileS at Hs
    icases Hs with ⟨-, Hf, -⟩
    iapply os.ownFile_named f fd name _ $$ Hf
  | _ :: bs, _ :: fs, _ :: rs, n + 1, hn => by
    simp only [ownFbrs]
    iintro ⟨-, H⟩
    iapply readAll_fbr_name IoE eof F f fd name fl g hS bs fs rs n hn $$ H

/-- The OS name behind each locked file is persistent across all decoder steps. -/
def readAllLockNames (dir : GoString) (gs : List SegG) (fls : List Loc) : IProp GF :=
  iprop(∀ (n : Nat) (g : SegG) (f : Loc), ⌜gs[n]? = some g ∧ fls[n]? = some f⌝ -∗
    os.fileNamed f (child dir g.name))

theorem readAll_decoder_names (dec : Loc) (IoE : GoInterface → Prop) (eof : GoInterface)
    (fs : List (DecFile GF)) (off : Nat) (crc : w32) (live : Bool)
    (dir : GoString) (gs : List SegG) (fls : List Loc) (hlen : fs.length = gs.length)
    (hfiles : ∀ (n : Nat) (F : DecFile GF) (g : SegG), fs[n]? = some F → gs[n]? = some g →
       ∃ (f : Loc) (fd : w64) (lo lk : Option Bool), fls[n]? = some f ∧
         F.S = walFileS f fd (child dir g.name) (walSegFd true lo lk g.ino) g) :
    ownDecoder dec IoE eof fs off crc live ⊢ readAllLockNames dir gs fls := by
  unfold ownDecoder readAllLockNames
  iintro ⟨%sl, %fbrs, %h, %rs, -, -, -, -, -, -, -, Hf, -⟩ %n %g %f %hs
  have hn : n < fs.length := hlen ▸ (List.getElem?_eq_some_iff.1 hs.1).1
  obtain ⟨F, hF⟩ : ∃ F, fs[n]? = some F := ⟨_, List.getElem?_eq_getElem hn⟩
  obtain ⟨f', fd, lo, lk, hf, hS⟩ := hfiles n F g hF hs.1
  have he := Option.some.inj (hf.symm.trans hs.2)
  subst f'
  iapply readAll_fbr_name IoE eof F f fd _ _ g hS fbrs fs rs n hF $$ Hf

instance (dir : GoString) (gs : List SegG) (fls : List Loc) :
    Persistent (readAllLockNames (GF := GF) dir gs fls) := by unfold readAllLockNames; infer_instance

end Perennial.EtcdGrove.WalFs
