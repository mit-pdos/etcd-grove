/- Lean-first (no Rocq counterpart).

# The etcd examples' extensions over the network: `[idIssueExt, fsExt, netExt]` (2026-11-23)

`etcdFsExts` (`FsExts.lean`: the request ids' issue record and the Linux file extension at `etcdFsSem`) with the
net extension: the extensions of an etcd program on a machine of a distributed deployment (`putget_safe`,
`notes/putget-dist-plan.md`; the plan's option (i) bundle, `notes/etcd-dist-plan.md` §9), and of a
single-process etcd program that listens (`single-process-restore`). Each extension's semantics and ghost
state is its own (the file extension's at `etcdFsSem`); the `HasExt` instances by computation; and the
interpretations' conditions on the initial states, from the network's start and each machine's `FsInit`
(`etcdNetExts_initP`: `etcdFsSem`, `Fs.fsSemWithS`, keeps `ExtSemantics`'s default `initLocal`, so `FsInit` is
the statement's to give).

For a single-process program that listens (`notes/single-process-restore.md`): `etcdNetFs_start` (`FsExts.lean`'s
`etcdFs_start` over this bundle), `netAddrFrees_start` (the right to listen at each address of a list of distinct
valid addresses, `netAddrFree`, from the net extension's listening tokens in `extsGlobalStart` and program start's
`addrClaim`), and `addrOk_loopback` (`127.0.0.1:<p>`, `1 ≤ p < 32768`, is valid: `Net.addrOk`).
-/
module

public import Robustness.Statement
public import Perennial.GooseLang.InitAdequacy
public import GooseLang.Ext.Net.Ghost
public import GooseLang.Ext.IdIssue.Specs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersDefs
public import GooseLang.Ext.Net.Proto
public import Proof.net.InvNet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- **The etcd examples' extensions over the network**: the request ids' issue record (`idutil`'s generator: the member's),
the Linux file extension (the member's WAL, backend and snapshots; every machine's `fileutil`
initializer) and the net extension (the member's listener, the client's connection): the etcd
examples' `etcdFsExts` with the net extension (`notes/etcd-dist-plan.md`, D2's `net` half, option (i)). -/
@[reducible] def etcdNetExts : GooseExts := ⟨[idIssueExt, Fs.fsExt, Net.netExt]⟩

attribute [local instance] etcdNetExts

/-- Their semantics: the issue record's, the file extension's restricted by `etcdSQ` (`etcdFsSem`: no
file system call fails), the net extension's own (every fault it allows). -/
@[reducible] def etcdNetExtsSemantics : GooseSemantics :=
  ⟨(idIssue_semantics, etcdFsSem, Net.net_semantics, ⟨⟩)⟩

/-- Their ghost state: each extension's own. -/
@[reducible] def etcdNetExtsInterp : GooseInterp := ⟨(idIssue_interp, Fs.fs_interp, Net.net_interp, ⟨⟩)⟩

attribute [local instance] etcdNetExtsSemantics etcdNetExtsInterp etcdFsSem

set_option linter.defProp false in
/-- The programs have the issue record (by computation). -/
@[reducible] def etcdNetExts_hasIdIssue : HasExt idIssueExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

set_option linter.defProp false in
/-- The programs have the Linux file extension, at `etcdFsSem` (by computation). -/
@[reducible] def etcdNetExts_hasFs : letI := etcdFsSem; HasExt Fs.fsExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

set_option linter.defProp false in
/-- The programs have the net extension (by computation). -/
@[reducible] def etcdNetExts_hasNet : HasExt Net.netExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

attribute [local instance] etcdNetExts_hasIdIssue etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSemOk

/-- **The interpretations' conditions on the machines' initial states**, for `etcdNetExts`: the network's
from `Robust`'s `extsInitGlobal` (no connection), each machine's files from `FsInit` (the issue record's
are `True`). -/
theorem etcdNetExts_initP (g : GlobalState) (nodes : List (Expr × state))
    (Hfs : ∀ m, m ∈ nodes → Fs.FsInit (extLocal Fs.fsExt m.2.world)) :
    extsInitGlobal g → (∀ m, m ∈ nodes → extsInitLocal m.2 g) →
      extsInitgP g.globalWorld ∧ ∀ m, m ∈ nodes → extsInitP m.2.world g.globalWorld :=
  fun hg _ => ⟨⟨trivial, trivial, hg.2.2.1, trivial⟩, fun m hm => ⟨trivial, Hfs m hm, trivial, trivial⟩⟩


section start
variable [GoGlobalContext] {GF : BundledGFunctors}

/-- The local start resources of `etcdNetExts`: the file extension's (`osStart`). -/
theorem etcdNetExts_localStart [L : GooseLocalGS GF] (w : ExtsLocalState etcdNetExts.exts) :
    extsLocalStart (GF := GF) w ⊢ Fs.osStart (Fs.gooseOsGS (L := L)) (extLocal Fs.fsExt w) :=
  (sep_elim_right (P := iprop(True))).trans sep_elim_left

/-- The global start resources of `etcdNetExts`: the net extension's (`netStart`). -/
theorem etcdNetExts_globalStart [G : GooseGlobalGS .hasLC GF] (g : ExtsGlobalState etcdNetExts.exts) :
    extsGlobalStart (GF := GF) g ⊢ Net.netStart (extGlobalGS Net.netExt) (extGlobal Net.netExt g) :=
  sep_elim_right.trans (sep_elim_right.trans sep_elim_left)

/-- **The start resources of the file extension** over `etcdNetExts` (`FsExts.lean`'s `etcdFs_start`):
the invariant of the mapped cells, every file, and the tree's history. -/
theorem etcdNetFs_start [hG : HeapGS .hasLC GF] (σ : state) (h : Fs.FsInit (extLocal Fs.fsExt σ.world)) :
    ⊢ extsLocalStart (GF := GF) σ.world ={⊤}=∗
      Fs.osInv (L := hG.goose_localGS) ∗
      ([∗map] i ↦ f ∈ (extLocal Fs.fsExt σ.world).fs.files, Fs.osFileStart (L := hG.goose_localGS) i f) ∗
      Fs.osTree (L := hG.goose_localGS) (DFrac.own 1) (extLocal Fs.fsExt σ.world).fs.roots
        ((extLocal Fs.fsExt σ.world).fs.treeDur, []) := by
  have Hl := etcdNetExts_localStart (GF := GF) (L := hG.goose_localGS) σ.world
  have hdisk : ∀ i f, (extLocal Fs.fsExt σ.world).fs.files !! i = some f →
      ∃ vs sz, f = Fs.OsFile.ofDisk vs sz := fun i f hf =>
    let ⟨img, sz, _, e⟩ := (h.2.2.2.2.2.2.1 i f hf).2; ⟨img, sz, e⟩
  iintro Hs
  icases Hl $$ Hs with Hs
  unfold Fs.osStart Fs.osStartF Fs.treeStart Fs.bytesMap Fs.metaMap
  icases Hs with ⟨⟨Hb, Hm, Hv⟩, Hd⟩
  ihave Hfs := Fs.start_files (Fs.gooseOsGS (L := hG.goose_localGS)) hdisk $$ [Hb Hm]
  · iframe
  imod Fs.osInv_alloc (L := hG.goose_localGS) ⊤ $$ Hv with #Hinv
  imodintro
  iframe Hinv
  isplitl [Hfs]
  · iapply BigSepM.bigSepM_mono (fun {i f} _ =>
      (Fs.fileStart_eq (L := hG.goose_localGS) i f).1) $$ Hfs
  · unfold Fs.osTree; iexact Hd

/-- **The right to listen at each address of `As`** (distinct, valid: `Net.addrOk`), from the net
extension's start resources (each address's listening token `netLisTok`, `Net.netStart`) and program
start's claims (`addrClaim`, `goose_adequacy_start`'s `startRights`). -/
theorem netAddrFrees_start [hG : HeapGS .hasLC GF] (g : ExtsGlobalState etcdNetExts.exts)
    (As : List GoString) (hAs : As.Nodup) (hok : ∀ a ∈ As, Net.addrOk a = true) :
    extsGlobalStart (GF := GF) g ∗ ([∗list] a ∈ As, addrClaim (GF := GF) a) ⊢
      [∗list] a ∈ As, netAddrFree (GF := GF) a := by
  iintro ⟨Hg, Hc⟩
  ihave Hs := etcdNetExts_globalStart (GF := GF) g $$ Hg
  unfold Net.netStart
  icases Hs with ⟨-, Htoks⟩
  ihave Htoks := Net.bigSepM_take_list
    (fun a _ => Net.netLisTok (extGlobalGS Net.netExt (G := hG.goose_globalGS)) a) (fun _ => ())
    (Net.addrSpace ()) As hAs (fun a ha => Net.addrSpace_lookup_ok _ (hok a ha)) $$ Htoks
  ihave Hb : ([∗list] a ∈ As, iprop(addrClaim (GF := GF) a ∗
      Net.netLisTok (extGlobalGS Net.netExt (G := hG.goose_globalGS)) a)) $$ [Hc Htoks]
  · iapply BigSepL.bigSepL_sep_eqv.2
    iframe Hc Htoks
  iapply BigSepL.bigSepL_mono (Φ := fun _ a => iprop(addrClaim (GF := GF) a ∗
    Net.netLisTok (extGlobalGS Net.netExt (G := hG.goose_globalGS)) a)) ?_ $$ Hb
  intro k a hk
  unfold netAddrFree
  iintro ⟨Hc, Ht⟩
  iframe Hc
  iexists etcdNetExts_hasNet
  iframe Ht
  ipureintro
  exact hok a (List.mem_of_getElem? hk)

end start

section addrs

open etcdstart

/-! ## A generated loopback address is valid for the net extension (`Net.addrOk`) -/

/-- The digits' value, as the net extension reads it (`Net.digitsVal`), is `decNumeral?`'s fold. -/
theorem digitsVal_foldl (s : List w8) (acc : Nat) :
    Net.digitsVal s acc = s.foldl (fun acc c => acc.bind fun n =>
      if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (10 * n + (c.toNat - 48)) else none) (some acc) := by
  have hnone : ∀ t : List w8, t.foldl (fun acc c => acc.bind fun n =>
      if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (10 * n + (c.toNat - 48)) else none) none = none := by
    intro t; induction t with
    | nil => rfl
    | cons _ _ ih => exact ih
  induction s generalizing acc with
  | nil => rfl
  | cons c s ih =>
    by_cases h : 48 ≤ c.toNat ∧ c.toNat ≤ 57
    · have hd : Net.isDigit c = true := by simp [Net.isDigit, h.1, h.2]
      simp only [Net.digitsVal, hd, ite_true, List.foldl_cons, Option.bind_some, h, and_self]
      rw [ih, Nat.mul_comm]
    · have hd : Net.isDigit c = false := by
        simp only [Net.isDigit, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
      simp only [Net.digitsVal, hd, Bool.false_eq_true, ite_false, List.foldl_cons, Option.bind_some,
        h, hnone]

/-- The net extension's canonical numeral (`Net.decNat`) is `decNumeral?`. -/
theorem decNat_eq_decNumeral (s : List w8) : Net.decNat s = decNumeral? s := by
  match s with
  | [] => rfl
  | [c] =>
    unfold decNumeral?
    rw [if_neg (by simp)]
    exact digitsVal_foldl [c] 0
  | c :: d :: t =>
    unfold decNumeral?
    by_cases h : c.toNat = 48
    · have : c = W8 48 := by apply BitVec.eq_of_toNat_eq; simp [W8, h]
      simp [Net.decNat, h, this]
    · have : c ≠ W8 48 := fun e => h (by rw [e]; rfl)
      rw [if_neg (by simpa [W8] using this)]
      simp only [Net.decNat, h, ite_false]
      exact digitsVal_foldl _ 0

/-- `Net.splitBy` of a string without the separator: the one piece. -/
theorem splitBy_noSep (sep : w8) (s cur : List w8) (h : ∀ c ∈ s, c.toNat ≠ sep.toNat) :
    Net.splitBy sep s cur = [cur.reverse ++ s] := by
  induction s generalizing cur with
  | nil => simp [Net.splitBy]
  | cons c s ih =>
    simp only [Net.splitBy, h c (List.mem_cons_self ..), ite_false]
    rw [ih (c :: cur) (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp

/-- **A generated loopback address is valid** (`Net.addrOk`, D20 of the net extension: the
single-process theorems take the listening tokens of their addresses from the extension's start, which
holds them for valid addresses only): `127.0.0.1:<p>` for any port `1 ≤ p < 32768` (below Linux's
ephemeral range, `Net.portOk`). -/
theorem addrOk_loopback (p : w64) (h1 : 1 ≤ p.toNat) (h2 : p.toNat < 32768) :
    Net.addrOk (go!"127.0.0.1:" ++ decStr p) = true := by
  have hcol : ∀ c ∈ decStr p, c.toNat ≠ (58 : w8).toNat := fun c hc => by
    have := decStr_digits p c hc; simp; omega
  have hsplit : Net.splitBy 58 (go!"127.0.0.1:" ++ decStr p) [] = [go!"127.0.0.1", decStr p] := by
    generalize decStr p = s at hcol ⊢
    have := splitBy_noSep 58 s [] hcol
    simp only [List.reverse_nil, List.nil_append] at this
    simp [Net.splitBy]
    exact this
  have hh : Net.splitBy 46 (go!"127.0.0.1" : List w8) [] = [go!"127", go!"0", go!"0", go!"1"] := by
    decide
  have e127 : Net.decNat (go!"127" : List w8) = some 127 := by decide
  have e0 : Net.decNat (go!"0" : List w8) = some 0 := by decide
  have e1 : Net.decNat (go!"1" : List w8) = some 1 := by decide
  have ep : Net.decNat (decStr p) = some p.toNat := by
    rw [decNat_eq_decNumeral]; exact decNumeral_decStr p (by omega)
  unfold Net.addrOk Net.parseAddr
  rw [hsplit]
  simp only
  rw [hh]
  simp only [e127, e0, e1, ep]
  simp [Net.portOk]
  omega

end addrs

end EtcdGrove
end Perennial

end
