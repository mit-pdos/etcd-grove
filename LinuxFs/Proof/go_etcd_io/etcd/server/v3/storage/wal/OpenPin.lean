/- Lean-first (no Rocq counterpart).

# Where `Open` finds its WAL directory (W3/W5's gaps 1 and 2, `notes/wal-fsext-plan.md`)

`openAtIndex`'s pin reads, from the program's half of the area claim (`walAreaRes`) and the WAL
invariant's contents, what the area holds at the WAL's name `nm`: the WAL's directory if the WAL
exists (`WalsAt`; then `osPathS` extends to `dir`), nothing if it does not (`AbsentNone`; then
`os.Open(dir)` fails, `selectWALFiles.specAbsent`).

* `walDirAt_pure`: the pure core, over a claim of the area among the invariant's claims.
* `walInvBody_areaAt`: the program's claim is that one (`osNames_same_name`, the shared invariant's
  disjointness), so the program's own claim's names say it.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateNamed

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **What the area claims hold at a WAL's name** (pure): the WAL's directory if it exists, nothing
if it does not. -/
theorem walDirAt_pure {C : WalCodec} {Mr : WalMarshal} {R : Roots} {jr : Ino} {s : AbsDiskState}
    {Ls : GMap GoString WalLay} {cl : List Claim} {n : Nat} {dir nm : GoString} {N : NameSet}
    {h : NamesH} (hok : WalsOk C Mr R jr s Ls cl n) (hA : WalsAt jr Ls cl)
    (han : AbsentNone s jr cl n) (hin : InArea s.area dir nm) (hc : (jr, N, h) ∈ cl)
    (hN : N.Mem nm) :
    (s.wal !! dir = none → h.cur !! nm = none) ∧
    ∀ d, s.wal !! dir = some d → ∃ lay, Ls !! dir = some lay ∧ lay.nm = nm ∧
      h.cur !! nm = some (.dir lay.j) := by
  refine ⟨fun hd => (han dir nm hin hd).1 N h hc hN, fun d hd => ?_⟩
  obtain ⟨lay, nm', -, hl, hin', -, hnm, -⟩ := hok.1 dir d hd
  have e : nm' = nm := by
    have := hin'.2.symm.trans hin.2
    exact (List.append_cancel_left this)
  subst e
  exact ⟨lay, hl, hnm, by rw [← hnm] at hN ⊢; exact hA.at hl hc hN⟩

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **The area at a WAL's name, from the program's claim** (see the file header): the contents
unchanged, the program's claim back, and what it holds at `nm`. -/
theorem walInvBody_areaAt (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir nm : GoString) (N : NameSet) (dq : DFrac) (h : NamesH) {Em : CoPset}
    (hin : InArea r dir nm) (hN : N.Mem nm) (hE : ↑osShN ⊆ Em) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ osSharedInv (L := L) R -∗
      osNames (L := L) jr N dq h ={Em}=∗
      walInvBody (L := L) (W := W) C Mr R jr r s ∗ osNames (L := L) jr N dq h ∗
      ⌜(s.wal !! dir = none → h.cur !! nm = none) ∧
        ∀ d, s.wal !! dir = some d → ∃ J, h.cur !! nm = some (.dir J)⌝ := by
  iintro Hb #Hsh Hn
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n0, %F, Hg, %Har, Hcl, Hcm, Hlays, %Hok, %Hco, Hcr, Htl, %Han, %Hnm, Hpk,
    Hk, %HAt, Hnms⟩
  obtain ⟨N', h', hc', hN'⟩ := Hco nm hin.1
  have hmem : ((jr, N', h'), DFrac.own (1 : Qp).half) ∈
      cl.map (fun c => (c, DFrac.own (1 : Qp).half)) := List.mem_map_of_mem hc'
  unfold osClaims
  icases (BigSepL.bigSepL_mem_acc hmem) $$ Hcl with ⟨Hi, Hcl⟩
  imod osNames_same_name R jr N N' dq _ h h' nm hN hN' hE $$ Hsh Hn Hi with ⟨%Hk', Hn, Hi⟩
  obtain ⟨rfl, rfl⟩ := Hk'
  ihave Hcl := Hcl $$ Hi
  have hin' : InArea s.area dir nm := by rw [Har]; exact hin
  obtain ⟨h1, h2⟩ := walDirAt_pure Hok HAt Han.1 hin' hc' hN
  imodintro
  iframe Hn
  isplitl
  · iexists Ls, cl, n0, F
    iframe
    ipureintro; exact ⟨Har, Hok, Hco, Han, Hnm, HAt⟩
  ipureintro
  refine ⟨h1, fun d hd => ?_⟩
  obtain ⟨lay, -, -, he⟩ := h2 d hd
  exact ⟨lay.j, he⟩

end iris

end WalFs
end EtcdGrove
end Perennial

end
