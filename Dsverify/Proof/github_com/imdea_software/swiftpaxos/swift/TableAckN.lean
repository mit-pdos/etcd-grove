/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/TableAckN.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`(*SDep).Unmarshal` and `(*MNewLeaderAckN).Unmarshal` (17) on a stream whose next bytes are
their encodings (the stream law), and the table's entry 17.

* `SDep.Unmarshal`: a count (`dep_v1`: the encoding's own), then 8 bytes per command id;
* `MNewLeaderAckN.Unmarshal`: a 12-byte header, then four lists each with its own count (the
  ids, 8 bytes each; the phases, 8 bytes each; the commands, by `Command.Unmarshal`; the
  dependency lists, by `SDep.Unmarshal` under `depNext`). Each count is the message's
  (`ackN_v1` … `ackN_v4`); at the end the stream law identifies what was read with the body of
  a well-formed message (`ackN_final`): in particular a command's two ignored value bytes are
  the encoder's zeros.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.TableOptAcks

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.tbl

/-! ## `MNewLeaderAckN`'s stream (pure) -/

/-- A command as `Command.Unmarshal` decodes it (the value's two ignored bytes `x`, `y`). -/
structure DCmd where
  op : w8
  k : w64
  l0 : w8
  l1 : w8
  x : w8
  y : w8
  v : List w8

def DCmd.bytes (c : DCmd) : List w8 := [c.op] ++ sp.le64 c.k ++ sp.decValue c.l0 c.l1 c.x c.y c.v
def DCmd.ok (c : DCmd) : Prop := c.l0.toNat + 256 * c.l1.toNat = c.v.length
def DCmd.cmd (c : DCmd) : sp.Cmd := ⟨c.op, c.k, c.v⟩

def aH (r b c : w32) : List w8 := sp.le32 r ++ sp.le32 b ++ sp.le32 c
def aI (es : List sp.RepEntry) : List w8 := (es.map (fun e => sp.encCmdId e.id)).flatten
def aP (es : List sp.RepEntry) : List w8 := (es.map (fun e => sp.le64 e.phase)).flatten
def aC (es : List sp.RepEntry) : List w8 := (es.map (fun e => sp.encCmd e.cmd)).flatten
def aD (es : List sp.RepEntry) : List w8 := (es.map (fun e => sp.encDep e.dep)).flatten

def fI (ids : List sp.CmdId) : List w8 := (ids.map sp.encCmdId).flatten
def fP (phs : List w64) : List w8 := (phs.map sp.le64).flatten
def fC (dcs : List DCmd) : List w8 := (dcs.map DCmd.bytes).flatten
def fD (dps : List (List sp.CmdId)) : List w8 := (dps.map sp.encDep).flatten

theorem ackN_body (r b c : w32) (es : List sp.RepEntry) :
    (sp.Msg.newLeaderAckN r b c es).body = aH r b c ++ (sp.varintLen es.length ++ (aI es ++
      (sp.varintLen es.length ++ (aP es ++ (sp.varintLen es.length ++ (aC es ++
        (sp.varintLen es.length ++ aD es))))))) := by
  simp [sp.Msg.body, sp.RepEntry.encCmds, aH, aI, aP, aC, aD, List.append_assoc]

theorem aH_length (r b c : w32) : (aH r b c).length = 12 := by
  simp [aH, sp.le32, u32Le_length]

theorem le64_length (x : w64) : (sp.le64 x).length = 8 := by simp [sp.le64, u64Le_length]

theorem fI_length (ids : List sp.CmdId) : (fI ids).length = 8 * ids.length := cmdIds_length ids

theorem aI_eq (es : List sp.RepEntry) : aI es = fI (es.map (·.id)) := by
  simp [aI, fI, List.map_map, Function.comp_def]

theorem fP_length (phs : List w64) : (fP phs).length = 8 * phs.length := by
  induction phs with
  | nil => simp [fP]
  | cons x l ih => simp only [fP, List.map_cons, List.flatten_cons, List.length_append,
      le64_length, List.length_cons] at ih ⊢; omega

theorem aP_eq (es : List sp.RepEntry) : aP es = fP (es.map (·.phase)) := by
  simp [aP, fP, List.map_map, Function.comp_def]

theorem aD_eq (es : List sp.RepEntry) : aD es = fD (es.map (·.dep)) := by
  simp [aD, fD, List.map_map, Function.comp_def]

theorem pf_le64 : sp.PF (fun _ : w64 => True) sp.le64 := fun _ _ _ _ _ _ h => sp.le64_peel h

theorem pf_dep : sp.PF sp.depWf sp.encDep := fun _ _ _ _ ha hb h => sp.dep_peel ha hb h

theorem vl_eq {d u rest : List w8} {k : Nat} (ht : sp.uvTerm d)
    (h : d ++ u = sp.varintLen k ++ rest) : d = sp.varintLen k := by
  unfold sp.varintLen at *; exact (sp.cw.uvTerm_peel ht h).1

theorem dcmd_peel {c : DCmd} {c' : sp.Cmd} {u v : List w8} (hc : c.ok) (hw : c'.wf)
    (h : c.bytes ++ u = sp.encCmd c' ++ v) : c.cmd = c' ∧ c.bytes = sp.encCmd c' ∧ u = v := by
  simp only [DCmd.bytes, sp.encCmd, List.append_assoc] at h
  obtain ⟨h1, h⟩ := sp.byte_peel h
  obtain ⟨h2, h⟩ := sp.le64_peel h
  obtain ⟨h3, h4, h5⟩ := sp.decValue_peel hc hw h
  refine ⟨?_, ?_, h5⟩
  · cases c'; simp_all [DCmd.cmd]
  · simp [DCmd.bytes, sp.encCmd, h1, h2, h4, List.append_assoc]

theorem fC_peel : ∀ (dcs : List DCmd) (es : List sp.RepEntry) (u v : List w8),
    dcs.length = es.length → (∀ c ∈ dcs, c.ok) → (∀ e ∈ es, e.cmd.wf) →
    fC dcs ++ u = aC es ++ v → dcs.map DCmd.cmd = es.map (·.cmd) ∧ fC dcs = aC es ∧ u = v
  | [], [], u, v, _, _, _, h => by simpa [fC, aC] using h
  | c :: dcs, e :: es, u, v, hl, hc, he, h => by
    simp only [fC, aC, List.map_cons, List.flatten_cons, List.append_assoc] at h
    obtain ⟨h1, h2, h3⟩ := dcmd_peel (hc c (by simp)) (he e (by simp)) h
    obtain ⟨h4, h5, h6⟩ := fC_peel dcs es u v (by simpa using hl) (fun z hz => hc z (by simp [hz]))
      (fun z hz => he z (by simp [hz])) (by simpa [fC, aC, List.append_assoc] using h3)
    refine ⟨by simp [h1, h4], ?_, h6⟩
    show c.bytes ++ fC dcs = sp.encCmd e.cmd ++ aC es
    rw [h2, h5]
  | [], _ :: _, _, _, hl, _, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _, _ => by simp at hl

theorem ackN_of_next {d : List w8} (h : sp.nextOk (W8 17) d) :
    ∃ (r b c : w32) (es : List sp.RepEntry) (u w : List w8),
      (sp.Msg.newLeaderAckN r b c es).wf ∧
      d ++ u = aH r b c ++ (sp.varintLen es.length ++ (aI es ++
        (sp.varintLen es.length ++ (aP es ++ (sp.varintLen es.length ++ (aC es ++
          (sp.varintLen es.length ++ (aD es ++ w)))))))) := by
  obtain ⟨m, w, hw, -, hc, u, hu⟩ := h
  cases m <;> simp [sp.Msg.code, sp.rpcTable] at hc
  rename_i r b c es
  refine ⟨r, b, c, es, u, w, hw, ?_⟩
  rw [hu, ackN_body]; simp only [List.append_assoc]

/-- After the header, the ids' count. -/
theorem ackN_v1 {hdr d : List w8} (hl : hdr.length = 12) (ht : sp.uvTerm d)
    (h : sp.nextOk (W8 17) (hdr ++ d)) : ∃ k, d = sp.varintLen k ∧ k < 2 ^ 62 := by
  obtain ⟨r, b, c, es, u, w, hw, hu⟩ := ackN_of_next h
  simp only [List.append_assoc] at hu
  obtain ⟨-, hu⟩ := List.append_inj hu (by rw [hl, aH_length])
  exact ⟨es.length, vl_eq ht hu, hw.1⟩

/-- The phases' count. -/
theorem ackN_v2 {hdr d : List w8} {n1 : Nat} {ids : List sp.CmdId} (hl : hdr.length = 12)
    (hi : ids.length = n1) (ht : sp.uvTerm d)
    (h : sp.nextOk (W8 17) (hdr ++ sp.varintLen n1 ++ fI ids ++ d)) :
    ∃ k, d = sp.varintLen k ∧ k < 2 ^ 62 := by
  obtain ⟨r, b, c, es, u, w, hw, hu⟩ := ackN_of_next h
  simp only [List.append_assoc] at hu
  obtain ⟨-, hu⟩ := List.append_inj hu (by rw [hl, aH_length])
  obtain ⟨hn, hu⟩ := sp.cw.varintLen_peel hu
  obtain ⟨-, hu⟩ := List.append_inj hu (by rw [fI_length, aI_eq, fI_length]; simp; omega)
  exact ⟨es.length, vl_eq ht hu, hw.1⟩

/-- The commands' count. -/
theorem ackN_v3 {hdr d : List w8} {n1 n2 : Nat} {ids : List sp.CmdId} {phs : List w64}
    (hl : hdr.length = 12) (hi : ids.length = n1) (hp : phs.length = n2) (ht : sp.uvTerm d)
    (h : sp.nextOk (W8 17) (hdr ++ sp.varintLen n1 ++ fI ids ++ sp.varintLen n2 ++ fP phs ++ d)) :
    ∃ k, d = sp.varintLen k ∧ k < 2 ^ 62 := by
  obtain ⟨r, b, c, es, u, w, hw, hu⟩ := ackN_of_next h
  simp only [List.append_assoc] at hu
  obtain ⟨-, hu⟩ := List.append_inj hu (by rw [hl, aH_length])
  obtain ⟨hn, hu⟩ := sp.cw.varintLen_peel hu
  obtain ⟨-, hu⟩ := List.append_inj hu (by rw [fI_length, aI_eq, fI_length]; simp; omega)
  obtain ⟨hn2, hu⟩ := sp.cw.varintLen_peel hu
  obtain ⟨-, hu⟩ := List.append_inj hu (by rw [fP_length, aP_eq, fP_length]; simp; omega)
  exact ⟨es.length, vl_eq ht hu, hw.1⟩

/-- The dependency lists' count. -/
theorem ackN_v4 {hdr d : List w8} {n1 n2 n3 : Nat} {ids : List sp.CmdId} {phs : List w64}
    {dcs : List DCmd} (hl : hdr.length = 12) (hi : ids.length = n1) (hp : phs.length = n2)
    (hc : dcs.length = n3) (hok : ∀ c ∈ dcs, c.ok) (ht : sp.uvTerm d)
    (h : sp.nextOk (W8 17) (hdr ++ sp.varintLen n1 ++ fI ids ++ sp.varintLen n2 ++ fP phs ++
      sp.varintLen n3 ++ fC dcs ++ d)) :
    ∃ k, d = sp.varintLen k ∧ k < 2 ^ 62 := by
  obtain ⟨r, b, c, es, u, w, hw, hu⟩ := ackN_of_next h
  simp only [List.append_assoc] at hu
  obtain ⟨-, hu⟩ := List.append_inj hu (by rw [hl, aH_length])
  obtain ⟨hn, hu⟩ := sp.cw.varintLen_peel hu
  obtain ⟨-, hu⟩ := List.append_inj hu (by rw [fI_length, aI_eq, fI_length]; simp; omega)
  obtain ⟨hn2, hu⟩ := sp.cw.varintLen_peel hu
  obtain ⟨-, hu⟩ := List.append_inj hu (by rw [fP_length, aP_eq, fP_length]; simp; omega)
  obtain ⟨hn3, hu⟩ := sp.cw.varintLen_peel hu
  obtain ⟨-, -, hu⟩ := fC_peel dcs es _ _ (by omega) hok (fun e he => (hw.2 e he).1)
    (by simpa [List.append_assoc] using hu)
  exact ⟨es.length, vl_eq ht hu, hw.1⟩

/-- A dependency list's law. -/
theorem ackN_dep {hdr d : List w8} {n1 n2 n3 n4 : Nat} {ids : List sp.CmdId} {phs : List w64}
    {dcs : List DCmd} {prev : List (List sp.CmdId)} (hl : hdr.length = 12)
    (hi : ids.length = n1) (hp : phs.length = n2) (hc : dcs.length = n3)
    (hok : ∀ c ∈ dcs, c.ok) (hpv : ∀ x ∈ prev, sp.depWf x) (hn : prev.length < n4)
    (h : sp.nextOk (W8 17) (hdr ++ sp.varintLen n1 ++ fI ids ++ sp.varintLen n2 ++ fP phs ++
      sp.varintLen n3 ++ fC dcs ++ sp.varintLen n4 ++ fD prev ++ d)) :
    depNext d := by
  obtain ⟨r, b, c, es, u, w, hw, hu⟩ := ackN_of_next h
  simp only [List.append_assoc] at hu
  obtain ⟨-, hu⟩ := List.append_inj hu (by rw [hl, aH_length])
  obtain ⟨hn1, hu⟩ := sp.cw.varintLen_peel hu
  obtain ⟨-, hu⟩ := List.append_inj hu (by rw [fI_length, aI_eq, fI_length]; simp; omega)
  obtain ⟨hn2, hu⟩ := sp.cw.varintLen_peel hu
  obtain ⟨-, hu⟩ := List.append_inj hu (by rw [fP_length, aP_eq, fP_length]; simp; omega)
  obtain ⟨hn3, hu⟩ := sp.cw.varintLen_peel hu
  obtain ⟨-, -, hu⟩ := fC_peel dcs es _ _ (by omega) hok (fun e he => (hw.2 e he).1)
    (by simpa [List.append_assoc] using hu)
  obtain ⟨hn4, hu⟩ := sp.cw.varintLen_peel hu
  rw [aD_eq] at hu
  obtain ⟨y, w', hy, hd⟩ := elems_next pf_dep prev (es.map (·.dep)) d u w hpv
    (by simp only [List.mem_map]; rintro _ ⟨e, he, rfl⟩; exact (hw.2 e he).2)
    (by simp; omega) (by simpa [fD, List.append_assoc] using hu)
  exact ⟨y, w', hy, hd⟩

/-- The whole message: what was read is a well-formed message's body after the header. -/
theorem ackN_final {hdr : List w8} {n1 n2 n3 n4 : Nat} {ids : List sp.CmdId} {phs : List w64}
    {dcs : List DCmd} {dps : List (List sp.CmdId)} (hl : hdr.length = 12)
    (hi : ids.length = n1) (hp : phs.length = n2) (hc : dcs.length = n3)
    (hok : ∀ c ∈ dcs, c.ok) (hd : dps.length = n4) (hdw : ∀ x ∈ dps, sp.depWf x)
    (h : sp.nextOk (W8 17) (hdr ++ sp.varintLen n1 ++ fI ids ++ sp.varintLen n2 ++ fP phs ++
      sp.varintLen n3 ++ fC dcs ++ sp.varintLen n4 ++ fD dps)) :
    ∃ es : List sp.RepEntry, es.length < 2 ^ 62 ∧ (∀ e ∈ es, e.cmd.wf ∧ sp.depWf e.dep) ∧
      n1 = es.length ∧ n2 = es.length ∧ n3 = es.length ∧ n4 = es.length ∧
      ids = es.map (·.id) ∧ phs = es.map (·.phase) ∧ dcs.map DCmd.cmd = es.map (·.cmd) ∧
      fC dcs = aC es ∧ dps = es.map (·.dep) := by
  obtain ⟨r, b, c, es, u, w, hw, hu⟩ := ackN_of_next h
  simp only [List.append_assoc] at hu
  obtain ⟨-, hu⟩ := List.append_inj hu (by rw [hl, aH_length])
  obtain ⟨hn1, hu⟩ := sp.cw.varintLen_peel hu
  obtain ⟨hI, hu⟩ := List.append_inj hu (by rw [fI_length, aI_eq, fI_length]; simp; omega)
  obtain ⟨hn2, hu⟩ := sp.cw.varintLen_peel hu
  obtain ⟨hP, hu⟩ := List.append_inj hu (by rw [fP_length, aP_eq, fP_length]; simp; omega)
  obtain ⟨hn3, hu⟩ := sp.cw.varintLen_peel hu
  obtain ⟨hC1, hC2, hu⟩ := fC_peel dcs es _ _ (by omega) hok (fun e he => (hw.2 e he).1)
    (by simpa [List.append_assoc] using hu)
  obtain ⟨hn4, hu⟩ := sp.cw.varintLen_peel hu
  rw [aD_eq] at hu
  obtain ⟨hD, -⟩ := sp.elems_peel pf_dep dps (es.map (·.dep)) u w (by simp; omega) hdw
    (by simp only [List.mem_map]; rintro _ ⟨e, he, rfl⟩; exact (hw.2 e he).2)
    (by simpa [fD] using hu)
  rw [aI_eq] at hI; rw [aP_eq] at hP
  obtain ⟨hI', -⟩ := sp.elems_peel sp.pf_cmdId ids (es.map (·.id)) [] [] (by simp; omega)
    (fun _ _ => trivial) (fun _ _ => trivial) (by simpa [fI] using hI)
  obtain ⟨hP', -⟩ := sp.elems_peel pf_le64 phs (es.map (·.phase)) [] [] (by simp; omega)
    (fun _ _ => trivial) (fun _ _ => trivial) (by simpa [fP] using hP)
  exact ⟨es, hw.1, hw.2, hn1, hn2, hn3, hn4, hI', hP', hC1, hC2, hD⟩

theorem dep_v1 {d : List w8} (ht : sp.uvTerm d) (h : depNext d) :
    ∃ n, d = sp.varintLen n ∧ n < 2 ^ 62 := by
  obtain ⟨ds, w, hw, hp⟩ := h
  refine ⟨ds.length, ?_, hw⟩
  apply uv_count (X := []) ht
  simpa [sp.encDep, List.append_assoc] using hp

section specs2
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]

/-- `(*MNewLeaderAckN).Unmarshal(br)`: without an error, the bytes read are the body of a
well-formed `.newLeaderAckN r b c es`, which `t` represents (`swift.msgRepM`'s shape). -/
abbrev MNewLeaderAckN.Unmarshal.specS : Prop :=
  ∀ (t : Loc) (v : swift.MNewLeaderAckN) (br : Loc) (rd : GoInterface)
    (I : List w8 → IProp netDistGF) (R : List w8),
  {{ ctxV ∗ bufio.readerOk rd I ∗ sp.streamLaw br rd I R (sp.nextOk (W8 17)) ∗
      bufio.ownReader br rd I R ∗ t ↦ v }}
    (App (Val (t @!! go.GoType.PointerType swift.MNewLeaderAckN.ty @!! go!"Unmarshal"))
      (Val #(interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br)))
  {{ (err : GoInterface), RET #err; ∃ data : List w8, bufio.ownReader br rd I (R ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (r b c : w32) (es : List sp.RepEntry) (ids ph cm dp : GoSlice)
          (cmL : List state.Command) (dpL : List swift.SDep),
          ⌜data = (sp.Msg.newLeaderAckN r b c es).body ∧ (sp.Msg.newLeaderAckN r b c es).wf⌝ ∗
          t ↦ swift.MNewLeaderAckN.mk r b c ids ph cm dp ∗
          ids ↦* (es.map (fun e => ofCmdId e.id)) ∗ ph ↦* (es.map (·.phase)) ∗ cm ↦* cmL ∗
          dp ↦* dpL ∗ ⌜cmL.length = es.length ∧ dpL.length = es.length⌝ ∗
          [∗list] i ↦ e ∈ es, ∃ (cc : state.Command) (sd : swift.SDep),
            ⌜cmL[i]? = some cc ∧ dpL[i]? = some sd⌝ ∗ swift.repEntryOwn cc sd e) ∨
        (⌜err ≠ interface.nil⌝ ∗ ∃ v' : swift.MNewLeaderAckN, t ↦ v')) }}

end specs2

/-- A decoded command in the `Cmds` slice. -/
def cmdOf (p : GoSlice × DCmd) : state.Command := state.Command.mk p.2.op p.2.k p.1
/-- A decoded dependency list in the `Deps` slice. -/
def depOf (p : GoSlice × List sp.CmdId) : swift.SDep := swift.SDep.mk p.1

section zip
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]

theorem zipOwn : ∀ (es : List sp.RepEntry) (cps : List (GoSlice × DCmd))
    (dps : List (GoSlice × List sp.CmdId)),
    cps.map (fun p => p.2.cmd) = es.map (·.cmd) → dps.map Prod.snd = es.map (·.dep) →
    ([∗list] p ∈ cps, p.1 ↦* p.2.v) ∗ ([∗list] p ∈ dps, p.1 ↦* p.2.map ofCmdId) ⊢
    [∗list] i ↦ e ∈ es, ∃ (cc : state.Command) (sd : swift.SDep),
      ⌜(cps.map cmdOf)[i]? = some cc ∧ (dps.map depOf)[i]? = some sd⌝ ∗
      swift.repEntryOwn cc sd e
  | [], [], [], _, _ => by
    iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | e :: es, c :: cps, d :: dps, h1, h2 => by
    simp only [List.map_cons, List.cons.injEq] at h1 h2
    iintro ⟨Hc, Hd⟩
    icases (BigSepL.bigSepL_cons).1 $$ Hc with ⟨Hc0, Hc⟩
    icases (BigSepL.bigSepL_cons).1 $$ Hd with ⟨Hd0, Hd⟩
    iapply (BigSepL.bigSepL_cons).2
    isplitl [Hc0 Hd0]
    · iexists cmdOf c, depOf d
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      unfold swift.repEntryOwn
      iexists c.1
      have hc : c.2.cmd = e.cmd := h1.1
      have hd : d.2 = e.dep := h2.1
      simp only [cmdOf, depOf, ← hc, ← hd, DCmd.cmd]
      iframe Hd0 Hc0
    ihave H := zipOwn es cps dps h1.2 h2.2 $$ [$Hc $Hd]
    iExactEq H; simp only [List.map_cons, List.getElem?_cons_succ]
  | [], _ :: _, _, h1, _ => by simp at h1
  | [], [], _ :: _, _, h2 => by simp at h2
  | _ :: _, [], _, h1, _ => by simp at h1
  | _ :: _, _ :: _, [], _, h2 => by simp at h2

end zip

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions]

set_option goose.wp.extras true

omit [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions] in
/-- The first `b` bytes of the slice `p[:a]` (capacity `c`) as `p[:b]`, and back. -/
theorem slice_shrink (p : Loc) (a b c : Nat) (xs : List w8) (hl : xs.length = a)
    (hb : 0 < b) (hba : b ≤ a) (hc : a ≤ c) (hc63 : c < 2 ^ 63) :
    (slice.mk p (W64 a) (W64 c) ↦* xs : IProp netDistGF) ⊢
      slice.mk p (W64 b) (W64 c) ↦* xs.take b ∗
      (∀ ys : List w8, ⌜ys.length = b⌝ -∗ slice.mk p (W64 b) (W64 c) ↦* ys -∗
        slice.mk p (W64 a) (W64 c) ↦* (ys ++ xs.drop b)) := by
  have ha' : sint.Z (W64 (a : Int)) = a := by word
  have hb' : sint.Z (W64 (b : Int)) = b := by word
  have hc' : sint.Z (W64 (c : Int)) = c := by word
  have hbn : sint.nat (W64 (b : Int)) = b := by word
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, -⟩)
  · exfalso; obtain ⟨-, h2⟩ := H; subst h2; simp at hl; omega
  simp only
  icases (array_split (V := w8) (W64 b) p (DFrac.own 1) _ _ (by rw [hb', ha']; omega)).1 $$ H
    with ⟨H1, H2⟩
  isplitl [H1]
  · iright
    isplitl
    · iExactEq H1; rw [hb', hbn]
    · ipureintro; rw [hb', hc']; omega
  iintro %ys %hys Hys
  icases Hys with (%H | ⟨Hys, -⟩)
  · exfalso; obtain ⟨-, h2⟩ := H; subst h2; simp at hys; omega
  iright
  isplitl
  · iapply (array_split (V := w8) (W64 b) p (DFrac.own 1) _
      (array.mk (sint.Z (W64 (a : Int))) (ys ++ xs.drop b)) (by rw [hb', ha']; omega)).2
    isplitl [Hys]
    · iExactEq Hys; simp only [hb', hbn]; congr 2; simp [hys]
    · iExactEq H2; simp only [hbn]; congr 2; simp [hys]
  · ipureintro; rw [ha', hc']; omega

omit [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions] in
theorem slice_shrink12 (p : Loc) (b : Nat) (xs : List w8) (hl : xs.length = 12)
    (hb : 0 < b) (hba : b ≤ 12) :
    (slice.mk p (W64 12) (W64 12) ↦* xs : IProp netDistGF) ⊢
      slice.mk p (W64 b) (W64 12) ↦* xs.take b ∗
      (∀ ys : List w8, ⌜ys.length = b⌝ -∗ slice.mk p (W64 b) (W64 12) ↦* ys -∗
        slice.mk p (W64 12) (W64 12) ↦* (ys ++ xs.drop b)) :=
  slice_shrink p 12 b 12 xs hl hb hba (by omega) (by omega)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem SDep.Unmarshal.wp_proof : SDep.Unmarshal.specS (hG := hG) := by
  intro t v br rd I R
  wp_start as ⟨#Hctx, #Hrd, #Hlaw, Hown, Ht⟩
  ihave #Hctx' := Hctx
  iunfold ctxV at Hctx'
  icases Hctx' with ⟨#Hio, #Hbuf, #Hbin, %ov, #Hov, %Hovn⟩
  ihave #Hbr := bufio.bufioReadsOk br rd I $$ [$Hbuf $Hrd]
  have hts : go.typeSetContains (go.GoType.PointerType bufio.Reader.ty) swift.byteReader.ty = true := by
    go_type_set
  try wp_auto
  rw [hts]
  wp_auto
  wp_apply wp_readVarint br rd _ _ ov $$ [$Hrd $Hown $Hov] as %x %err ⟨%vd1, Hown, %Hx⟩
  · ipureintro; exact Hovn
  rcases err with e | _
  · wp_auto
    iapply HΦ
    iexists _
    iframe Hown
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists _
    iexact Ht
  obtain ⟨ht1, hb1, hx1⟩ := Hx rfl
  icases streamLaw_use br rd I R vd1 _ $$ [$Hlaw $Hown] with ⟨Hown, %Hn1⟩
  obtain ⟨n, rfl, hn62⟩ := dep_v1 ht1 Hn1
  obtain ⟨-, rfl⟩ := swift.rd.varint_count n hb1 hx1
  try wp_auto
  wp_apply wp_slice_make2 (V := swift.CommandId) (W64 n) as %sl ⟨Hsl, -⟩
  · ipureintro; word
  ihave %Hsllen := ownSlice_len $$ Hsl
  rw [show sint.nat (W64 n) = n by word]
  try wp_auto
  ihave Hb := slice_array b_ptr 10 (Perennial.zero_val (GoArray w8 10)) (by decide) $$ b
  rw [show (Perennial.zero_val (GoArray w8 10)).arr = List.replicate 10 (W8 0) from rfl] at *
  ihave Hb4 := slice_take4 b_ptr _ (by simp) $$ Hb
  ihave HL : (∃ (j : Nat) (ds : List sp.CmdId) (y0 y1 y2 y3 : w8) (bsv : GoSlice),
      "i" ∷ i_ptr ↦ W64 j ∗ "bs" ∷ bs_ptr ↦ bsv ∗
      "Ht" ∷ t ↦ swift.SDep.mk sl ∗
      "Hsl" ∷ sl ↦* (ds.map ofCmdId ++ List.replicate (n - j) (zero_val swift.CommandId)) ∗
      "Hown" ∷ bufio.ownReader br rd I (R ++ (sp.varintLen n ++ (ds.map sp.encCmdId).flatten)) ∗
      "Hb4" ∷ slice.mk b_ptr (W64 4) (W64 10) ↦* [y0, y1, y2, y3] ∗
      "%Hj" ∷ ⌜j ≤ n ∧ ds.length = j⌝ : IProp netDistGF) $$ [i bs Ht Hsl Hown Hb4]
  · iexists 0, [], W8 0, W8 0, W8 0, W8 0, _
    simp only [List.map_nil, List.nil_append, Nat.sub_zero, List.flatten_nil, List.append_nil]
    iframe
    ipureintro; simp
  wp_for HL
  wp_if_destruct
  · obtain ⟨hjn', rfl⟩ := Hj
    have hjn : ds.length < n := by
      have h1 : sint.Z (W64 (ds.length : Int)) = ds.length := by word
      have h2 : sint.Z (W64 (n : Int)) = n := by word
      omega
    have hlook : (ds.map ofCmdId ++ List.replicate (n - ds.length) (zero_val swift.CommandId))[
        ((ds.length : Nat) : Int).toNat]? = some (zero_val swift.CommandId) := by
      rw [Int.toNat_natCast, List.getElem?_append_right (by simp)]
      simp only [List.length_map, Nat.sub_self]
      rw [List.getElem?_replicate]; simp; omega
    have hbnd : 0 ≤ sint.Z (W64 (ds.length : Int)) ∧
        sint.Z (W64 (ds.length : Int)) < sint.Z sl.len := by
      obtain ⟨h1, h2⟩ := Hsllen
      have hn' : sint.nat (W64 (n : Int)) = n := by word
      simp only [List.length_replicate, hn'] at h1
      have h3 : sint.nat sl.len = (sint.Z sl.len).toNat := rfl
      have : sint.Z (W64 (ds.length : Int)) = ds.length := by word
      rw [this]; omega
    have hk64 : sint.Z (W64 (ds.length : Int)) = ds.length := by word
    icases ownSlice_elem_acc ((ds.length : Nat) : Int) (zero_val swift.CommandId) sl _ _
      (by omega) hlook $$ Hsl with ⟨He, Hsl⟩
    rw [show R ++ (sp.varintLen n ++ (ds.map sp.encCmdId).flatten) =
      (R ++ (sp.varintLen n ++ (ds.map sp.encCmdId).flatten)) ++ [] from (List.append_nil _).symm]
    generalize hB : R ++ (sp.varintLen n ++ (ds.map sp.encCmdId).flatten) = B
    rd4 a0 a1 a2 a3
    rw [ite_cond_eq_true _ _ (eq_true hbnd), hk64]
    wp_auto
    rd4 b0 b1 b2 b3
    rw [ite_cond_eq_true _ _ (eq_true hbnd), hk64]
    wp_auto
    let x : sp.CmdId := ⟨leToU32 [a0, a1, a2, a3], leToU32 [b0, b1, b2, b3]⟩
    ihave Hsl := Hsl $$ %(ofCmdId x) [He]
    · iExactEq He; simp only [x, ofCmdId, encoding.binary.leToU32_4]
    subst hB
    wp_for_post
    iframe
    iexists ds.length + 1, ds ++ [x], b0, b1, b2, b3, _
    isplitl [i]
    · iExactEq i; congr 1; word
    isplitl [bs]
    · iexact bs
    isplitl [Ht]
    · iexact Ht
    isplitl [Hsl]
    · iExactEq Hsl; congr 1
      rw [Int.toNat_natCast, swift.rd.set_slot ofCmdId ds _ _ (n - ds.length) (by omega)]
      simp [List.map_append, List.append_assoc, show n - (ds.length + 1) = n - ds.length - 1 by omega]
    isplitl [Hown]
    · iExactEq Hown; congr 1
      simp only [List.map_append, List.flatten_append, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc, List.nil_append]
      simp only [x, sp.encCmdId, sp.le32]
      rw [leToU32_le _ rfl, leToU32_le _ rfl]
    isplitl [Hb4]
    · iexact Hb4
    ipureintro
    simp; omega
  · obtain ⟨hjn', rfl⟩ := Hj
    have hjn : ds.length = n := by
      have h1 : sint.Z (W64 (ds.length : Int)) = ds.length := by word
      have h2 : sint.Z (W64 (n : Int)) = n := by word
      omega
    subst hjn
    try wp_auto
    iapply HΦ
    iexists sp.encDep ds
    isplitl [Hown]
    · iExactEq Hown; simp only [sp.encDep]
    ileft
    isplitr
    · ipureintro; rfl
    iexists ds, sl
    isplitr
    · ipureintro; exact ⟨rfl, hn62⟩
    iframe Ht
    iExactEq Hsl; simp

theorem list4 {l : List w8} (h : l.length = 4) : ∃ a b c d, l = [a, b, c, d] := by
  match l, h with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

theorem list8 {l : List w8} (h : l.length = 8) : ∃ a b c d e f g k, l = [a, b, c, d, e, f, g, k] := by
  match l, h with
  | [a, b, c, d, e, f, g, k], _ => exact ⟨a, b, c, d, e, f, g, k, rfl⟩

theorem eight_of {data : List w8} {u : List w8} (hl : data.length ≤ u.length) (hu : u.length = 8)
    (he : sint.Z (W64 8) ≤ (data.length : Int)) :
    ∃ a b c d e f g h, data = [a, b, c, d, e, f, g, h] := by
  have : sint.Z (W64 8) = 8 := rfl
  match data with
  | [a, b, c, d, e, f, g, h] => exact ⟨a, b, c, d, e, f, g, h, rfl⟩
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
  | [_, _, _, _, _, _, _] => rw [this] at he; simp at he
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => simp at hl; omega

set_option hygiene false in
/-- `ReadAtLeast(wire, bs, 4)` into `b[:4]` of a 12-byte `b` (an error returns), the loads. -/
macro "rd4c" a:ident b:ident c:ident d:ident : tactic => `(tactic| (
  try wp_auto
  try rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 4 - W64 0 = W64 4 from rfl,
    show W64 12 - W64 0 = W64 12 from rfl]
  try wp_auto
  wp_apply bufio.wp_ReadAtLeast _ _ _ _ [_, _, _, _] (W64 4) (by simp; decide) $$
    [Hown Hb4] as %n0 %err ⟨%data0, %Hd0, Hb4, Hown, #He0⟩
  · iframe Hown Hb4 Hbr
  obtain ⟨-, hdl0, herr0⟩ := Hd0
  rcases err with e0 | _
  · subst hB
    wp_auto
    wp_for_post
    iapply HΦ
    iexists _
    isplitl [Hown]
    · iExactEq Hown; simp only [List.append_assoc]; rfl
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists _
    iexact Ht
  obtain ⟨$a, $b, $c, $d, rfl⟩ := four_of hdl0 rfl (herr0.1 rfl)
  try isimp only [List.length_cons, List.length_nil, List.drop_succ_cons, List.drop_zero,
    List.drop_nil, List.append_nil, Nat.reduceAdd] at Hb4
  try rw [List.append_assoc B _ [$a, $b, $c, $d]]
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ _ (by decide) $$ [Hb4] as Hb4
  · iframe Hb4; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 1)) _ _ _ (by decide) $$ [Hb4] as Hb4
  · iframe Hb4; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 2)) _ _ _ (by decide) $$ [Hb4] as Hb4
  · iframe Hb4; ipureintro; rfl
  try wp_auto
  wp_apply wp_load_slice_index _ (sint.Z (W64 3)) _ _ _ (by decide) $$ [Hb4] as Hb4
  · iframe Hb4; ipureintro; rfl
  try wp_auto))

set_option hygiene false in
/-- Load `bs[i]` of `Hb`. -/
macro "ldb" i:num : tactic => `(tactic| (
  wp_apply wp_load_slice_index _ (sint.Z (W64 $i)) _ _ _ (by decide) $$ [Hb] as Hb
  · iframe Hb; ipureintro; rfl
  try wp_auto))

set_option hygiene false in
/-- Load `bs[i]` of the hypothesis `h`. -/
macro "ldh" h:ident i:num : tactic => `(tactic| (
  wp_apply wp_load_slice_index _ (sint.Z (W64 $i)) _ _ _ (by decide) $$ [$h:ident] as $h:ident
  · iframe $h:ident; ipureintro; rfl
  try wp_auto))

end proofs

section proofs2
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [io.Assumptions] [errors.Assumptions]
  [bufio.Assumptions] [replica.defs.Assumptions] [state.Assumptions]

set_option goose.wp.extras true

set_option maxRecDepth 40000 in
set_option maxHeartbeats 16000000 in
theorem MNewLeaderAckN.Unmarshal.wp_proof (wp_SDep : SDep.Unmarshal.specS (hG := hG))
    (wp_Val : state.Value.Unmarshal.spec (GF := netDistGF)) :
    MNewLeaderAckN.Unmarshal.specS (hG := hG) := by
  intro t v br rd I R
  wp_start as ⟨#Hctx, #Hrd, #Hlaw, Hown, Ht⟩
  ihave #Hctx' := Hctx
  iunfold ctxV at Hctx'
  icases Hctx' with ⟨#Hio, #Hbuf, #Hbin, %ov, #Hov, %Hovn⟩
  ihave #Hbr := bufio.bufioReadsOk br rd I $$ [$Hbuf $Hrd]
  have hts : go.typeSetContains (go.GoType.PointerType bufio.Reader.ty) swift.byteReader.ty = true := by
    go_type_set
  try wp_auto
  rw [hts]
  wp_auto
  ihave Hb := slice_array b_ptr 12 (Perennial.zero_val (GoArray w8 12)) (by decide) $$ b
  rw [show (Perennial.zero_val (GoArray w8 12)).arr = List.replicate 12 (W8 0) from rfl]
  try rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 12 - W64 0 = W64 12 from rfl]
  try wp_auto
  wp_apply bufio.wp_ReadAtLeast _ _ _ _ _ (W64 12) (by simp; decide) $$
    [$Hio $Hbr $Hown $Hb] as %n %err ⟨%data, %Hd, Hb, Hown, #He⟩
  obtain ⟨hn, hdl, herr⟩ := Hd
  rcases err with e | _
  · wp_auto
    iapply HΦ
    iexists data
    iframe Hown
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists v
    iexact Ht
  have h12 : data.length = 12 := by
    have := herr.1 rfl; simp at hdl; have : sint.Z (W64 12) = 12 := rfl; omega
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, rfl⟩ :
      ∃ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 : w8,
        data = [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] := by
    match data, h12 with
    | [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11], _ =>
      exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, rfl⟩
  isimp only [List.length_cons, List.length_nil, List.drop_replicate, List.append_nil,
    Nat.reduceAdd, Nat.sub_self, List.replicate_zero] at Hb
  wp_auto
  ldb 0
  ldb 1
  ldb 2
  ldb 3
  ldb 4
  ldb 5
  ldb 6
  ldb 7
  ldb 8
  ldb 9
  ldb 10
  ldb 11
  isimp only [← encoding.binary.leToU32_4] at Ht
  have hHdr : [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] = aH (leToU32 [d0, d1, d2, d3])
      (leToU32 [d4, d5, d6, d7]) (leToU32 [d8, d9, d10, d11]) := by
    simp only [aH, sp.le32]; rw [leToU32_le _ rfl, leToU32_le _ rfl, leToU32_le _ rfl]; rfl
  rw [hHdr]
  generalize leToU32 [d0, d1, d2, d3] = r0
  generalize leToU32 [d4, d5, d6, d7] = b0
  generalize leToU32 [d8, d9, d10, d11] = c0
  clear hHdr hdl herr hn
  -- the ids' count
  wp_apply wp_readVarint br rd _ _ ov $$ [$Hrd $Hown $Hov] as %x %err ⟨%vd1, Hown, %Hx⟩
  · ipureintro; exact Hovn
  rcases err with e | _
  · wp_auto
    iapply HΦ
    iexists _
    rw [List.append_assoc]
    iframe Hown
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists _
    iexact Ht
  obtain ⟨ht1, hb1, hx1⟩ := Hx rfl
  icases streamLaw_use br rd I R (aH r0 b0 c0 ++ vd1) _ $$ [$Hlaw Hown] with ⟨Hown, %Hn1⟩
  · iExactEq Hown; simp only [List.append_assoc]
  obtain ⟨n1, rfl, hn1⟩ := ackN_v1 (aH_length _ _ _) ht1 Hn1
  obtain ⟨-, rfl⟩ := swift.rd.varint_count n1 hb1 hx1
  try wp_auto
  wp_apply wp_slice_make2 (V := swift.CommandId) (W64 n1) as %sl1 ⟨Hsl, -⟩
  · ipureintro; word
  ihave %Hsllen := ownSlice_len $$ Hsl
  rw [show sint.nat (W64 n1) = n1 by word]
  try wp_auto
  icases slice_shrink12 b_ptr 4 (aH r0 b0 c0) (aH_length _ _ _) (by omega) (by omega)
    $$ Hb with ⟨Hb4, W4⟩
  obtain ⟨y0, y1, y2, y3, hy⟩ := list4 (l := (aH r0 b0 c0).take 4) (by simp [aH_length])
  rw [hy]
  ihave HL : (∃ (j : Nat) (ids : List sp.CmdId) (y0 y1 y2 y3 : w8) (bsv : GoSlice),
      "i" ∷ i_ptr ↦ W64 j ∗ "bs" ∷ bs_ptr ↦ bsv ∗
      "Ht" ∷ t ↦ swift.MNewLeaderAckN.mk r0 b0 c0 sl1 v.Phases' v.Cmds' v.Deps' ∗
      "Hsl" ∷ sl1 ↦* (ids.map ofCmdId ++ List.replicate (n1 - j) (zero_val swift.CommandId)) ∗
      "Hown" ∷ bufio.ownReader br rd I (R ++ (aH r0 b0 c0 ++ sp.varintLen n1 ++ fI ids)) ∗
      "Hb4" ∷ slice.mk b_ptr (W64 4) (W64 12) ↦* [y0, y1, y2, y3] ∗
      "%Hj" ∷ ⌜j ≤ n1 ∧ ids.length = j⌝ : IProp netDistGF) $$ [i bs Ht Hsl Hown Hb4]
  · iexists 0, [], y0, y1, y2, y3, _
    simp only [List.map_nil, List.nil_append, Nat.sub_zero, fI, List.flatten_nil, List.append_nil]
    iframe
    ipureintro; simp
  wp_for HL
  wp_if_destruct
  · obtain ⟨hjn', rfl⟩ := Hj
    have hjn : ids.length < n1 := by
      have h1 : sint.Z (W64 (ids.length : Int)) = ids.length := by word
      have h2 : sint.Z (W64 (n1 : Int)) = n1 := by word
      omega
    have hlook : (ids.map ofCmdId ++ List.replicate (n1 - ids.length) (zero_val swift.CommandId))[
        ((ids.length : Nat) : Int).toNat]? = some (zero_val swift.CommandId) := by
      rw [Int.toNat_natCast, List.getElem?_append_right (by simp)]
      simp only [List.length_map, Nat.sub_self]
      rw [List.getElem?_replicate]; simp; omega
    have hbnd : 0 ≤ sint.Z (W64 (ids.length : Int)) ∧
        sint.Z (W64 (ids.length : Int)) < sint.Z sl1.len := by
      obtain ⟨h1, h2⟩ := Hsllen
      have hn' : sint.nat (W64 (n1 : Int)) = n1 := by word
      simp only [List.length_replicate, hn'] at h1
      have h3 : sint.nat sl1.len = (sint.Z sl1.len).toNat := rfl
      have : sint.Z (W64 (ids.length : Int)) = ids.length := by word
      rw [this]; omega
    have hk64 : sint.Z (W64 (ids.length : Int)) = ids.length := by word
    icases ownSlice_elem_acc ((ids.length : Nat) : Int) (zero_val swift.CommandId) sl1 _ _
      (by omega) hlook $$ Hsl with ⟨He, Hsl⟩
    rw [show R ++ (aH r0 b0 c0 ++ sp.varintLen n1 ++ fI ids) =
      (R ++ (aH r0 b0 c0 ++ sp.varintLen n1 ++ fI ids)) ++ [] from (List.append_nil _).symm]
    generalize hB : R ++ (aH r0 b0 c0 ++ sp.varintLen n1 ++ fI ids) = B
    rd4c a0 a1 a2 a3
    rw [ite_cond_eq_true _ _ (eq_true hbnd), hk64]
    wp_auto
    rd4c e0 e1 e2 e3
    rw [ite_cond_eq_true _ _ (eq_true hbnd), hk64]
    wp_auto
    let x : sp.CmdId := ⟨leToU32 [a0, a1, a2, a3], leToU32 [e0, e1, e2, e3]⟩
    ihave Hsl := Hsl $$ %(ofCmdId x) [He]
    · iExactEq He; simp only [x, ofCmdId, encoding.binary.leToU32_4]
    subst hB
    wp_for_post
    iframe
    iexists ids.length + 1, ids ++ [x], e0, e1, e2, e3, _
    isplitl [i]
    · iExactEq i; congr 1; word
    isplitl [bs]
    · iexact bs
    isplitl [Ht]
    · iexact Ht
    isplitl [Hsl]
    · iExactEq Hsl; congr 1
      rw [Int.toNat_natCast, swift.rd.set_slot ofCmdId ids _ _ (n1 - ids.length) (by omega)]
      simp [List.map_append, List.append_assoc, show n1 - (ids.length + 1) = n1 - ids.length - 1 by omega]
    isplitl [Hown]
    · iExactEq Hown; congr 1
      simp only [fI, List.map_append, List.flatten_append, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc, List.nil_append]
      simp only [x, sp.encCmdId, sp.le32]
      rw [leToU32_le _ rfl, leToU32_le _ rfl]
    isplitl [Hb4]
    · iexact Hb4
    ipureintro
    simp; omega
  obtain ⟨hjn', rfl⟩ := Hj
  have hjn : ids.length = n1 := by
    have h1 : sint.Z (W64 (ids.length : Int)) = ids.length := by word
    have h2 : sint.Z (W64 (n1 : Int)) = n1 := by word
    omega
  subst hjn
  simp only [Nat.sub_self, List.replicate_zero, List.append_nil] at *
  ihave Hb := W4 $$ %([y0, y1, y2, y3] : List w8) %rfl Hb4
  -- the phases' count
  wp_apply wp_readVarint br rd _ _ ov $$ [$Hrd $Hown $Hov] as %x2 %err ⟨%vd2, Hown, %Hx2⟩
  · ipureintro; exact Hovn
  rcases err with e | _
  · wp_auto
    iapply HΦ
    iexists _
    isplitl [Hown]
    · iExactEq Hown; simp only [List.append_assoc]; rfl
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists _
    iexact Ht
  obtain ⟨ht2, hb2, hx2⟩ := Hx2 rfl
  icases streamLaw_use br rd I R (aH r0 b0 c0 ++ sp.varintLen ids.length ++ fI ids ++ vd2) _ $$
    [$Hlaw Hown] with ⟨Hown, %Hn2⟩
  · iExactEq Hown; simp only [List.append_assoc]
  obtain ⟨n2, rfl, hn2⟩ := ackN_v2 (aH_length _ _ _) rfl ht2 Hn2
  obtain ⟨-, rfl⟩ := swift.rd.varint_count n2 hb2 hx2
  try wp_auto
  wp_apply wp_slice_make2 (V := w64) (W64 n2) as %sl2 ⟨Hph, -⟩
  · ipureintro; word
  ihave %Hphlen := ownSlice_len $$ Hph
  rw [show sint.nat (W64 n2) = n2 by word]
  try wp_auto
  icases slice_shrink12 b_ptr 8 ([y0, y1, y2, y3] ++ (aH r0 b0 c0).drop 4)
    (by simp [aH_length]) (by omega) (by omega) $$ Hb with ⟨Hb8, W8⟩
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, hz⟩ :=
    list8 (l := ([y0, y1, y2, y3] ++ (aH r0 b0 c0).drop 4).take 8) (by simp [aH_length])
  rw [hz]
  ihave HL2 : (∃ (j : Nat) (phs : List w64) (z0 z1 z2 z3 z4 z5 z6 z7 : w8) (bsv : GoSlice),
      "i" ∷ i_ptr ↦ W64 j ∗ "bs" ∷ bs_ptr ↦ bsv ∗
      "Ht" ∷ t ↦ swift.MNewLeaderAckN.mk r0 b0 c0 sl1 sl2 v.Cmds' v.Deps' ∗
      "Hph" ∷ sl2 ↦* (phs ++ List.replicate (n2 - j) (zero_val w64)) ∗
      "Hown" ∷ bufio.ownReader br rd I (R ++ (aH r0 b0 c0 ++ sp.varintLen ids.length ++ fI ids ++
        sp.varintLen n2 ++ fP phs)) ∗
      "Hb8" ∷ slice.mk b_ptr (W64 8) (W64 12) ↦* [z0, z1, z2, z3, z4, z5, z6, z7] ∗
      "%Hj" ∷ ⌜j ≤ n2 ∧ phs.length = j⌝ : IProp netDistGF) $$ [i bs Ht Hph Hown Hb8]
  · iexists 0, [], z0, z1, z2, z3, z4, z5, z6, z7, _
    simp only [List.nil_append, Nat.sub_zero, fP, List.map_nil, List.flatten_nil, List.append_nil]
    iframe
    ipureintro; simp
  wp_for HL2
  wp_if_destruct
  · obtain ⟨hjn', rfl⟩ := Hj
    have hjn : phs.length < n2 := by
      have h1 : sint.Z (W64 (phs.length : Int)) = phs.length := by word
      have h2 : sint.Z (W64 (n2 : Int)) = n2 := by word
      omega
    have hbnd : 0 ≤ sint.Z (W64 (phs.length : Int)) ∧
        sint.Z (W64 (phs.length : Int)) < sint.Z sl2.len := by
      obtain ⟨h1, h2⟩ := Hphlen
      have hn' : sint.nat (W64 (n2 : Int)) = n2 := by word
      simp only [List.length_replicate, hn'] at h1
      have h3 : sint.nat sl2.len = (sint.Z sl2.len).toNat := rfl
      have : sint.Z (W64 (phs.length : Int)) = phs.length := by word
      rw [this]; omega
    have hk64 : sint.Z (W64 (phs.length : Int)) = phs.length := by word
    try wp_auto
    try rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, show W64 8 - W64 0 = W64 8 from rfl,
      show W64 12 - W64 0 = W64 12 from rfl]
    try wp_auto
    wp_apply bufio.wp_ReadAtLeast _ _ _ _ [_, _, _, _, _, _, _, _] (W64 8) (by simp; decide) $$
      [Hown Hb8] as %n0 %err ⟨%data0, %Hd0, Hb8, Hown, #He0⟩
    · iframe Hown Hb8 Hbr
    obtain ⟨-, hdl0, herr0⟩ := Hd0
    rcases err with e0 | _
    · wp_auto
      wp_for_post
      iapply HΦ
      iexists _
      isplitl [Hown]
      · iExactEq Hown; simp only [List.append_assoc]; rfl
      iright
      isplitr
      · ipureintro; intro h; cases h
      iexists _
      iexact Ht
    obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := eight_of hdl0 rfl (herr0.1 rfl)
    try isimp only [List.length_cons, List.length_nil, List.drop_succ_cons, List.drop_zero,
      List.drop_nil, List.append_nil, Nat.reduceAdd] at Hb8
    try wp_auto
    ldh Hb8 0
    ldh Hb8 1
    ldh Hb8 2
    ldh Hb8 3
    ldh Hb8 4
    ldh Hb8 5
    ldh Hb8 6
    ldh Hb8 7
    rw [ite_cond_eq_true _ _ (eq_true hbnd), ← encoding.binary.leToU64_8]
    wp_apply wp_store_slice_index _ _ _ _ $$ [Hph] as Hph
    · iframe Hph; ipureintro; rw [hk64]; simp; omega
    try wp_auto
    wp_for_post
    iframe
    iexists phs.length + 1, phs ++ [leToU64 [a0, a1, a2, a3, a4, a5, a6, a7]], a0, a1, a2, a3, a4,
      a5, a6, a7, _
    isplitl [i]
    · iExactEq i; congr 1; word
    isplitl [bs]
    · iexact bs
    isplitl [Ht]
    · iexact Ht
    isplitl [Hph]
    · iExactEq Hph; congr 1
      rw [hk64, Int.toNat_natCast, List.set_append_right _ _ (by simp)]
      simp only [Nat.sub_self]
      obtain ⟨q, hq⟩ : ∃ q, n2 - phs.length = q + 1 := ⟨n2 - phs.length - 1, by omega⟩
      rw [hq, List.replicate_succ, List.set_cons_zero, show n2 - (phs.length + 1) = q by omega]
      simp
    isplitl [Hown]
    · iExactEq Hown; congr 1
      simp only [fP, List.map_append, List.flatten_append, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
      simp only [sp.le64]
      rw [leToU64_le _ rfl]
    isplitl [Hb8]
    · iexact Hb8
    ipureintro
    simp; omega
  obtain ⟨hjn', rfl⟩ := Hj
  have hjn : phs.length = n2 := by
    have h1 : sint.Z (W64 (phs.length : Int)) = phs.length := by word
    have h2 : sint.Z (W64 (n2 : Int)) = n2 := by word
    omega
  subst hjn
  simp only [Nat.sub_self, List.replicate_zero, List.append_nil] at *
  -- the commands' count
  wp_apply wp_readVarint br rd _ _ ov $$ [$Hrd $Hown $Hov] as %x3 %err ⟨%vd3, Hown, %Hx3⟩
  · ipureintro; exact Hovn
  rcases err with e | _
  · wp_auto
    iapply HΦ
    iexists _
    isplitl [Hown]
    · iExactEq Hown; simp only [List.append_assoc]; rfl
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists _
    iexact Ht
  obtain ⟨ht3, hb3, hx3⟩ := Hx3 rfl
  icases streamLaw_use br rd I R (aH r0 b0 c0 ++ sp.varintLen ids.length ++ fI ids ++
    sp.varintLen phs.length ++ fP phs ++ vd3) _ $$ [$Hlaw Hown] with ⟨Hown, %Hn3⟩
  · iExactEq Hown; simp only [List.append_assoc]
  obtain ⟨n3, rfl, hn3⟩ := ackN_v3 (aH_length _ _ _) rfl rfl ht3 Hn3
  obtain ⟨-, rfl⟩ := swift.rd.varint_count n3 hb3 hx3
  try wp_auto
  wp_apply wp_slice_make2 (V := state.Command) (W64 n3) as %sl3 ⟨Hcm, -⟩
  · ipureintro; word
  ihave %Hcmlen := ownSlice_len $$ Hcm
  rw [show sint.nat (W64 n3) = n3 by word]
  try wp_auto
  ihave HL3 : (∃ (j : Nat) (cps : List (GoSlice × DCmd)),
      "i" ∷ i_ptr ↦ W64 j ∗
      "Ht" ∷ t ↦ swift.MNewLeaderAckN.mk r0 b0 c0 sl1 sl2 sl3 v.Deps' ∗
      "Hcm" ∷ sl3 ↦* (cps.map cmdOf ++ List.replicate (n3 - j) (zero_val state.Command)) ∗
      "Hcv" ∷ ([∗list] p ∈ cps, p.1 ↦* p.2.v) ∗
      "Hown" ∷ bufio.ownReader br rd I (R ++ (aH r0 b0 c0 ++ sp.varintLen ids.length ++ fI ids ++
        sp.varintLen phs.length ++ fP phs ++ sp.varintLen n3 ++ fC (cps.map Prod.snd))) ∗
      "%Hj" ∷ ⌜j ≤ n3 ∧ cps.length = j ∧ ∀ p ∈ cps, p.2.ok⌝ : IProp netDistGF) $$ [i Ht Hcm Hown]
  · iexists 0, []
    simp only [List.map_nil, List.nil_append, Nat.sub_zero, fC, List.flatten_nil, List.append_nil]
    iframe
    isplitl
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; simp
  wp_for HL3
  wp_if_destruct
  · obtain ⟨hjn', rfl, hok⟩ := Hj
    have hjn : cps.length < n3 := by
      have h1 : sint.Z (W64 (cps.length : Int)) = cps.length := by word
      have h2 : sint.Z (W64 (n3 : Int)) = n3 := by word
      omega
    have hlook : (cps.map cmdOf ++ List.replicate (n3 - cps.length) (zero_val state.Command))[
        ((cps.length : Nat) : Int).toNat]? = some (zero_val state.Command) := by
      rw [Int.toNat_natCast, List.getElem?_append_right (by simp)]
      simp only [List.length_map, Nat.sub_self]
      rw [List.getElem?_replicate]; simp; omega
    have hbnd : 0 ≤ sint.Z (W64 (cps.length : Int)) ∧
        sint.Z (W64 (cps.length : Int)) < sint.Z sl3.len := by
      obtain ⟨h1, h2⟩ := Hcmlen
      have hn' : sint.nat (W64 (n3 : Int)) = n3 := by word
      simp only [List.length_replicate, hn'] at h1
      have h3 : sint.nat sl3.len = (sint.Z sl3.len).toNat := rfl
      have : sint.Z (W64 (cps.length : Int)) = cps.length := by word
      rw [this]; omega
    have hk64 : sint.Z (W64 (cps.length : Int)) = cps.length := by word
    rw [ite_cond_eq_true _ _ (eq_true hbnd)]
    rw [hk64]
    icases ownSlice_elem_acc ((cps.length : Nat) : Int) (zero_val state.Command) sl3 _ _
      (by omega) hlook $$ Hcm with ⟨He, Hcm⟩
    wp_apply wp_Command_Unmarshal wp_Val _ _ _ (bufio.ownReader br rd I) _ $$
      [$Hio $Hbin $Hbr $Hown $He] as %err ⟨%data, Hown, Hres⟩
    icases Hres with (⟨%Hen, %op, %k, %l0, %l1, %x, %y, %vv, %vs, ⟨%Hd, %Hl⟩, He, Hvs⟩ |
      ⟨%Hen, %c', He⟩)
    · subst Hen Hd
      ihave Hcm := Hcm $$ He
      wp_auto
      wp_for_post
      iframe
      iexists cps.length + 1, cps ++ [(vs, ⟨op, k, l0, l1, x, y, vv⟩)]
      isplitl [i]
      · iExactEq i; congr 1; word
      isplitl [Ht]
      · iexact Ht
      isplitl [Hcm]
      · iExactEq Hcm; congr 1
        rw [Int.toNat_natCast, swift.rd.set_slot cmdOf cps _ _ (n3 - cps.length) (by omega)]
        simp [List.map_append, List.append_assoc, cmdOf,
          show n3 - (cps.length + 1) = n3 - cps.length - 1 by omega]
      isplitl [Hcv Hvs]
      · iapply (BigSepL.bigSepL_snoc).2
        iframe
      isplitl [Hown]
      · iExactEq Hown; congr 1
        simp [fC, DCmd.bytes, List.map_append, List.flatten_append, List.append_assoc]
      ipureintro
      refine ⟨by omega, by simp, ?_⟩
      intro p hp
      rcases List.mem_append.1 hp with h' | h'
      · exact hok p h'
      · simp at h'; subst h'; exact Hl
    · rcases err with eo | _
      · wp_auto
        wp_for_post
        iapply HΦ
        iexists _
        isplitl [Hown]
        · iExactEq Hown; simp only [List.append_assoc]; rfl
        iright
        isplitr
        · ipureintro; exact Hen
        iexists _
        iexact Ht
      · exact absurd rfl Hen
  obtain ⟨hjn', hjl, hok⟩ := Hj
  have hjn : j = n3 := by
    have h1 : sint.Z (W64 (j : Int)) = j := by word
    have h2 : sint.Z (W64 (n3 : Int)) = n3 := by word
    omega
  subst hjn hjl
  simp only [Nat.sub_self, List.replicate_zero, List.append_nil] at *
  have hokc : ∀ c ∈ cps.map Prod.snd, c.ok := by
    intro c hc; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc; exact hok p hp
  -- the dependency lists' count
  wp_apply wp_readVarint br rd _ _ ov $$ [$Hrd $Hown $Hov] as %x4 %err ⟨%vd4, Hown, %Hx4⟩
  · ipureintro; exact Hovn
  rcases err with e | _
  · wp_auto
    iapply HΦ
    iexists _
    isplitl [Hown]
    · iExactEq Hown; simp only [List.append_assoc]; rfl
    iright
    isplitr
    · ipureintro; intro h; cases h
    iexists _
    iexact Ht
  obtain ⟨ht4, hb4, hx4⟩ := Hx4 rfl
  icases streamLaw_use br rd I R (aH r0 b0 c0 ++ sp.varintLen ids.length ++ fI ids ++
    sp.varintLen phs.length ++ fP phs ++ sp.varintLen cps.length ++ fC (cps.map Prod.snd) ++ vd4) _ $$
    [$Hlaw Hown] with ⟨Hown, %Hn4⟩
  · iExactEq Hown; simp only [List.append_assoc]
  obtain ⟨n4, rfl, hn4⟩ := ackN_v4 (aH_length _ _ _) rfl rfl (by simp) hokc ht4 Hn4
  obtain ⟨-, rfl⟩ := swift.rd.varint_count n4 hb4 hx4
  try wp_auto
  wp_apply wp_slice_make2 (V := swift.SDep) (W64 n4) as %sl4 ⟨Hdp, -⟩
  · ipureintro; word
  ihave %Hdplen := ownSlice_len $$ Hdp
  rw [show sint.nat (W64 n4) = n4 by word]
  try wp_auto
  ihave HL4 : (∃ (j : Nat) (dps : List (GoSlice × List sp.CmdId)),
      "i" ∷ i_ptr ↦ W64 j ∗
      "Ht" ∷ t ↦ swift.MNewLeaderAckN.mk r0 b0 c0 sl1 sl2 sl3 sl4 ∗
      "Hdp" ∷ sl4 ↦* (dps.map depOf ++ List.replicate (n4 - j) (zero_val swift.SDep)) ∗
      "Hdv" ∷ ([∗list] p ∈ dps, p.1 ↦* p.2.map ofCmdId) ∗
      "Hown" ∷ bufio.ownReader br rd I (R ++ (aH r0 b0 c0 ++ sp.varintLen ids.length ++ fI ids ++
        sp.varintLen phs.length ++ fP phs ++ sp.varintLen cps.length ++ fC (cps.map Prod.snd) ++
        sp.varintLen n4 ++ fD (dps.map Prod.snd))) ∗
      "%Hj" ∷ ⌜j ≤ n4 ∧ dps.length = j ∧ ∀ p ∈ dps, sp.depWf p.2⌝ : IProp netDistGF) $$
      [i Ht Hdp Hown]
  · iexists 0, []
    simp only [List.map_nil, List.nil_append, Nat.sub_zero, fD, List.flatten_nil, List.append_nil]
    iframe
    isplitl
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; simp
  wp_for HL4
  wp_if_destruct
  · obtain ⟨hjn', rfl, hokd⟩ := Hj
    have hjn : dps.length < n4 := by
      have h1 : sint.Z (W64 (dps.length : Int)) = dps.length := by word
      have h2 : sint.Z (W64 (n4 : Int)) = n4 := by word
      omega
    have hlook : (dps.map depOf ++ List.replicate (n4 - dps.length) (zero_val swift.SDep))[
        ((dps.length : Nat) : Int).toNat]? = some (zero_val swift.SDep) := by
      rw [Int.toNat_natCast, List.getElem?_append_right (by simp)]
      simp only [List.length_map, Nat.sub_self]
      rw [List.getElem?_replicate]; simp; omega
    have hbnd : 0 ≤ sint.Z (W64 (dps.length : Int)) ∧
        sint.Z (W64 (dps.length : Int)) < sint.Z sl4.len := by
      obtain ⟨h1, h2⟩ := Hdplen
      have hn' : sint.nat (W64 (n4 : Int)) = n4 := by word
      simp only [List.length_replicate, hn'] at h1
      have h3 : sint.nat sl4.len = (sint.Z sl4.len).toNat := rfl
      have : sint.Z (W64 (dps.length : Int)) = dps.length := by word
      rw [this]; omega
    have hk64 : sint.Z (W64 (dps.length : Int)) = dps.length := by word
    rw [ite_cond_eq_true _ _ (eq_true hbnd)]
    rw [hk64]
    icases ownSlice_elem_acc ((dps.length : Nat) : Int) (zero_val swift.SDep) sl4 _ _
      (by omega) hlook $$ Hdp with ⟨He, Hdp⟩
    have hwd : ∀ x ∈ dps.map Prod.snd, sp.depWf x := by
      intro x hx; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx; exact hokd p hp
    have hel : ∀ d, sp.nextOk (W8 17)
        ((aH r0 b0 c0 ++ sp.varintLen ids.length ++ fI ids ++
          sp.varintLen phs.length ++ fP phs ++ sp.varintLen cps.length ++ fC (cps.map Prod.snd) ++
          sp.varintLen n4 ++ fD (dps.map Prod.snd)) ++ d) → depNext d :=
      fun d hd => ackN_dep (aH_length _ _ _) rfl rfl (by simp) hokc hwd (by simp; omega) hd
    ihave #Hlaw1 := streamLaw_shift br rd I R
      (aH r0 b0 c0 ++ sp.varintLen ids.length ++ fI ids ++
          sp.varintLen phs.length ++ fP phs ++ sp.varintLen cps.length ++ fC (cps.map Prod.snd) ++
          sp.varintLen n4 ++ fD (dps.map Prod.snd)) _ $$ Hlaw
    ihave #Hlaw' := streamLaw_mono br rd I _ _ depNext hel $$ Hlaw1
    wp_apply wp_SDep _ _ br rd I _ $$ [$Hctx $Hrd $Hlaw' $He Hown]
      as %err ⟨%data, Hown, Hres⟩
    · iExactEq Hown; simp [List.append_assoc]
    icases Hres with (⟨%Hen, %ds, %dsl, ⟨%Hd, %Hwf⟩, He, Hdsl⟩ | ⟨%Hen, %v', He⟩)
    · subst Hen Hd
      ihave Hdp := Hdp $$ He
      wp_auto
      wp_for_post
      iframe
      iexists dps.length + 1, dps ++ [(dsl, ds)]
      isplitl [i]
      · iExactEq i; congr 1; word
      isplitl [Ht]
      · iexact Ht
      isplitl [Hdp]
      · iExactEq Hdp; congr 1
        rw [Int.toNat_natCast, swift.rd.set_slot depOf dps _ _ (n4 - dps.length) (by omega)]
        simp [List.map_append, List.append_assoc, depOf,
          show n4 - (dps.length + 1) = n4 - dps.length - 1 by omega]
      isplitl [Hdv Hdsl]
      · iapply (BigSepL.bigSepL_snoc).2
        iframe
      isplitl [Hown]
      · iExactEq Hown; congr 1
        simp [fD, List.map_append, List.flatten_append, List.append_assoc]
      ipureintro
      refine ⟨by omega, by simp, ?_⟩
      intro p hp
      rcases List.mem_append.1 hp with h' | h'
      · exact hokd p h'
      · simp at h'; subst h'; exact Hwf
    · rcases err with eo | _
      · wp_auto
        wp_for_post
        iapply HΦ
        iexists _
        isplitl [Hown]
        · iExactEq Hown; simp only [List.append_assoc]; rfl
        iright
        isplitr
        · ipureintro; exact Hen
        iexists _
        iexact Ht
      · exact absurd rfl Hen
  -- the end: the message
  obtain ⟨hjn', hjl, hokd⟩ := Hj
  have hjn : j = n4 := by
    have h1 : sint.Z (W64 (j : Int)) = j := by word
    have h2 : sint.Z (W64 (n4 : Int)) = n4 := by word
    omega
  subst hjn hjl
  simp only [Nat.sub_self, List.replicate_zero, List.append_nil] at *
  have hwd : ∀ x ∈ dps.map Prod.snd, sp.depWf x := by
    intro x hx; obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx; exact hokd p hp
  icases streamLaw_use br rd I R (aH r0 b0 c0 ++ sp.varintLen ids.length ++ fI ids ++
    sp.varintLen phs.length ++ fP phs ++ sp.varintLen cps.length ++ fC (cps.map Prod.snd) ++
    sp.varintLen dps.length ++ fD (dps.map Prod.snd)) _ $$ [$Hlaw $Hown] with ⟨Hown, %Hfin⟩
  obtain ⟨es, hes, hesw, hn1, hn2, hn3, hn4, hI, hP, hC1, hC2, hD⟩ :=
    ackN_final (aH_length _ _ _) rfl rfl (by simp) hokc (by simp) hwd Hfin
  try wp_auto
  iapply HΦ
  iexists (sp.Msg.newLeaderAckN r0 b0 c0 es).body
  isplitl [Hown]
  · iExactEq Hown; congr 2
    rw [hn1, hn2, hn3, hn4, ackN_body, aI_eq, aP_eq, aD_eq, ← hI, ← hP, ← hC2, ← hD]
    simp only [List.append_assoc]
  ileft
  isplitr
  · ipureintro; rfl
  iexists r0, b0, c0, es, sl1, sl2, sl3, sl4, cps.map cmdOf, dps.map depOf
  isplitr
  · ipureintro; exact ⟨rfl, hes, hesw⟩
  iframe Ht Hcm Hdp
  isplitl [Hsl]
  · iExactEq Hsl; rw [hI]; simp [Function.comp_def]
  isplitl [Hph]
  · iExactEq Hph; rw [hP]
  isplitr
  · ipureintro; simp; omega
  iapply zipOwn es cps dps (by simpa [List.map_map, Function.comp_def] using hC1) hD $$ [$Hcv $Hdv]


/-! ## The entry -/

theorem unmarshalOk_newLeaderAckN (wp_SDep : SDep.Unmarshal.specS (hG := hG))
    (wp_Val : state.Value.Unmarshal.spec (GF := netDistGF)) (l : Loc) (v : swift.MNewLeaderAckN) :
    ctxV ∗ l ↦ v ⊢ sp.unmarshalOk (W8 17) (swift.msgRep (W8 17))
      (interface.mkOk (go.GoType.PointerType swift.MNewLeaderAckN.ty) #l) := by
  iintro ⟨#Hctx, Hl⟩
  unfold sp.unmarshalOk
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %br %rd %I %R %Φ #Hrd #Hlaw Hown HΦ
  wp_apply MNewLeaderAckN.Unmarshal.wp_proof wp_SDep wp_Val l v br rd I R $$
    [$Hctx $Hrd $Hlaw $Hown $Hl] as %err ⟨%data, Hown, Hres⟩
  icases Hres with (⟨%He, %r, %b, %c, %es, %ids, %ph, %cm, %dp, %cmL, %dpL, ⟨%Hd, %Hwf⟩, Ht,
    Hids, Hph, Hcm, Hdp, %Hlen, Hents⟩ | ⟨%He, -⟩)
  · iapply HΦ $$ Hown
    ileft
    isplitr
    · ipureintro; exact He
    iexists .newLeaderAckN r b c es
    isplitr
    · ipureintro; subst Hd; exact sp.decodes_of_body rfl Hwf
    unfold swift.msgRep swift.msgRepM
    iexists l, ids, ph, cm, dp, cmL, dpL
    isplitr
    · ipureintro; rfl
    iframe
    ipureintro; exact Hlen
  · iapply HΦ $$ Hown
    iright
    ipureintro; exact He

omit [io.Assumptions] [errors.Assumptions] [bufio.Assumptions]
  [replica.defs.Assumptions] [state.Assumptions] in
theorem wp_New_MNewLeaderAckN (o : Loc) :
    {{ (True : IProp netDistGF) }}
      (App (Val (o @!! go.GoType.PointerType swift.MNewLeaderAckN.ty @!! go!"New")) (Val #()))
    {{ (l : Loc), RET #(interface.mkOk (go.GoType.PointerType swift.MNewLeaderAckN.ty) #l);
        l ↦ (zero_val swift.MNewLeaderAckN) }} := by
  wp_start
  wp_auto
  wp_alloc_auto
  wp_auto
  iapply HΦ; iframe

theorem newOk_newLeaderAckN (wp_SDep : SDep.Unmarshal.specS (hG := hG))
    (wp_Val : state.Value.Unmarshal.spec (GF := netDistGF)) (o : Loc) :
    ctxV ⊢ sp.newOk (W8 17) (swift.msgRep (W8 17))
      (interface.mkOk (go.GoType.PointerType swift.MNewLeaderAckN.ty) #o) := by
  apply newOk_of _ _ _ o ctxV (fun l => iprop(l ↦ (zero_val swift.MNewLeaderAckN)))
  · iintro %Φ - HΦ
    iapply wp_New_MNewLeaderAckN o $$ [] HΦ
    itrivial
  · intro l; exact unmarshalOk_newLeaderAckN wp_SDep wp_Val l _

end proofs2

end swift.tbl

end Perennial.github_com.imdea_software.swiftpaxos
